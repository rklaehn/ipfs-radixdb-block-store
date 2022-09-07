#![allow(dead_code)]
//!
//! A radix tree that implements a content-addressed store for ipfs
//!
//!
use fnv::FnvHashSet;
use libipld::{
    cbor::{DagCborCodec},
    codec::{Codec, References},
    multihash::Code,
    store::{StoreParams, Store},
    Cid, DefaultParams, Ipld,
};
use log::info;
use parking_lot::Mutex;
use radixdb::{
    node::DowncastConverter,
    store::{BlobStore, DynBlobStore, OwnedBlob, PagedFileStore},
    RadixTree,
};
use std::{
    collections::BTreeMap,
    fmt,
    marker::PhantomData,
    sync::Arc,
    time::{Instant, Duration}, borrow::Cow,
};
use tempfile::tempfile;

#[cfg(test)]
mod tests;

/// alias -> id
const ALIAS: &[u8] = "alias".as_bytes();
/// the actual block data
const BLOCK: &[u8] = "block".as_bytes();

fn format_prefix(prefix: &[u8]) -> anyhow::Result<String> {
    Ok(if prefix.starts_with(ALIAS) {
        format!("\"alias\"   {}", hex::encode(&prefix[BLOCK.len()..]))
    } else if prefix.starts_with(BLOCK) {
        format!("\"block\"   {}", hex::encode(&prefix[BLOCK.len()..]))
    } else {
        hex::encode(prefix)
    })
}

fn format_value(_prefix: &[u8], value: &[u8]) -> anyhow::Result<String> {
    Ok(hex::encode(value))
}

fn alias_key(alias: &[u8]) -> Vec<u8> {
    let mut res = Vec::with_capacity(ALIAS.len() + alias.len());
    res.extend_from_slice(ALIAS);
    res.extend_from_slice(alias);
    res
}

fn block_key(id: &Cid) -> Vec<u8> {
    let mut res = Vec::with_capacity(BLOCK.len() + 64);
    res.extend_from_slice(BLOCK);
    id.write_bytes(&mut res).unwrap();
    res
}

/// a handle that contains a temporary pin
///
/// Dropping this handle enqueues the pin for dropping before the next gc.
// do not implement Clone for this!
pub struct TempPin {
    id: u64,
    temp_pins: Arc<Mutex<BTreeMap<u64, FnvHashSet<Cid>>>>,
}

impl TempPin {
    fn new(id: u64, temp_pins: Arc<Mutex<BTreeMap<u64, FnvHashSet<Cid>>>>) -> Self {
        Self { id, temp_pins }
    }

    fn extend(&mut self, cids: impl IntoIterator<Item = Cid>) {
        let mut temp_pins = self.temp_pins.lock();
        let current = temp_pins.entry(self.id).or_default();
        current.extend(cids);
    }
}

/// dump the temp alias id so you can find it in the database
impl fmt::Debug for TempPin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut builder = f.debug_struct("TempAlias");
        if self.id > 0 {
            builder.field("id", &self.id);
        } else {
            builder.field("unused", &true);
        }
        builder.finish()
    }
}

impl Drop for TempPin {
    fn drop(&mut self) {
        if self.id > 0 {
            self.temp_pins.lock().remove(&self.id);
        }
    }
}

trait RadixTreeExt<S: BlobStore> {
    fn insert(&mut self, key: &[u8], value: &[u8]) -> Result<(), S::Error>;

    fn remove(&mut self, key: &[u8]) -> Result<(), S::Error>;
}

impl<S: BlobStore + Clone> RadixTreeExt<S> for RadixTree<S> {
    fn insert(&mut self, key: &[u8], value: &[u8]) -> Result<(), S::Error> {
        self.try_outer_combine_with(&RadixTree::single(key, value), DowncastConverter, |a, b| {
            Ok(a.set(Some(b.downcast())))
        })
    }

    fn remove(&mut self, key: &[u8]) -> Result<(), S::Error> {
        self.try_left_combine_with(&RadixTree::single(key, &[]), DowncastConverter, |a, _| {
            Ok(a.set(None))
        })
    }
}

type Block = libipld::Block<libipld::store::DefaultParams>;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StoreStats {
    count: u64,
    size: u64,
}

impl StoreStats {
    /// Total number of blocks in the store
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Total size of blocks in the store
    pub fn size(&self) -> u64 {
        self.size
    }
}

fn get_links<E: Extend<Cid>>(cid: &Cid, data: &[u8], cids: &mut E) -> anyhow::Result<()> {
    let codec = <DefaultParams as StoreParams>::Codecs::try_from(cid.codec())?;
    codec.references::<Ipld, E>(data, cids)?;
    Ok(())
}

pub struct Transaction<'a, S>(&'a mut BlockStore<S>);

impl<'a, S> Transaction<'a, S>
where
    S: StoreParams,
    Ipld: References<S::Codecs>,
{
    pub(crate) fn new(owner: &'a mut BlockStore<S>) -> Self {
        Self(owner)
    }

    /// Set or delete an alias
    pub fn alias<'b>(
        &mut self,
        name: impl Into<Cow<'b, [u8]>>,
        link: Option<&'b Cid>,
    ) -> anyhow::Result<()> {
        self.0.alias(name.into().as_ref(), link)
    }

    /// Returns the aliases referencing a cid.
    pub fn reverse_alias(&mut self, cid: &Cid) -> anyhow::Result<Option<FnvHashSet<Vec<u8>>>> {
        self.0.reverse_alias(cid)
    }

    /// Resolves an alias to a cid.
    pub fn resolve<'b>(&mut self, name: impl Into<Cow<'b, [u8]>>) -> anyhow::Result<Option<Cid>> {
        self.0.resolve(name.into().as_ref())
    }

    /// Get a temporary pin for safely adding blocks to the store
    pub fn temp_pin(&mut self) -> TempPin {
        self.0.temp_pin()
    }

    /// Extend temp pin with an additional cid
    pub fn extend_temp_pin(&mut self, pin: &mut TempPin, link: &Cid) -> anyhow::Result<()> {
        todo!()
    }

    /// Checks if the store knows about the cid.
    ///
    /// Note that this does not necessarily mean that the store has the data for the cid.
    pub fn has_cid(&mut self, cid: &Cid) -> anyhow::Result<bool> {
        self.0.has_block(cid)
    }

    /// Checks if the store has the data for a cid
    pub fn has_block(&mut self, cid: &Cid) -> anyhow::Result<bool> {
        self.0.has_block(cid)
    }

    /// Get all cids that the store knows about
    pub fn get_known_cids<C: FromIterator<Cid>>(&mut self) -> anyhow::Result<C> {
        self.0.cids().map(|x| x.into_iter().collect())
    }

    /// Get all cids for which the store has blocks
    pub fn get_block_cids<C: FromIterator<Cid>>(&mut self) -> anyhow::Result<C> {
        self.0.cids().map(|x| x.into_iter().collect())
    }

    /// Get descendants of a cid
    pub fn get_descendants<C: FromIterator<Cid>>(&mut self, cid: &Cid) -> anyhow::Result<C> {
        let mut roots = FnvHashSet::default();
        roots.insert(*cid);
        self.0.get_descendants(roots).map(|x| x.into_iter().collect())
    }

    /// Given a root of a dag, gives all cids which we do not have data for.
    pub fn get_missing_blocks<C: FromIterator<Cid>>(&mut self, cid: &Cid) -> anyhow::Result<C> {
        let mut roots = FnvHashSet::default();
        roots.insert(*cid);
        self.0.get_missing_blocks(roots)
    }

    /// list all aliases
    pub fn aliases<C: FromIterator<(Vec<u8>, Cid)>>(&mut self) -> anyhow::Result<C> {
        self.0.aliases()
    }

    /// Put a block. This will only be completed once the transaction is successfully committed
    pub fn put_block(&mut self, block: libipld::Block<S>, pin: Option<&mut TempPin>) -> anyhow::Result<()> {
        self.0.put_block(&block, pin)
    }

    /// Get a block
    pub fn get_block(&mut self, cid: &Cid) -> anyhow::Result<Option<Vec<u8>>> {
        self.0.get_block(cid).map(|x| x.map(|x| x.to_vec()))        
    }

    /// Get the stats for the store.
    ///
    /// The stats are kept up to date, so this is fast.
    pub fn get_store_stats(&mut self) -> anyhow::Result<StoreStats> {
        Ok(StoreStats::default())
    }

    /// Commit and consume the transaction. Default is to not commit.
    pub fn commit(mut self) -> anyhow::Result<()> {
        Ok(())
    }
}

#[derive(Debug)]
pub struct BlockStore<S> {
    root: RadixTree<DynBlobStore>,
    temp_pins: Arc<Mutex<BTreeMap<u64, FnvHashSet<Cid>>>>,
    p: PhantomData<S>,
}

impl<S> BlockStore<S>
    where
        S: StoreParams,
        Ipld: References<S::Codecs>,
 {

    pub fn incremental_gc(&mut self, _min_blocks: usize, _target_duration: Duration) -> anyhow::Result<bool> {
        self.gc()?;
        Ok(false)
    }

    pub fn flush(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    pub fn get_store_stats(&self) -> anyhow::Result<StoreStats> {
        Ok(StoreStats::default())
    }

    pub fn transaction(&mut self) -> Transaction<'_, S> {
        Transaction::new(self)
    }
}

impl<S: StoreParams> BlockStore<S> {

    pub fn temp_pin(&mut self) -> TempPin {
        let mut temp_pins = self.temp_pins.lock();
        let id = temp_pins
            .iter()
            .next_back()
            .map(|(id, _)| *id + 1)
            .unwrap_or_default();
        temp_pins.insert(id, Default::default());
        TempPin::new(id, self.temp_pins.clone())
    }

    /// compute the set of all live ids
    pub fn live_set(&self) -> anyhow::Result<FnvHashSet<Cid>> {
        self.get_descendants(self.gc_roots()?)
    }

    /// Given a set of roots for a dag, gives all known descendants.
    pub fn get_descendants(&self, roots: FnvHashSet<Cid>) -> anyhow::Result<FnvHashSet<Cid>> {
        let mut curr = roots;
        // new ids (already in all)
        let mut new = curr.clone();
        // a temporary set
        let mut tmp = FnvHashSet::default();
        let mut children = FnvHashSet::default();
        while !new.is_empty() {
            std::mem::swap(&mut new, &mut tmp);
            new.clear();
            children.clear();
            for parent in &tmp {
                self.links(parent, &mut children)?;
            }
            for child in &children {
                // add to the new set only if it is a new cid (all.insert returns true)
                if curr.insert(*child) {
                    new.insert(*child);
                }
            }
        }
        Ok(curr)
    }

    /// Given a set of roots for a dag, gives all cids which we do not have data for.
    pub fn get_missing_blocks<C: FromIterator<Cid>>(&self, roots: FnvHashSet<Cid>) -> anyhow::Result<C> {
        let mut curr = roots;
        let mut next = FnvHashSet::default();
        let mut res = FnvHashSet::default();
        while !curr.is_empty() {
            for cid in &curr {
                if self.has_block(cid)? {
                    self.links(cid, &mut next)?;
                } else {
                    res.insert(*cid);
                }
            }
            curr.clear();
            std::mem::swap(&mut curr, &mut next);
        }
        Ok(res.into_iter().collect())
    }

    pub fn gc(&mut self) -> anyhow::Result<()> {
        let t0 = Instant::now();
        info!("figuring out live set");
        let live_set = self.live_set()?;
        let mut dead = self.cids()?;
        let total = dead.len();
        dead.retain(|id| !live_set.contains(id));
        info!(
            "{} total, {} alive, {} s",
            total,
            live_set.len(),
            t0.elapsed().as_secs_f64()
        );
        let t0 = Instant::now();
        info!("taking out the dead");
        for id in dead {
            self.root.remove(&block_key(&id))?;
        }
        info!("{}", t0.elapsed().as_secs_f64());
        Ok(())
    }

    fn store(&self) -> &DynBlobStore {
        RadixTree::store(&self.root)
    }

    pub fn commit(&mut self) -> anyhow::Result<()> {
        self.root.try_reattach()?;
        self.store().sync()
    }

    pub fn resolve(&self, alias: &[u8]) -> anyhow::Result<Option<Cid>> {
        let key = alias_key(alias);
        Ok(if let Some(v) = self.root.try_get(&key)? {
            let v = v.load(&self.store())?;
            let cid = Cid::read_bytes(v.as_ref())?;
            Some(cid)
        } else {
            None
        })
    }

    /// list all aliases
    pub fn aliases<C: FromIterator<(Vec<u8>, Cid)>>(&self) -> anyhow::Result<C> {
        let res: anyhow::Result<Vec<_>> = self
            .root
            .try_scan_prefix(ALIAS)?
            .map(|r| {
                r.and_then(|(k, v)| {
                    let k = k.to_vec();
                    let v = v.load(&self.store())?;
                    let v = Cid::read_bytes(v.as_ref())?;
                    Ok((k, v))
                })
            })
            .collect();
        Ok(res?.into_iter().collect())
    }

    fn gc_roots(&self) -> anyhow::Result<FnvHashSet<Cid>> {
        // all permanent roots, from the db
        let mut roots = self.root
            .try_scan_prefix(ALIAS)?
            .map(|r| {
                r.and_then(|(_, v)| {
                    v.load(&self.store())
                        .and_then(|b| Ok(Cid::read_bytes(b.as_ref())?))
                })
            })
            .collect::<anyhow::Result<FnvHashSet<Cid>>>()?;
        // add temp pins from memory
        for (_, v) in self.temp_pins.lock().iter() {
            roots.extend(v.iter().cloned());
        }
        Ok(roots)
    }

    /// all cids we have blocks for
    fn cids(&self) -> anyhow::Result<Vec<Cid>> {
        self.root
            .try_scan_prefix(BLOCK)?
            .map(|r| r.and_then(|(k, _)| Ok(Cid::read_bytes(&k.as_ref()[5..])?)))
            .collect()
    }

    pub fn new(store: DynBlobStore) -> anyhow::Result<Self> {
        Ok(Self {
            root: RadixTree::empty(store),
            temp_pins: Default::default(),
            p: PhantomData,
        })
    }

    pub fn get_block(&self, id: &Cid) -> anyhow::Result<Option<OwnedBlob>> {
        let block_key = block_key(id);
        let t = self.root.try_get(&block_key)?;
        let t = t.map(|x| x.load(&self.store())).transpose()?;
        Ok(t)
    }

    pub fn has_block(&self, id: &Cid) -> anyhow::Result<bool> {
        let block_key = block_key(id);
        self.root.try_contains_key(&block_key)
    }

    pub fn alias(&mut self, name: &[u8], cid: Option<&Cid>) -> anyhow::Result<()> {
        if let Some(cid) = cid {
            self.root.insert(&alias_key(name), &cid.to_bytes())?;
        } else {
            self.root.remove(&alias_key(name))?;
        }
        Ok(())
    }

    pub fn reverse_alias(&mut self, cid: &Cid) -> anyhow::Result<Option<FnvHashSet<Vec<u8>>>> {
        let aliases: Vec<_> = self.aliases()?;
        let mut res = FnvHashSet::default();
        for (name, root) in aliases {
            if cid == &root {
                res.insert(name);
            }
        }
        Ok(if res.is_empty() {
            None
        } else {
            Some(res)
        })
    }

    fn links<E: Extend<Cid>>(&self, id: &Cid, res: &mut E) -> anyhow::Result<()> {
        let key = block_key(id);
        if let Some(blob) = self.root.try_get(&key)? {
            let blob = blob.load(&self.store())?;
            get_links(id, &blob, res)?;
        };
        Ok(())
    }

    fn dump(&self) -> anyhow::Result<()> {
        todo!()
        // self.root
        //     .dump_tree_custom("", &self.store, format_prefix, format_value, |_| {
        //         Ok("".into())
        //     })
    }

    pub fn put_blocks<'a>(
        &mut self,
        blocks: impl IntoIterator<Item = &'a libipld::Block<S>>,
        pin: Option<&mut TempPin>,
    ) -> anyhow::Result<()> {
        let mut cids = Vec::new();
        for block in blocks.into_iter() {
            self.put_block(block, None)?;
            cids.push(*block.cid());
        }
        if let Some(pin) = pin {
            pin.extend(cids);
        }
        Ok(())
    }

    pub fn put_block(&mut self, block: &libipld::Block<S>, pin: Option<&mut TempPin>) -> anyhow::Result<()> {
        let block_key = block_key(&block.cid());
        self.root.insert(&block_key, block.data())?;
        if let Some(pin) = pin {
            pin.extend(Some(*block.cid()));
        }
        Ok(())
    }
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let file = tempfile()?;
    let store = PagedFileStore::<4194304>::new(file)?;
    let mut ipfs = BlockStore::<DefaultParams>::new(Arc::new(store.clone()))?;
    let mut hashes = Vec::new();
    let blocks = (0..100_000u64)
        .map(|i| {
            let mut data = vec![0u8; 10000];
            data[0..8].copy_from_slice(&i.to_be_bytes());
            Block::encode(DagCborCodec, Code::Sha2_256, &Ipld::Bytes(data)).unwrap()
        })
        .collect::<Vec<_>>();
    let t0 = Instant::now();
    for (i, block) in blocks.into_iter().enumerate() {
        println!("putting block {}", i);
        ipfs.put_block(&block, None)?;
        hashes.push(*block.cid());
    }
    println!("finished {}", t0.elapsed().as_secs_f64());
    let t0 = Instant::now();
    println!("committing {:?}", store);
    ipfs.commit()?;
    println!("done {:?} {}", store, t0.elapsed().as_secs_f64());
    // ipfs.dump()?;
    // let data = ipfs.get(b"abcd")?;
    // ipfs.alias(b"root1", Some(b"abcd"))?;
    // ipfs.dump()?;
    println!("{:?}", ipfs.live_set()?);
    ipfs.alias(b"root1", None)?;
    println!("traversing all (in order)");
    let t0 = Instant::now();
    let mut res = 0u64;
    for hash in &hashes {
        res += ipfs.get_block(hash)?.unwrap().len() as u64;
    }
    println!("done {} {}", res, t0.elapsed().as_secs_f64());
    println!("traversing all (in order, hot)");
    let t0 = Instant::now();
    let mut res = 0u64;
    for hash in &hashes {
        res += ipfs.get_block(hash)?.unwrap().len() as u64;
    }
    println!("done {} {}", res, t0.elapsed().as_secs_f64());
    hashes.sort();
    for _ in 0..10 {
        println!("traversing all (random)");
        let t0 = Instant::now();
        let mut res = 0u64;
        for hash in &hashes {
            res += ipfs.get_block(hash)?.unwrap().len() as u64;
        }
        println!("done {} {}", res, t0.elapsed().as_secs_f64());
    }
    // ipfs.dump()?;
    println!("performing gc");
    ipfs.gc()?;
    println!("committing {:?}", store);
    ipfs.commit()?;
    println!("done {:?}", store);
    // ipfs.dump()?;
    Ok(())
}
