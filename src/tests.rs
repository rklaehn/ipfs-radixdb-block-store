use std::{sync::Arc, time::Instant, collections::HashSet};
use libipld::{
    cbor::DagCborCodec,
    codec::Codec,
    multihash::{Code, MultihashDigest},
    Cid, DagCbor, DefaultParams,
};
use log::{info, trace};
use maplit::hashset;
use radixdb::store::MemStore;

use crate::{Block, BlockStore};

#[derive(Debug, DagCbor)]
struct Node {
    links: Vec<Cid>,
    text: String,
}

impl Node {
    pub fn leaf(text: &str) -> Self {
        Self {
            links: Vec::new(),
            text: text.into(),
        }
    }

    pub fn branch(text: &str, links: impl IntoIterator<Item = Cid>) -> Self {
        Self {
            links: links.into_iter().collect(),
            text: text.into(),
        }
    }
}

/// creates a simple leaf block
fn block(name: &str) -> Block {
    let ipld = Node::leaf(name);
    let bytes = DagCborCodec.encode(&ipld).unwrap();
    let hash = Code::Sha2_256.digest(&bytes);
    // https://github.com/multiformats/multicodec/blob/master/table.csv
    Block::new_unchecked(Cid::new_v1(0x71, hash), bytes)
}

/// creates a block with some links
fn links(name: &str, children: Vec<&Block>) -> Block {
    let ipld = Node::branch(name, children.iter().map(|b| *b.cid()).collect::<Vec<_>>());
    let bytes = DagCborCodec.encode(&ipld).unwrap();
    let hash = Code::Sha2_256.digest(&bytes);
    let cid = Cid::new_v1(0x71, hash);
    trace!("{:?} {}", ipld, cid);
    // https://github.com/multiformats/multicodec/blob/master/table.csv
    Block::new_unchecked(cid, bytes)
}

/// creates a block with a min size
fn sized(name: &str, min_size: usize) -> Block {
    let mut text = name.to_string();
    while text.len() < min_size {
        text += " ";
    }
    let ipld = Node::leaf(&text);
    let bytes = DagCborCodec.encode(&ipld).unwrap();
    let hash = Code::Sha2_256.digest(&bytes);
    // https://github.com/multiformats/multicodec/blob/master/table.csv
    Block::new_unchecked(Cid::new_v1(0x71, hash), bytes)
}

/// create a chain of depth `depth`, with minimum block size `bs`, returning the root block
fn chain(name: &str, depth: usize, bs: usize, insert: &mut impl FnMut(&Block)) -> Option<Block> {
    let mut prev: Option<Block> = None;
    let mut data = name.to_string();
    while data.len() < bs {
        data.push(' ');
    }
    for _ in 0..depth {
        let block = links(&data, prev.iter().collect::<Vec<_>>());
        insert(&block);
        prev = Some(block);
    }
    prev
}

// create a tree of depth `depth` with branch factor `branch`, with leafs being minimum `bs` bytes, returning the root block
fn tree(
    name: &str,
    depth: usize,
    branch: usize,
    bs: usize,
    insert: &mut impl FnMut(&Block),
) -> Block {
    if depth == 0 {
        let block = sized(name, bs);
        insert(&block);
        block
    } else {
        let mut children = Vec::new();
        for i in 0..branch {
            children.push(tree(
                &format!("{}-{}", name, i),
                depth - 1,
                branch,
                bs,
                insert,
            ));
        }
        let block = links(name, children.iter().collect());
        insert(&block);
        block
    }
}

#[test]
fn get_missing_blocks() -> anyhow::Result<()> {
    let store = Arc::new(MemStore::default());
    let mut ipfs = BlockStore::<DefaultParams>::new(store)?;

    let b = block("b");
    let c = block("c");
    let d = block("d");
    let a = links("a", vec![&b, &c, &d]);
    ipfs.put_blocks([&a], None)?;
    let res: HashSet<Cid> = ipfs.get_missing_blocks(vec![*a.cid()].into_iter().collect())?;
    assert_eq!(res, hashset!{ *b.cid(), *c.cid(), *d.cid() });
    ipfs.put_blocks([&b, &c], None)?;
    let res: HashSet<Cid> = ipfs.get_missing_blocks(vec![*a.cid()].into_iter().collect())?;
    assert_eq!(res, hashset!{ *d.cid() });
    ipfs.put_blocks([&d], None)?;
    let res: HashSet<Cid> = ipfs.get_missing_blocks(vec![*a.cid()].into_iter().collect())?;
    assert_eq!(res, hashset!{ });
    Ok(())
}

#[test]
fn gc_smoke() -> anyhow::Result<()> {
    let store = Arc::new(MemStore::default());
    let mut ipfs = BlockStore::<DefaultParams>::new(store)?;
    let b = block("b");
    let c = block("c");
    let a = links("a", vec![&b, &c, &c]);
    let d = block("d");

    ipfs.put_blocks([&a, &b, &c, &d], None)?;

    assert!(ipfs.has_block(a.cid())?);
    assert!(ipfs.has_block(b.cid())?);
    assert!(ipfs.has_block(c.cid())?);
    assert!(ipfs.has_block(d.cid())?);

    ipfs.alias(b"test", Some(a.cid()))?;
    ipfs.gc()?;
    assert!(ipfs.has_block(a.cid())?);
    assert!(ipfs.has_block(b.cid())?);
    assert!(ipfs.has_block(c.cid())?);
    assert!(!ipfs.has_block(d.cid())?);

    ipfs.alias(b"test", None)?;
    ipfs.gc()?;
    assert!(!ipfs.has_block(a.cid())?);
    assert!(!ipfs.has_block(b.cid())?);
    assert!(!ipfs.has_block(c.cid())?);
    assert!(!ipfs.has_block(d.cid())?);

    Ok(())
}

#[test]
fn gc_bench_chain() -> anyhow::Result<()> {
    let _ = env_logger::try_init();
    let store = Arc::new(MemStore::default());
    let mut ipfs = BlockStore::<DefaultParams>::new(store.clone())?;
    let mut roots = Vec::new();
    for i in 0..100 {
        roots.extend(chain(&format!("{}", i), 1000, 1000, &mut |x| {
            ipfs.put_block(x, None).unwrap();
        }));
    }
    info!("{:?}", ipfs);
    info!("{:?}", store.count());
    ipfs.alias(b"root", roots.iter().next().map(|x| x.cid()))?;
    let t0 = Instant::now();
    ipfs.gc()?;
    info!("GC took {}", t0.elapsed().as_secs_f64());
    Ok(())
}

#[test]
fn gc_bench_tree() -> anyhow::Result<()> {
    let _ = env_logger::try_init();
    let store = Arc::new(MemStore::default());
    let mut ipfs = BlockStore::<DefaultParams>::new(store.clone())?;
    let mut roots = Vec::new();
    for i in 0..10 {
        roots.push(tree(&format!("{}", i), 7, 4, 1000, &mut |x| {
            ipfs.put_block(x, None).unwrap();
        }));
    }
    info!("{:?}", ipfs);
    info!("{:?}", store.count());
    ipfs.alias(b"root", roots.iter().next().map(|x| x.cid()))?;
    let t0 = Instant::now();
    ipfs.gc()?;
    info!("GC took {}", t0.elapsed().as_secs_f64());
    Ok(())
}

#[test]
fn sizes() {
    println!("{}", std::mem::size_of::<Cid>());
}
