use std::io::Write;
use crate::alloc::{GlobalAlloc, global_alloc, Allocator};
use crate::{PathMap, morphisms::Catamorphism, utils::{BitMask, ByteMask, find_prefix_overlap}, zipper::{
    Zipper, ZipperValues, ZipperForking, ZipperAbsolutePath, ZipperIteration,
    ZipperMoving, ZipperPathBuffer, ZipperReadOnlyValues, ZipperSubtries,
    ZipperConcrete, ZipperReadOnlyConditionalValues, TrieRef
}, TrieValue};
use crate::write_zipper::ZipperWriting;

fn stream16_bare<RZ : Zipper + ZipperIteration>(rz: &mut RZ, ms: &mut Vec<u16>) {
    let cm = rz.child_mask();
    let nm = cm.nibble_mask();
    let nz = nm.count_ones() as usize;
    ms.push(nm);
    if nm == 0 { return; }
    ms.reserve(nz);
    cm.store_nz_lo_masks(nm, unsafe { ms.as_mut_ptr().add(ms.len()) });
    unsafe { ms.set_len(ms.len() + nz); }

    for b in cm.iter() {
        rz.descend_to_byte(b);
        stream16_bare(rz, ms);
        rz.ascend_byte();
    }
}

fn trie16_bare<'a, A : Allocator, V : TrieValue, WZ : Zipper + ZipperWriting<V, A>>(mut ms: &'a [u16], wz: &mut WZ, value: V) -> &'a [u16] {
    let nm = ms[0];
    ms = &ms[1..];
    if nm == 0 {
        wz.set_val(value.clone());
        return ms;
    }
    let cm = ByteMask::load_nz_lo_masks(nm, ms.as_ptr());
    ms = &ms[nm.count_ones() as _..];

    for b in cm.iter() {
        wz.descend_to_byte(b);
        ms = trie16_bare(ms, wz, value.clone());
        wz.ascend_byte();
    }
    ms
}

fn stream16_values<V : TrieValue, RZ : Zipper + ZipperIteration + ZipperValues<V>>(rz: &mut RZ, ms: &mut Vec<u16>, vs: &mut Vec<V>) {
    let cm = rz.child_mask();
    let nm = cm.nibble_mask();
    let nz = nm.count_ones() as usize;
    ms.push(nm);
    if nm == 0 {
        vs.push(rz.val().unwrap().clone());
        return;
    }
    ms.reserve(nz);
    cm.store_nz_lo_masks(nm, unsafe { ms.as_mut_ptr().add(ms.len()) });
    unsafe { ms.set_len(ms.len() + nz); }

    for b in cm.iter() {
        rz.descend_to_byte(b);
        stream16_values(rz, ms, vs);
        rz.ascend_byte();
    }
}

fn trie16_values<'a, 'b, A : Allocator, V : TrieValue + std::fmt::Debug, WZ : Zipper + ZipperWriting<V, A>>(mut ms: &'a [u16], mut vs: &'b [V], wz: &mut WZ) -> (&'a [u16], &'b [V]) {
    let nm = ms[0];
    ms = &ms[1..];
    if nm == 0 {
        wz.set_val(vs[0].clone());
        return (ms, &vs[1..]);
    }
    let cm = ByteMask::load_nz_lo_masks(nm, ms.as_ptr());
    ms = &ms[nm.count_ones() as _..];

    for b in cm.iter() {
        wz.descend_to_byte(b);
        (ms, vs) = trie16_values(ms, vs, wz);
        wz.ascend_byte();
    }
    (ms, vs)
}

fn stream16_locations<V : TrieValue, RZ : Zipper + ZipperIteration + ZipperValues<V>>(rz: &mut RZ, ms: &mut Vec<u16>, ls: &mut Vec<usize>) {
    let cm = rz.child_mask();
    let nm = cm.nibble_mask();
    let nz = nm.count_ones() as usize;
    if rz.is_val() {
        ls.push(ms.len());
    }
    ms.push(nm);
    if nm == 0 {
        return;
    }
    ms.reserve(nz);
    cm.store_nz_lo_masks(nm, unsafe { ms.as_mut_ptr().add(ms.len()) });
    unsafe { ms.set_len(ms.len() + nz); }

    for b in cm.iter() {
        rz.descend_to_byte(b);
        stream16_locations(rz, ms, ls);
        rz.ascend_byte();
    }
}

fn trie16_locations<'a, 'b, A : Allocator, WZ : Zipper + ZipperWriting<(), A>>(ms: &'a [u16], mut ls: &'b [usize], wz: &mut WZ, mut loc: usize) -> (usize, &'b [usize]) {
    let nm = ms[loc];
    if loc == ls[0] {
        wz.set_val(());
        ls = &ls[1..];
    }
    loc += 1;
    if nm == 0 {
        return (loc, ls);
    }
    let cm = ByteMask::load_nz_lo_masks(nm, &ms[loc]);
    loc += nm.count_ones() as usize;

    for b in cm.iter() {
        wz.descend_to_byte(b);
        (loc, ls) = trie16_locations(ms, ls, wz, loc);
        wz.ascend_byte();
    }
    (loc, ls)
}

mod tests {
    use crate::cbm_stream::*;
    use crate::PathMap;

    #[test]
    fn basic16() {
        let mut btm = PathMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.set_val_at(r.as_bytes(), i); });

        let mut v = vec![];
        stream16_bare(&mut btm.read_zipper(), &mut v);
        println!("{} {}", 2*v.len(), rs.iter().map(|x| x.len()).sum::<usize>());
        for nm in v.iter() {
            print!("{nm:b}");
        }
        println!();

        let mut btm_: PathMap<()> = PathMap::new();
        trie16_bare(&v[..], &mut btm_.write_zipper(), ());
        println!("{:?}", btm_);
        for (p, _) in btm.iter() {
            assert!(btm_.path_exists_at(&p[..]));
        }
    }

    #[test]
    fn values16() {
        let mut btm = PathMap::new();
        // internal values paths unsupported "roman"
        let rs = ["arrow", "bow", "cannon", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.set_val_at(r.as_bytes(), i); });

        let mut ms = vec![];
        let mut vs = vec![];
        stream16_values(&mut btm.read_zipper(), &mut ms, &mut vs);
        for nm in ms.iter() {
            print!("{nm:b}");
        }
        println!();
        println!("{:?}", vs);

        let mut btm_: PathMap<usize> = PathMap::new();
        trie16_values(&ms[..], &mut vs, &mut btm_.write_zipper());
        println!("{:?}", btm_);
        for (p, v) in btm.iter() {
            assert!(btm_.path_exists_at(&p[..]));
            println!("{:?}", std::str::from_utf8(&p[..]));
            assert_eq!(v, btm_.get_val_at(&p[..]).unwrap())
        }
    }

    #[test]
    fn locations16() {
        let mut btm = PathMap::new();
        // internal values paths unsupported "roman"
        let rs = ["arrow", "bow", "cannon", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.set_val_at(r.as_bytes(), i); });

        let mut ms = vec![];
        let mut ls = vec![];
        stream16_locations(&mut btm.read_zipper(), &mut ms, &mut ls);
        for nm in ms.iter() {
            print!("{nm:b}");
        }
        println!();
        println!("{:?}", ls);

        let mut btm_: PathMap<()> = PathMap::new();
        trie16_locations(&ms[..], &mut ls, &mut btm_.write_zipper(), 0);
        for (p, v) in btm.iter() {
            assert!(btm_.path_exists_at(&p[..]));
            assert!(btm_.get_val_at(&p[..]).is_some())
        }
    }
}
