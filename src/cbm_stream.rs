use std::io::Write;
use crate::alloc::{GlobalAlloc, global_alloc, Allocator};
use crate::{PathMap, morphisms::Catamorphism, utils::{BitMask, ByteMask, find_prefix_overlap}, zipper::{
    Zipper, ZipperValues, ZipperForking, ZipperAbsolutePath, ZipperIteration,
    ZipperMoving, ZipperPathBuffer, ZipperReadOnlyValues, ZipperSubtries,
    ZipperConcrete, ZipperReadOnlyConditionalValues, TrieRef
}, TrieValue};
use crate::write_zipper::ZipperWriting;

fn stream16<RZ : Zipper + ZipperIteration>(rz: &mut RZ, v: &mut Vec<u16>) {
    let cm = rz.child_mask();
    let nm = cm.nibble_mask();
    let nz = nm.count_ones() as usize;
    v.push(nm);
    if nm == 0 { println!("pushing empty nm"); return; }
    v.reserve(nz);
    cm.store_nz_lo_masks(nm, unsafe { v.as_mut_ptr().add(v.len()) });
    unsafe { v.set_len(v.len() + nz); }

    for b in cm.iter() {
        rz.descend_to_byte(b);
        stream16(rz, v);
        rz.ascend_byte();
    }
}

fn trie16<'a, A : Allocator, V : TrieValue, WZ : Zipper + ZipperWriting<V, A>>(mut v: &'a [u16], wz: &mut WZ, value: V) -> &'a [u16] {
    let nm = v[0];
    v = &v[1..];
    if nm == 0 {
        wz.set_val(value.clone());
        return v;
    }
    let cm = ByteMask::load_nz_lo_masks(nm, v.as_ptr());
    v = &v[nm.count_ones() as _..];

    for b in cm.iter() {
        wz.descend_to_byte(b);
        v = trie16(v, wz, value.clone());
        wz.ascend_byte();
    }
    v
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
        stream16(&mut btm.read_zipper(), &mut v);
        println!("{} {}", 2*v.len(), rs.iter().map(|x| x.len()).sum::<usize>());
        for nm in v.iter() {
            print!("{nm:b}");
        }
        println!();

        let mut btm_: PathMap<()> = PathMap::new();
        trie16(&v[..], &mut btm_.write_zipper(), ());
        println!("{:?}", btm_);
        for (p, _) in btm.iter() {
            println!("{:?}", btm_.path_exists_at(&p[..]));
        }
    }
}
