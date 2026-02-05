use num_traits::PrimInt;
use smallvec::ExtendFromSlice;
use crate::alloc::Allocator;
use crate::write_zipper::ZipperWriting;
use crate::{utils::ByteMask, zipper::{
    Zipper, ZipperIteration, ZipperValues
}, TrieValue};
use crate::ring::{AlgebraicResult, COUNTER_IDENT, SELF_IDENT};
use crate::utils::BitMask;

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

fn deplete_bare(ms: &[u16], c: &mut usize) {
    let nm = ms[*c];
    *c += 1;
    if nm == 0 {
        return;
    }
    let cm = ByteMask::load_nz_lo_masks(nm, &ms[*c]);
    *c += nm.count_ones() as usize;

    for _ in 0..cm.count_bits() {
        deplete_bare(ms, c);
    }
}

fn bare_join(sms: &[u16], oms: &[u16], ms: &mut Vec<u16>, sc: &mut usize, oc: &mut usize) {
    let sm = ByteMask::load_nz_lo_masks(sms[*sc], &sms[*sc+1]);
    *sc += 1 + sms[*sc].count_ones() as usize;
    let om = ByteMask::load_nz_lo_masks(oms[*oc], &oms[*oc+1]);
    *oc += 1 + oms[*oc].count_ones() as usize;

    let jm: ByteMask = sm | om;
    let mm: ByteMask = sm & om;

    let jnm = jm.nibble_mask();
    let nz = jnm.count_ones() as usize;
    ms.push(jnm);
    ms.reserve(nz as _);
    jm.store_nz_lo_masks(jnm, unsafe { ms.as_mut_ptr().add(ms.len()) });
    unsafe { ms.set_len(ms.len() + nz); }

    for b in jm.iter() {
        if mm.test_bit(b) {
            bare_join(sms, oms, ms, sc, oc);
        } else if om.test_bit(b) {
            let old_oc = *oc;
            deplete_bare(oms, oc);
            ms.extend_from_slice(&oms[old_oc..*oc]);
        } else if sm.test_bit(b) {
            let old_sc = *sc;
            deplete_bare(sms, sc);
            ms.extend_from_slice(&sms[old_sc..*sc]);
        }
    }
}

// returns whether to keep this branch
fn bare_meet(sms: &[u16], oms: &[u16], ms: &mut Vec<u16>, sc: &mut usize, oc: &mut usize) -> bool {
    let sm = ByteMask::load_nz_lo_masks(sms[*sc], &sms[*sc+1]);
    *sc += 1 + sms[*sc].count_ones() as usize;
    let om = ByteMask::load_nz_lo_masks(oms[*oc], &oms[*oc+1]);
    *oc += 1 + oms[*oc].count_ones() as usize;

    let jm: ByteMask = sm | om;
    let mm: ByteMask = sm & om;
    let mut amm: ByteMask = sm & om;

    let mnm = mm.nibble_mask();
    let nz = mnm.count_ones() as usize;
    ms.push(mnm);
    let amm_pos = ms.len();
    ms.extend_from_slice(&[0u16; 16][..nz]);

    for (c, b) in jm.iter().enumerate() {
        if mm.test_bit(b) {
            let old_ms = ms.len();
            if !bare_meet(sms, oms, ms, sc, oc) {
                ms.truncate(old_ms);
                amm.clear_bit(b);
            }
        } else if om.test_bit(b) {
            deplete_bare(oms, oc);
        } else if sm.test_bit(b) {
            deplete_bare(sms, sc);
        }
    }

    if amm.count_bits() != 0 {
        amm.store_nz_lo_masks(mnm, unsafe { ms.as_mut_ptr().add(amm_pos) });
        true
    } else {
        (sm | om).count_bits() == 0
    }
}

mod tests {
    use crate::cbm_stream::*;
    use crate::morphisms::Catamorphism;
    use crate::PathMap;

    #[test]
    fn basic16() {
        let mut btm = PathMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.set_val_at(r.as_bytes(), i); });

        let mut v = vec![];
        stream16_bare(&mut btm.read_zipper(), &mut v);
        println!("{} {}", 2*v.len(), rs.iter().map(|x| x.len()).sum::<usize>());
        for nm in v.iter() { print!("{nm:b}"); }
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
        for nm in ms.iter() { print!("{nm:b}"); }
        println!();
        println!("{:?}", vs);

        let mut btm_: PathMap<usize> = PathMap::new();
        trie16_values(&ms[..], &mut vs, &mut btm_.write_zipper());
        println!("{:?}", btm_);
        for (p, v) in btm.iter() {
            assert!(btm_.path_exists_at(&p[..]));
            assert_eq!(v, btm_.get_val_at(&p[..]).unwrap())
        }
    }

    #[test]
    fn locations16() {
        let mut btm = PathMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
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
        for (p, _) in btm.iter() {
            assert!(btm_.path_exists_at(&p[..]));
            assert!(btm_.get_val_at(&p[..]).is_some())
        }
    }

    #[test]
    fn basic_bare_join() {
        let mut a = PathMap::new();
        let mut b = PathMap::new();
        let rs = ["Abbotsford", "Abbottabad", "Abcoude", "Abdul Hakim", "Abdulino", "Abdullahnagar", "Abdurahmoni Jomi", "Abejorral", "Abelardo Luz"];
        for (i, path) in rs.into_iter().enumerate() {
            if i % 3 == 0 {
                a.set_val_at(path, ());
                b.set_val_at(path, ());
            } else if i % 3 == 1 {
                a.set_val_at(path, ());
            } else {
                b.set_val_at(path, ());
            }
        }

        println!("a {:?}", a);
        println!("b {:?}", b);
        let joined = a.join(&b);

        let mut ams = vec![];
        stream16_bare(&mut a.read_zipper(), &mut ams);
        let mut bms = vec![];
        stream16_bare(&mut b.read_zipper(), &mut bms);

        let mut cms = vec![];
        let mut ac = 0;
        let mut bc = 0;
        bare_join(&ams[..], &bms[..], &mut cms, &mut ac, &mut bc);

        let mut joined_ = PathMap::new();
        trie16_bare(&cms[..], &mut joined_.write_zipper(), ());

        println!("{:?}", joined);
        println!("{:?}", joined_);
        assert_eq!(joined.hash(), joined_.hash());
    }

    #[test]
    fn basic_bare_meet() {
        let mut a = PathMap::new();
        let mut b = PathMap::new();
        let rs = ["Abbotsford", "Abbottabad", "Abcoude", "Abdul Hakim", "Abdulino", "Abdullahnagar", "Abdurahmoni Jomi", "Abejorral", "Abelardo Luz"];
        for (i, path) in rs.into_iter().enumerate() {
            if i % 3 == 0 {
                a.set_val_at(path, ());
                b.set_val_at(path, ());
            } else if i % 3 == 1 {
                a.set_val_at(path, ());
            } else {
                b.set_val_at(path, ());
            }
        }

        let met = a.meet(&b);

        let mut ams = vec![];
        stream16_bare(&mut a.read_zipper(), &mut ams);
        println!("a: {:?}", ams);
        for nm in ams.iter() { print!("{nm:016b} "); } println!();
        let mut bms = vec![];
        stream16_bare(&mut b.read_zipper(), &mut bms);
        println!("b: {:?}", bms);
        for nm in bms.iter() { print!("{nm:016b} "); } println!();

        let mut cms = vec![];
        let mut ac = 0;
        let mut bc = 0;
        bare_meet(&ams[..], &bms[..], &mut cms, &mut ac, &mut bc);
        for nm in cms.iter() { print!("{nm:016b} "); } println!();

        let mut met_ = PathMap::new();
        trie16_bare(&cms[..], &mut met_.write_zipper(), ());

        println!("{:?}", met);
        println!("{:?}", met_);
        assert_eq!(met.hash(), met_.hash());
    }
}
