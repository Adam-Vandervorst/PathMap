use pathmap::*;
use pathmap::zipper::{ZipperMoving, ZipperWriting};

fn main() {
    const SILLY_LARGE_COUNTS: bool = false;
    let mut pm0 = PathMap::new();
    pm0.insert(&[b'C', b'0', b'0'], ());
    pm0.insert(&[b'C', b'0', b'1'], ());
    pm0.insert(&[b'C', b'0', b'2'], ());
    pm0.insert(&[b'O', b'0', b'0'], ());
    pm0.insert(&[b'O', b'0',  b'1'], ());

    let mut pm1 = PathMap::new();
    if SILLY_LARGE_COUNTS { // at copious amounts of C atoms with the second map
        let mut wz = pm1.write_zipper_at_path(&[b'C', b'1']);
        let m = utils::ints::gen_int_range(0usize, 1 << 63, 2, ());
        wz.graft_map(m);
        drop(wz);
    } else { // add a few C atoms with the second map
        pm1.insert(&[b'C', b'1', b'0'], ());
        pm1.insert(&[b'C', b'1', b'1'], ());
    }

    let pm2 = pm0.join(&pm1);

    let large_val_count = pm2.read_zipper_at_path(&[b'C']).val_count();
    println!("number of C atoms {:?}", large_val_count);
    if SILLY_LARGE_COUNTS {
        assert_eq!(large_val_count, (1 << 63) / 2 + 3); // size(0..(1<<63) by 2) + the three C's in pm0
    }
    println!("number of O atoms {:?}", pm2.read_zipper_at_path(&[b'O']).val_count());

    #[cfg(feature="viz")]
    {
        use pathmap::viz::{viz_maps, DrawConfig, VizMode};
        let mut v = vec![];
        let dc = DrawConfig{ mode: VizMode::Ascii, ascii_path: false, hide_value_paths: false, minimize_values: false, logical: true, color: false };
        viz_maps(&[pm0, pm1, pm2], &dc, &mut v).unwrap();
        println!("{}", str::from_utf8(&v[..]).unwrap());
    }
}
