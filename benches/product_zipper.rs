use divan::{Divan, Bencher, black_box};

use std::fs::File;
use std::io::BufReader;

use serde::*;
use csv::ReaderBuilder;
const CUT_CITIES_LIST: usize = 2000;
fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(16);

    divan.main();
}

fn read_data() -> Vec<(String, i32)> {
    // A geonames file may be downloaded from: [http://download.geonames.org/export/dump/cities500.zip]
    // for a large file, or "cities15000.zip" for a smaller file
    //NOTE: Benchmark timing depends on the cities file, so benchmarks with different files are incomparable
    let file_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benches").join("cities5000.txt");
    let file = File::open(file_path).unwrap();

    //Data structure to parse the GeoNames TSV file into
    #[derive(Clone, Debug, Serialize, Deserialize)]
    struct GeoName {
        geonameid         : i32, //integer id of record in geonames database
        name              : String, //name of geographical point (utf8) varchar(200)
        asciiname         : String, //name of geographical point in plain ascii characters, varchar(200)
        alternatenames    : String, //alternatenames, comma separated, ascii names automatically transliterated, convenience attribute from alternatename table, varchar(10000)
        latitude          : f32, //latitude in decimal degrees (wgs84)
        longitude         : f32, //longitude in decimal degrees (wgs84)
        feature_class     : char, //see http://www.geonames.org/export/codes.html, char(1)
        feature_code      : String,//[char; 10], //see http://www.geonames.org/export/codes.html, varchar(10)
        country_code      : String,//[char; 2], //ISO-3166 2-letter country code, 2 characters
        cc2               : String, //alternate country codes, comma separated, ISO-3166 2-letter country code, 200 characters
        admin1_code       : String,//[char; 20], //fipscode (subject to change to iso code), see exceptions below, see file admin1Codes.txt for display names of this code; varchar(20)
        admin2_code       : String, //code for the second administrative division, a county in the US, see file admin2Codes.txt; varchar(80) 
        admin3_code       : String,//[char; 20], //code for third level administrative division, varchar(20)
        admin4_code       : String,//[char; 20], //code for fourth level administrative division, varchar(20)
        population        : i64, //bigint (8 byte int)
        #[serde(deserialize_with = "default_if_empty")]
        elevation         : i32, //in meters, integer
        #[serde(deserialize_with = "default_if_empty")]
        dem               : i32, //digital elevation model, srtm3 or gtopo30, average elevation of 3''x3'' (ca 90mx90m) or 30''x30'' (ca 900mx900m) area in meters, integer. srtm processed by cgiar/ciat.
        timezone          : String, //the iana timezone id (see file timeZone.txt) varchar(40)
        modification_date : String, //date of last modification in yyyy-MM-dd format
    }
    fn default_if_empty<'de, D, T>(de: D) -> Result<T, D::Error>
        where D: serde::Deserializer<'de>, T: serde::Deserialize<'de> + Default,
    {
        Option::<T>::deserialize(de).map(|x| x.unwrap_or_else(|| T::default()))
    }

    //Parser for the tab-saparated value file
    let reader = BufReader::new(file);
    let mut tsv_parser = ReaderBuilder::new()
        .delimiter(b'\t')
        .has_headers(false)
        .flexible(true) //We want to permit situations where some rows have fewer columns for now
        .quote(0)
        .double_quote(false)
        .from_reader(reader);

    let mut _tsv_record_count = 0;
    let mut pairs = vec![];
    for geoname in tsv_parser.deserialize::<GeoName>().map(|result| result.unwrap()) {
        _tsv_record_count += 1;

        pairs.push((geoname.name, geoname.geonameid));

        if geoname.alternatenames.len() > 0 {
            //Separate the comma-separated alternatenames field
            for alt_name in geoname.alternatenames.split(',') {
                pairs.push((alt_name.to_string(), geoname.geonameid));
            }
        }
    }
    // println!("tsv_record_count = {_tsv_record_count}, total_entries = {}", pairs.len());

    pairs
}
use pathmap::utils::ByteMask;
// FnMut(&ByteMask, &mut [W], Option<&V>, &[u8])
fn val_count_cata<V>(_bm: &ByteMask, vals: &mut[usize], _val: Option<&V>, _path: &[u8]) -> usize {
    1 + vals.iter().copied().sum::<usize>()
}
#[divan::bench()]
fn introspecting_pathmap_pathmap(bencher: Bencher) {
    use pathmap::{
        PathMap,
        morphisms::Catamorphism,
        zipper::{ProductZipper},
    };
    let mut sink = 0;
    let pairs = read_data();
    let map1 = PathMap::from_iter(pairs.iter().take(CUT_CITIES_LIST).map(|p| (&p.0, p.1 as u64)));
    let map2 = PathMap::from_iter(pairs.iter().take(CUT_CITIES_LIST).map(|p| (&p.0, p.1 as u64)));
    bencher.bench_local(|| {
        let pz = ProductZipper::new(map1.read_zipper(), [map2.read_zipper()]);
        *black_box(&mut sink) = pz.into_cata_side_effect(val_count_cata);
    });
}

#[divan::bench()]
fn generic_pathmap_pathmap(bencher: Bencher) {
    use pathmap::{
        PathMap,
        morphisms::Catamorphism,
        zipper::{ProductZipperG},
    };
    let mut sink = 0;
    let pairs = read_data();
    let map1 = PathMap::from_iter(pairs.iter().take(CUT_CITIES_LIST).map(|p| (&p.0, p.1 as u64)));
    let map2 = PathMap::from_iter(pairs.iter().take(CUT_CITIES_LIST).map(|p| (&p.0, p.1 as u64)));
    bencher.bench_local(|| {
        let pz = ProductZipperG::new(map1.read_zipper(), [map2.read_zipper()]);
        *black_box(&mut sink) = pz.into_cata_side_effect(val_count_cata);
    });
}

#[cfg(feature="arena_compact")]
#[divan::bench()]
fn generic_act_act(bencher: Bencher) {
    use pathmap::{
        PathMap,
        arena_compact::{ArenaCompactTree},
        morphisms::Catamorphism,
        zipper::{ProductZipperG},
    };
    let mut sink = 0;
    let pairs = read_data();
    let map1 = PathMap::from_iter(pairs.iter().take(CUT_CITIES_LIST).map(|p| (&p.0, p.1 as u64)));
    let map2 = PathMap::from_iter(pairs.iter().take(CUT_CITIES_LIST).map(|p| (&p.0, p.1 as u64)));
    let map1 = ArenaCompactTree::from_zipper(map1.read_zipper(), |x| *x as u64);
    let map2 = ArenaCompactTree::from_zipper(map2.read_zipper(), |x| *x as u64);
    bencher.bench_local(|| {
        let pz = ProductZipperG::new(map1.read_zipper_u64(), [map2.read_zipper_u64()]);
        *black_box(&mut sink) = pz.into_cata_side_effect(val_count_cata);
    });
}

#[cfg(feature="arena_compact")]
#[divan::bench()]
fn generic_pathmap_act(bencher: Bencher) {
    use pathmap::{
        PathMap,
        arena_compact::{ArenaCompactTree},
        morphisms::Catamorphism,
        zipper::{ProductZipperG},
    };
    let mut sink = 0;
    let pairs = read_data();
    let map1 = PathMap::from_iter(pairs.iter().take(CUT_CITIES_LIST).map(|p| (&p.0, p.1 as u64)));
    let map2 = PathMap::from_iter(pairs.iter().take(CUT_CITIES_LIST).map(|p| (&p.0, p.1 as u64)));
    // let map1 = ArenaCompactTree::from_zipper(map1.read_zipper(), |x| *x as u64);
    let map2 = ArenaCompactTree::from_zipper(map2.read_zipper(), |x| *x as u64);
    bencher.bench_local(|| {
        let pz = ProductZipperG::new(map1.read_zipper(), [map2.read_zipper_u64()]);
        *black_box(&mut sink) = pz.into_cata_side_effect(val_count_cata);
    });
}
