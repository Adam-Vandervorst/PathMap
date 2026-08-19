
use std::thread;
use std::sync::mpsc;

use divan::{Divan, Bencher};

use pathmap::PathMap;
use pathmap::zipper::*;

fn main() {
    let divan = Divan::from_args()
        .sample_count(8);

    divan.main();
}

// The test parameters take the form `(elements, thread_cnt)`
//NOTE: Using &str for thread_cnt makes sure we can keep leading zeros in the output so it sorts better
const TEST_ARGS: [(usize, &str); 50] = [
    (512, "000"), (512, "001"), (512, "002"), (512, "004"), (512, "008"), (512, "016"), (512, "032"), (512, "064"), (512, "128"), (512, "256"),
    (4096, "000"), (4096, "001"), (4096, "002"), (4096, "004"), (4096, "008"), (4096, "016"), (4096, "032"), (4096, "064"), (4096, "128"), (4096, "256"),
    (32768, "000"), (32768, "001"), (32768, "002"), (32768, "004"), (32768, "008"), (32768, "016"), (32768, "032"), (32768, "064"), (32768, "128"), (32768, "256"),
    (262144, "000"), (262144, "001"), (262144, "002"), (262144, "004"), (262144, "008"), (262144, "016"), (262144, "032"), (262144, "064"), (262144, "128"), (262144, "256"),
    (2097152, "000"), (2097152, "001"), (2097152, "002"), (2097152, "004"), (2097152, "008"), (2097152, "016"), (2097152, "032"), (2097152, "064"), (2097152, "128"), (2097152, "256"),
    // (16777216, "000"), (16777216, "001"), (16777216, "002"), (16777216, "004"), (16777216, "008"), (16777216, "016"), (16777216, "032"), (16777216, "064"), (16777216, "128"), (16777216, "256"),
    // (100_000_000, "000"), (100_000_000, "001"), (100_000_000, "002"), (100_000_000, "004"), (100_000_000, "008"), (100_000_000, "016"), (100_000_000, "032"), (100_000_000, "064"), (100_000_000, "128"), (100_000_000, "256"),
];

#[divan::bench(sample_size = 1, args = TEST_ARGS)]
fn parallel_read_zipper_get(bencher: Bencher, (elements, thread_cnt): (usize, &str)) {
    let thread_cnt = usize::from_str_radix(thread_cnt, 10).unwrap();
    let real_thread_cnt = thread_cnt.max(1);

    let mut map = PathMap::<usize>::new();
    let elements_per_thread = elements / real_thread_cnt;
    for n in 0..real_thread_cnt {
        let path = [n as u8];
        let mut zipper = map.write_zipper_at_path(&path);
        for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
            zipper.move_to_path(prefix_key(&(i as u64)));
            zipper.set_val(i);
        }
    }

    thread::scope(|scope| {

        let mut zipper_senders: Vec<mpsc::Sender<ReadZipperUntracked<'_, '_, usize>>> = Vec::with_capacity(thread_cnt);
        let mut signal_receivers: Vec<mpsc::Receiver<bool>> = Vec::with_capacity(thread_cnt);

        //Spawn all the threads
        for n in 0..thread_cnt {
            let (zipper_tx, zipper_rx) = mpsc::channel::<ReadZipperUntracked<'_, '_, usize>>();
            zipper_senders.push(zipper_tx);
            let (signal_tx, signal_rx) = mpsc::channel::<bool>();
            signal_receivers.push(signal_rx);

            scope.spawn(move || {
                loop {
                    //The thread will block here waiting for the zipper to be sent
                    match zipper_rx.recv() {
                        Ok(mut zipper) => {
                            //We got the zipper, do the stuff
                            for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                                zipper.move_to_path(prefix_key(&(i as u64)));
                                assert_eq!(zipper.get_val().unwrap(), &i);
                            }

                            //Tell the main thread we're done
                            signal_tx.send(true).unwrap();
                        },
                        Err(_) => {
                            //The zipper_sender channel is closed, meaning it's time to shut down
                            break;
                        }
                    }
                }
            });
        }

        bencher.with_inputs(|| {}).bench_local_values(|()| {
            if thread_cnt > 0 {

                //Dispatch a zipper to each thread
                for n in 0..thread_cnt {
                    let path = [n as u8];
                    let zipper = map.read_zipper_at_path(&path);
                    zipper_senders[n].send(zipper).unwrap();
                };

                //Wait for the threads to all be done
                for n in 0..thread_cnt {
                    assert_eq!(signal_receivers[n].recv().unwrap(), true);
                };

            } else {
                //No-thread case, to measure overhead of sync and spawning vs. 1-thread case
                let path = [0];
                let mut zipper = map.read_zipper_at_path(&path);
                for i in 0..elements {
                    zipper.move_to_path(prefix_key(&(i as u64)));
                    assert_eq!(zipper.get_val().unwrap(), &i);
                }
            }
        });
    });
}

#[divan::bench(sample_size = 1, args = TEST_ARGS)]
fn parallel_insert(bencher: Bencher, (elements, thread_cnt): (usize, &str)) {
    let thread_cnt = usize::from_str_radix(thread_cnt, 10).unwrap();
    let real_thread_cnt = thread_cnt.max(1);
    let elements_per_thread = elements / real_thread_cnt;

    let mut map = PathMap::<usize>::new();
    let zipper_head = map.zipper_head();

    thread::scope(|scope| {

        let mut zipper_senders: Vec<mpsc::Sender<WriteZipperTracked<'_, '_, usize>>> = Vec::with_capacity(thread_cnt);
        let mut signal_receivers: Vec<mpsc::Receiver<bool>> = Vec::with_capacity(thread_cnt);

        //Spawn all the threads
        for n in 0..thread_cnt {
            let (zipper_tx, zipper_rx) = mpsc::channel::<WriteZipperTracked<'_, '_, usize>>();
            zipper_senders.push(zipper_tx);
            let (signal_tx, signal_rx) = mpsc::channel::<bool>();
            signal_receivers.push(signal_rx);

            scope.spawn(move || {
                loop {
                    //The thread will block here waiting for the zipper to be sent
                    match zipper_rx.recv() {
                        Ok(mut zipper) => {
                            //We got the zipper, do the stuff
                            for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                                zipper.move_to_path(prefix_key(&(i as u64)));
                                zipper.set_val(i);
                            }

                            //Tell the main thread we're done
                            signal_tx.send(true).unwrap();
                        },
                        Err(_) => {
                            //The zipper_sender channel is closed, meaning it's time to shut down
                            break;
                        }
                    }
                }
            });
        }

        bencher.with_inputs(|| {}).bench_local_values(|()| {
            if thread_cnt > 0 {

                //Dispatch a zipper to each thread
                for n in 0..thread_cnt {
                    let path = [n as u8];
                    let zipper = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(path) };
                    zipper_senders[n].send(zipper).unwrap();
                };

                //Wait for the threads to all be done
                for n in 0..thread_cnt {
                    assert_eq!(signal_receivers[n].recv().unwrap(), true);
                };

            } else {
                //No-thread case, to measure overhead of sync vs. 1-thread case
                let mut zipper = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(&[0]) };
                for i in 0..elements {
                    zipper.move_to_path(prefix_key(&(i as u64)));
                    zipper.set_val(i);
                }
            }
        });
    });
}

#[divan::bench(sample_size = 1, args = TEST_ARGS)]
fn parallel_copy_known_path(bencher: Bencher, (elements, thread_cnt): (usize, &str)) {
    let thread_cnt = usize::from_str_radix(thread_cnt, 10).unwrap();
    let real_thread_cnt = thread_cnt.max(1);
    let elements_per_thread = elements / real_thread_cnt;

    let mut map = PathMap::<usize>::new();
    let mut zipper = map.write_zipper_at_path(b"in");
    for n in 0..real_thread_cnt {
        for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
            zipper.descend_to_byte(n as u8);
            zipper.descend_to(i.to_be_bytes());
            zipper.set_val(i);
            zipper.reset();
        }
    }
    drop(zipper);

    let zipper_head = map.zipper_head();

    thread::scope(|scope| {

        let mut zipper_senders: Vec<mpsc::Sender<(ReadZipperTracked<'_, '_, usize>, WriteZipperTracked<'_, '_, usize>)>> = Vec::with_capacity(thread_cnt);
        let mut signal_receivers: Vec<mpsc::Receiver<bool>> = Vec::with_capacity(thread_cnt);

        //Spawn all the threads
        for n in 0..thread_cnt {
            let (zipper_tx, zipper_rx) = mpsc::channel();
            zipper_senders.push(zipper_tx);
            let (signal_tx, signal_rx) = mpsc::channel::<bool>();
            signal_receivers.push(signal_rx);

            scope.spawn(move || {
                loop {
                    //The thread will block here waiting for the zippers to be sent
                    match zipper_rx.recv() {
                        Ok((mut reader_z, mut writer_z)) => {
                            //We got the zippers, do the stuff
                            let witness = reader_z.witness();
                            for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                                let buf = i.to_be_bytes();
                                reader_z.move_to_path(&buf);
                                let val = reader_z.get_val_with_witness(&witness).unwrap();

                                writer_z.move_to_path(&buf);
                                writer_z.set_val(*val);
                            }

                            //Tell the main thread we're done
                            signal_tx.send(true).unwrap();
                        },
                        Err(_) => {
                            //The zipper_sender channel is closed, meaning it's time to shut down
                            break;
                        }
                    }
                }
            });
        }

        bencher.with_inputs(|| {
            let mut writer_z = zipper_head.write_zipper_at_exclusive_path(b"out").unwrap();
            writer_z.remove_branches(true);
        }).bench_local_values(|()| {
            if thread_cnt > 0 {

                //Dispatch a zipper to each thread
                for n in 0..thread_cnt {
                    let path = vec![b'o', b'u', b't', n as u8];
                    let writer_z = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(path) };
                    let path = vec![b'i', b'n', n as u8];
                    let reader_z = unsafe{ zipper_head.read_zipper_at_path_unchecked(path) };

                    zipper_senders[n].send((reader_z, writer_z)).unwrap();
                };

                //Wait for the threads to all be done
                for n in 0..thread_cnt {
                    assert_eq!(signal_receivers[n].recv().unwrap(), true);
                };

            } else {
                //No-thread case, to measure overhead of sync vs. 1-thread case
                let mut writer_z = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(&[b'o', b'u', b't', 0]) };
                let mut reader_z = unsafe{ zipper_head.read_zipper_at_path_unchecked(&[b'i', b'n', 0]) };
                let witness = reader_z.witness();
                for i in 0..elements {
                    reader_z.move_to_path(i.to_be_bytes());
                    let val = reader_z.get_val_with_witness(&witness).unwrap();

                    writer_z.move_to_path(i.to_be_bytes());
                    writer_z.set_val(*val);
                }
            }
        });
    });
}

#[divan::bench(sample_size = 1, args = TEST_ARGS)]
fn parallel_copy_traverse(bencher: Bencher, (elements, thread_cnt): (usize, &str)) {
    let thread_cnt = usize::from_str_radix(thread_cnt, 10).unwrap();
    let real_thread_cnt = thread_cnt.max(1);
    let elements_per_thread = elements / real_thread_cnt;

    let mut map = PathMap::<usize>::new();
    let mut zipper = map.write_zipper_at_path(b"in");
    for n in 0..real_thread_cnt {
        for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
            zipper.descend_to_byte(n as u8);
            zipper.descend_to(i.to_be_bytes());
            zipper.set_val(i);
            zipper.reset();
        }
    }
    drop(zipper);

    let zipper_head = map.zipper_head();

    thread::scope(|scope| {

        let mut zipper_senders: Vec<mpsc::Sender<(ReadZipperTracked<'_, '_, usize>, WriteZipperTracked<'_, '_, usize>)>> = Vec::with_capacity(thread_cnt);
        let mut signal_receivers: Vec<mpsc::Receiver<bool>> = Vec::with_capacity(thread_cnt);

        //Spawn all the threads
        for _ in 0..thread_cnt {
            let (zipper_tx, zipper_rx) = mpsc::channel();
            zipper_senders.push(zipper_tx);
            let (signal_tx, signal_rx) = mpsc::channel::<bool>();
            signal_receivers.push(signal_rx);

            scope.spawn(move || {
                loop {
                    let mut sanity_counter = 0;

                    //The thread will block here waiting for the zippers to be sent
                    match zipper_rx.recv() {
                        Ok((mut reader_z, mut writer_z)) => {
                            //We got the zippers, do the stuff
                            let witness = reader_z.witness();
                            while let Some(val) = reader_z.to_next_get_val_with_witness(&witness) {
                                writer_z.move_to_path(reader_z.path());
                                writer_z.set_val(*val);

                                sanity_counter += 1;
                            }

                            assert_eq!(sanity_counter, elements_per_thread);

                            //Tell the main thread we're done
                            signal_tx.send(true).unwrap();
                        },
                        Err(_) => {
                            //The zipper_sender channel is closed, meaning it's time to shut down
                            break;
                        }
                    }
                }
            });
        }

        bencher.with_inputs(|| {
            let mut writer_z = zipper_head.write_zipper_at_exclusive_path(b"out").unwrap();
            writer_z.remove_branches(true);
        }).bench_local_values(|()| {
            if thread_cnt > 0 {

                //Dispatch a zipper to each thread
                for n in 0..thread_cnt {
                    let path = vec![b'o', b'u', b't', n as u8];
                    let writer_z = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(path) };
                    let path = vec![b'i', b'n', n as u8];
                    let reader_z = unsafe{ zipper_head.read_zipper_at_path_unchecked(path) };

                    zipper_senders[n].send((reader_z, writer_z)).unwrap();
                };

                //Wait for the threads to all be done
                for n in 0..thread_cnt {
                    assert_eq!(signal_receivers[n].recv().unwrap(), true);
                };

            } else {
                //No-thread case, to measure overhead of sync vs. 1-thread case
                let mut sanity_counter = 0;
                let mut writer_z = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(&[b'o', b'u', b't', 0]) };
                let mut reader_z = unsafe{ zipper_head.read_zipper_at_path_unchecked(&[b'i', b'n', 0]) };
                let witness = reader_z.witness();
                while let Some(val) = reader_z.to_next_get_val_with_witness(&witness) {
                    writer_z.move_to_path(reader_z.path());
                    writer_z.set_val(*val);
                    sanity_counter += 1;
                }
                assert_eq!(sanity_counter, elements_per_thread);
            }
        });
    });
    drop(zipper_head);
}

fn prefix_key(k: &u64) -> &[u8] {
    let bs = (8 - k.leading_zeros()/8) as u8;
    let kp: *const u64 = k;
    unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
}
