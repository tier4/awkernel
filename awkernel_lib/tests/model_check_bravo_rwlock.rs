#[cfg(loom)]
#[test]
fn model_check_rwlock() {
    use awkernel_lib::sync::bravo_rwlock;
    use loom::sync::Arc;

    loom::model(|| {
        bravo_rwlock::init_visible_readers();

        let n = Arc::new(bravo_rwlock::BravoRwLock::new(0));
        let mut readers = Vec::new();
        let mut writers = Vec::new();

        let num_readers = 1;
        let num_writers = 2;
        let num_iterations = 1;

        for i in 0..num_readers {
            let n0 = n.clone();
            let t = loom::thread::spawn(move || {
                for _ in 0..num_iterations {
                    let r = n0.read_cpu_id(i);
                    let data = r.with(|data| unsafe { *data });
                    assert_eq!(data, 0);
                }
            });

            readers.push(t);
        }

        for _ in 0..num_writers {
            let n0 = n.clone();
            let t = loom::thread::spawn(move || {
                for _ in 0..num_iterations {
                    let mut r = n0.write();
                    r.with_mut(|data| unsafe {
                        *data += 1;
                        *data -= 1;
                    });
                }
            });

            writers.push(t);
        }

        for t in readers {
            t.join().unwrap();
        }

        for t in writers {
            t.join().unwrap();
        }
    });
}
