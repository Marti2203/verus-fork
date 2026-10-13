#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] scoped_threads_borrow verus_code! {
        use vstd::thread::*;

        fn test(v: &Vec<u64>, x: u64)
            requires x < 100,
        {
            let n = scope(|s: Scope| -> (r: usize)
                ensures r == v.len()
            {
                let h1 = s.spawn(|| -> (r: usize) ensures r == v.len() { v.len() });
                let h2 = s.spawn(|| -> (r: u64) requires x < 100 ensures r == x + 1 { x + 1 });
                if let Ok(y) = h2.join() {
                    assert(y == x + 1);
                }
                match h1.join() {
                    Ok(n) => n,
                    Err(_) => v.len(),
                }
            });
            assert(n == v.len());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] scoped_threads_fail verus_code! {
        use vstd::thread::*;

        fn spawn_requires(x: u64) {
            scope(|s: Scope| {
                let h = s.spawn(|| -> (r: u64) requires x < 100 { x + 1 }); // FAILS
            });
        }

        fn join_can_fail(v: &Vec<u64>) {
            scope(|s: Scope| {
                let h = s.spawn(|| -> (r: usize) ensures r == v.len() { v.len() });
                let r = h.join();
                assert(r is Ok); // FAILS
            });
        }

        fn scope_ret() {
            let r = scope(|s: Scope| -> (r: u64) ensures r < 10 { 5 });
            assert(r == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] thread_builder verus_code! {
        use vstd::thread::*;

        fn test() {
            let b = Builder::new().name("worker".to_string()).stack_size(1 << 24);
            if let Ok(h) = b.spawn(move || -> (r: u64) ensures r == 7 { 7 }) {
                if let Ok(v) = h.join() {
                    assert(v == 7);
                    assert(v == 8); // FAILS
                }
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] thread_misc verus_code! {
        use vstd::prelude::*;
        use std::time::Duration;

        vstd::thread_local! { static LIMIT: u64 = 10; }

        fn test() {
            std::thread::sleep(Duration::from_millis(1));
            std::thread::yield_now();
            let _id = std::thread::current().id();
            let _n = std::thread::available_parallelism();
            let r = LIMIT.with(|l: &u64| -> (r: u64) ensures r < 100 { if *l < 100 { *l } else { 0 } });
            assert(r < 100);
            let r = LIMIT.with(|l: &u64| *l);
            assert(r == 10); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] sync_primitives verus_code! {
        use vstd::rwlock::RwLockPredicate;
        use vstd::sync::*;
        use vstd::thread::*;

        struct Even;
        impl RwLockPredicate<u64> for Even {
            open spec fn inv(self, v: u64) -> bool { v % 2 == 0 }
        }

        fn mutex() -> (r: u64)
            ensures r % 2 == 0
        {
            let m = Mutex::<u64, Even>::new(0, Ghost(Even));
            let cv = Condvar::new();
            scope(|s: Scope| {
                let h = s.spawn(|| {
                    let (v, g) = m.lock();
                    g.release(if v < 1000 { v + 2 } else { 0 });
                    cv.notify_all();
                });
                let (v, g) = m.lock();
                let (v, g) = cv.wait(g, v);
                g.release(v);
                let _ = h.join();
            });
            m.into_inner()
        }

        fn chan() {
            let (tx, rx) = channel::<u64, Even>(Ghost(Even));
            let h = spawn(move || { let _ = tx.send(4); });
            if let Ok(v) = rx.recv() {
                assert(v % 2 == 0);
            }
            let _ = h.join();
        }

        fn barrier() {
            let b = std::sync::Barrier::new(1);
            let _ = b.wait().is_leader();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] sync_primitives_fail verus_code! {
        use vstd::rwlock::RwLockPredicate;
        use vstd::sync::*;

        struct Even;
        impl RwLockPredicate<u64> for Even {
            open spec fn inv(self, v: u64) -> bool { v % 2 == 0 }
        }

        fn release_bad(m: &Mutex<u64, Even>) {
            let (v, g) = m.lock();
            g.release(3); // FAILS
        }

        fn lock_only_inv(m: &Mutex<u64, Even>) {
            let (v, g) = m.lock();
            assert(v == 0); // FAILS
            g.release(v);
        }

        fn send_bad(tx: &Sender<u64, Even>)
            requires tx.pred() == Even,
        {
            let _ = tx.send(5); // FAILS
        }

        fn recv_only_inv(rx: &Receiver<u64, Even>)
            requires rx.pred() == Even,
        {
            if let Ok(v) = rx.recv() {
                assert(v == 2); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] thread_local_init_is_verified verus_code! {
        use vstd::prelude::*;

        pub struct Pos { x: u64 }

        impl Pos {
            #[verifier::type_invariant]
            spec fn wf(self) -> bool { self.x > 0 }
        }

        // The initializer is verified (the `// FAILS` marker is lost inside the macro call)
        vstd::thread_local! { static X: Pos = Pos { x: 0 }; }
    } => Err(err) => assert_vir_error_msg(err, "may fail to meet its declared type invariant")
}
