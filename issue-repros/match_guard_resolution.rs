use vstd::prelude::*;
verus! {

pub struct S { pub n: u64 }

impl S {
    fn bump(&mut self)
        requires old(self).n < 100,
        ensures final(self).n == old(self).n + 1,
    {
        self.n = self.n + 1;
    }

    // guarded arm whose body calls &mut self
    fn guarded(&mut self, o: Option<u64>) -> (r: u64)
        requires old(self).n < 10,
        ensures final(self).n >= old(self).n,
    {
        match o {
            Some(k) if k == 3 => {
                self.bump();
                k
            },
            _ => 0,
        }
    }

    // same without the guard
    fn unguarded(&mut self, o: Option<u64>) -> (r: u64)
        requires old(self).n < 10,
        ensures final(self).n >= old(self).n,
    {
        match o {
            Some(k) => if k == 3 {
                self.bump();
                k
            } else {
                0
            },
            _ => 0,
        }
    }
}

fn main() {}
}
