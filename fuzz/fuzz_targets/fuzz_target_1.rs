#![no_main]
use libfuzzer_sys::fuzz_target;

use libfuzzer_sys::arbitrary;

#[derive(arbitrary::Arbitrary, Debug)]
struct Ops<'a> {
    initial: String,
    ops: Vec<Op<'a>>,
}

#[derive(arbitrary::Arbitrary, Debug)]
enum Op<'a> {
    Push(char),
    PushStr(&'a str),
    Pop,
    PopChars(usize),
}

fuzz_target!(|ops: Ops<'_>| {
    struct Model {
        unmapped: String,
        mapped: String,
    }

    use in_place_string_map::MapInPlace;

    let Ops {mut initial, ops} = ops;

    let mut model = Model { unmapped: initial.clone(), mapped: String::new()};

    let mut m = MapInPlace::new(&mut initial);

            for o in ops {
                match o {
                    Op::Pop => {
                        let real = m.pop();

                        let model = if model.unmapped.len() == 0 {
                            None
                        } else {
                            Some(model.unmapped.remove(0))
                        };

                        assert_eq!(real, model);
                    },
                    Op::Push(c) => {
                        if m.push(c).is_err() {
                            return;
                        }
                        model.mapped.push(c);
                    }
                    Op::PushStr(c) => {
                        if m.push_str(c).is_err() {
                            return;
                        }
                        model.mapped.push_str(c);
                    }
                    Op::PopChars(n) => {
                        let popped = m.pop_chars(n);

                        if popped.is_none() {
                            continue;
                        }

                        let model_str = {
                            if model.unmapped.len() < n || n == 0 {
                                None
                            } else {
                                let mut temp = String::new();
                                for _ in 0..n { temp.push(model.unmapped.remove(0)); }
                                Some(temp)
                            }
                        };

                        assert_eq!(popped, model_str.as_deref());
                    }
                }

                assert_eq!(std::str::from_utf8(m.all().as_bytes()).unwrap(), m.all(), "UTF-8 did not round trip");
                assert_eq!(m.unmapped(), model.unmapped, "unmapped did not match");
                assert_eq!(m.mapped(), model.mapped, "mapped did not match");
            }
    // fuzzed code goes here
});
