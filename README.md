# in-place-string-map

Someone said C was better than Rust at in-place string modifications. So I made this.

```rust
use in_place_string_map::MapInPlace;

fn decode_percent(s: &mut str) -> &mut str {
    let mut m = MapInPlace::new(s);

    while let Some(c) = m.pop() {
        match c {
            '%' => {
                let num = m.pop_chars(2).expect("not enough chars");
                let n = u8::from_str_radix(num, 16).expect("invalid hex");
                m.push(n as char).expect("no more capacity");
            }
            _ => {
                m.push(c).expect("no more capacity");
            }
        }
    }

    m.into_mapped()
}
```

The only thing you need to be careful of is to not push more bytes than you
have popped so far. Here it's fine since %ff is 2 bytes long (the longest it
can be) but took 3 bytes of source text. It's not unsafe to do this of course,
you'll just fail to push.

More details about how it works are both in the code (it's somewhat commented)
and [the blog
post](https://www.5snb.club/posts/2021/03/27/in-place-string-mapping.html).
