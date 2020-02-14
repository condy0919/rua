use std::env;
use std::fs::File;

mod binary;
use binary::undump;

fn main() {
    let mut args = env::args();
    if args.len() > 1 {
        let f = File::open(args.nth(1).unwrap()).expect("Failed to open file");
        let proto = undump(f).expect("undump failed");
        println!("proto = {:?}", proto);
    }

    println!("Hello, world!");
}
