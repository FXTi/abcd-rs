//! Scratch: print the recorded source_code for one fixture.
fn main() {
    let path = std::env::args().nth(1).expect("fixture");
    let data = std::fs::read(&path).unwrap();
    let file = abcd_file::decode(&data).unwrap();
    let module = abcd_lift::lift_file(&file).unwrap();
    for f in &module.functions {
        if let Some(d) = &f.debug
            && let Some(s) = &d.source_code
        {
            println!(
                "--- {} source_code:",
                module.sym.resolve(f.name).unwrap_or("?")
            );
            println!("{s}");
        }
    }
}
