//! Scratch: print decompiled text for one fixture.
use abcd_decompile::emit::{EmitOptions, decompile_module};
fn main() {
    let data = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let file = abcd_file::decode(&data).unwrap();
    let module = abcd_lift::lift_file(&file).unwrap();
    let mut opts = EmitOptions::default();
    if std::env::var_os("GATE").is_some() {
        opts.call_entry = true;
    }
    print!("{}", decompile_module(&module, &opts).text);
}
