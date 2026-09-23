//! Scratch: function kinds + modifiers.
fn main() {
    let data = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let file = abcd_file::decode(&data).unwrap();
    let module = abcd_lift::lift_file(&file).unwrap();
    for f in &module.functions {
        println!(
            "{}: kind={:?} modifiers={:?}",
            module.sym.resolve(f.name).unwrap_or("?"),
            f.kind,
            f.modifiers
        );
    }
}
