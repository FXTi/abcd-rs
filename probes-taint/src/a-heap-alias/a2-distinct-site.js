// Family A probe: distinct alloc sites, same field name (FP guard).
// Ground truth: b.secret was never stored — a hit here is an FP.
var TAINT = "tainted";
function main() {
  let a = {};
  let b = {};
  a.secret = TAINT;
  print(b.secret);
}
main();
