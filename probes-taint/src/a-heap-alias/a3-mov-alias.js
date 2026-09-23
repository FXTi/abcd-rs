// Family A probe: store through a Mov alias of the object (TP —
// rung-0 def-chain resolution sees p and o share the alloc site).
// Ground truth: p === o, so o.secret IS tainted.
var TAINT = "tainted";
function main() {
  let o = {};
  let p = o;
  p.secret = TAINT;
  print(o.secret);
}
main();
