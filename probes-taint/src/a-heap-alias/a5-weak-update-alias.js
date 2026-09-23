// Family A probe: sanitizing store through an unproven alias is a WEAK
// update at rung 0 (p is a call result → no must-alias proof) — the
// taint on o.secret survives and the sink fires (EXPECTED FP; rung 1's
// points_to proves p === o and the strong update kills the taint).
// Ground truth: at runtime p === o, so p.secret = "clean" overwrites
// the taint — the flow does NOT exist.
var TAINT = "tainted";
function main() {
  function id(x) { return x; }
  let o = {};
  let p = id(o);
  o.secret = TAINT;
  p.secret = "clean";
  print(o.secret);
}
main();
