// Family A probe: phi merge of the aliased object and a fresh one —
// the rung-0 site union still intersects o's site (TP; the merge is a
// weak update, so this also exercises the weak-update path).
// Ground truth: TAINT.length is 7, the branch is NOT taken at runtime,
// p === o on every execution — the flow is real.
var TAINT = "tainted";
function main() {
  let o = {};
  let p = o;
  if (TAINT.length > 100) { p = {}; }
  p.secret = TAINT;
  print(o.secret);
}
main();
