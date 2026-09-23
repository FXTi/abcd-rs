// Family C probe: method-valued callee off a local object — dispatch
// is UNRESOLVED at rung 0 (no receiver typing), but the fallback
// ladder's identity heuristic still carries the argument taint to the
// call result (TP via native/unknown keep, not via dispatch).
// Ground truth: o.log returns its argument — the flow is real.
var TAINT = "tainted";
function main() {
  let o = {};
  o.log = function (x) { return x; };
  print(o.log(TAINT));
}
main();
