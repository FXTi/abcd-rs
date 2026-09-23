// Family C probe: dynamic dispatch over a phi of two closures — both
// targets are stepped into (set-valued resolution); the real flow
// through id is found (TP). The konst over-approximation produces no
// sink-level FP here because the runtime path really goes through id.
// Ground truth: TAINT.length is 7 > 0, so f === id — the flow is real.
var TAINT = "tainted";
function main() {
  function id(x) { return x; }
  function konst(x) { return "clean"; }
  let f = TAINT.length > 0 ? id : konst;
  print(f(TAINT));
}
main();
