// Family E probe: no summary, resolved callee with a body — the solver
// STEPS INTO the body (TP; the annotation asserts the body_step
// counter fired, i.e. this flow does not ride the identity heuristic).
// Ground truth: passthru returns its argument — the flow is real.
var TAINT = "tainted";
function main() {
  function passthru(x) { return x; }
  let r = passthru(TAINT);
  print(r);
}
main();
