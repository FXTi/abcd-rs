// Family D probe: the thrower is a TOP-LEVEL function — a global
// binding, so the call edge is unresolved at rung 0 (the corpus' ~97%
// unknown-callee reality) and the tainted argument never enters boom's
// body; the catch binding stays clean (KNOWN FN; the rung-2 call-graph
// layer's global-call resolution closes it).
// Ground truth: boom really throws the tainted argument and main really
// catches it — the flow is real.
var TAINT = "tainted";
function boom(x) { throw x; }
function main() {
  try {
    boom(TAINT);
  } catch (e) {
    print(e);
  }
}
main();
