// Family D probe: taint thrown inside a RESOLVED callee lands on the
// caller's catch binding (TP — return_flow Throw wiring, T5/T10).
// Ground truth: boom throws its argument; the caught value IS tainted.
var TAINT = "tainted";
function main() {
  function boom(x) { throw x; }
  try {
    boom(TAINT);
  } catch (e) {
    print(e);
  }
}
main();
