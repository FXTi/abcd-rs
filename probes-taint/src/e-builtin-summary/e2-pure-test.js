// Family E probe: exclusive PURE-TEST summary — Object.is's result is
// a fresh boolean and the operand taint is killed on the
// call-to-return edge (FP guard; proves summary APPLICATION beats the
// native identity heuristic, which would otherwise taint the result).
// Ground truth: Object.is returns a boolean — the flow does NOT exist.
var TAINT = "tainted";
function main() {
  let b = Object.is(TAINT, 1);
  print(b);
}
main();
