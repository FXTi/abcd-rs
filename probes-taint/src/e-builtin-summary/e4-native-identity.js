// Family E probe: no summary, external-but-named callee — the
// conservative keep + identity heuristic (fallback ladder rung 3)
// carries operand taint to the result (TP; the annotation asserts
// parseInt shows up in the named-miss log, i.e. no summary fired).
// Ground truth: parseInt's result derives from the tainted input.
var TAINT = "tainted";
function main() {
  let n = parseInt(TAINT);
  print(n);
}
main();
