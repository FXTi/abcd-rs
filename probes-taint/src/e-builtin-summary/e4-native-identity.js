// Family E probe: no summary, external-but-named callee — the
// conservative keep + identity heuristic (fallback ladder rung 3)
// carries operand taint to the result (TP; the annotation asserts
// parseFloat shows up in the named-miss log, i.e. no summary fired).
// The sentinel was parseInt until t-P5 REGISTERED it (the ladder
// moved; the unsummarized-native pin moved to parseFloat, its
// deliberately-unregistered sibling).
// Ground truth: parseFloat's result derives from the tainted input.
var TAINT = "tainted";
function main() {
  let n = parseFloat(TAINT);
  print(n);
}
main();
