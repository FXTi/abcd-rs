// Family E probe (t-P3): repeat's COUNT argument does not taint the
// result — the summary (Base→Return only) applies through the constant
// receiver's String family and the tainted count goes nowhere. FP
// guard: the native-identity heuristic (tainted operand ⇒ tainted
// return) WOULD taint the result — this pins summary application
// beating the fallback, e2's prototype-path analogue.
// Ground truth: "x".repeat("tainted") is "" — the result is clean.
var TAINT = "tainted";
function main() {
  let s = "x".repeat(TAINT);
  print(s);
}
main();
