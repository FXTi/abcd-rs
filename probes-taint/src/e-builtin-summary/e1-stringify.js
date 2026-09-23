// Family E probe: exclusive summary application — JSON.stringify's
// param(0)→return flow carries the taint (TP; the annotation also
// asserts the SUMMARY fired, i.e. this is not the identity heuristic).
// Ground truth: the JSON string derives from the tainted value.
var TAINT = "tainted";
function main() {
  let s = JSON.stringify(TAINT);
  print(s);
}
main();
