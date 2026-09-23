// Family E probe (t-P4): filter's callback is a PREDICATE — its boolean
// return taints nothing (return channel None); the result array's
// elements are the base's KEPT elements, a static
// Field([AnyIndex])→ReturnField([AnyIndex]) flow. The predicate body
// still receives the tainted element (the gap enter), but `e > 1`
// only feeds the comparison.
// Ground truth: b contains the pushed TAINT — the flow is real.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.push(TAINT);
  let b = a.filter(function (e) { return true; });
  print(b[0]);
}
main();
