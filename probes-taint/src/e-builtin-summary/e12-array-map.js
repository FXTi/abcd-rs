// Family E probe (t-P4): the gap RETURN channel — map's callback
// returns its (tainted) formal; the gap return wires that taint onto
// the result array's [AnyIndex] elements, and the indexed read of the
// result fires.
// Ground truth: b[0] IS the callback's return over the tainted element
// — the flow is real.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.push(TAINT);
  let b = a.map(function (e) { return e; });
  print(b[0]);
}
main();
