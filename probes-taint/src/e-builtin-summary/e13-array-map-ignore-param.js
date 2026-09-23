// Family E probe (t-P4, negative control): map's callback IGNORES its
// parameter and returns a constant — the result array's elements carry
// no taint (the gap enter seeded the formal, but nothing in the body
// flows it to the return). Pins that the result's taint comes from the
// callback's RETURN, not from the base array directly.
// Ground truth: b[0] is 0 — the flow does NOT exist.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.push(TAINT);
  let b = a.map(function (e) { return 0; });
  print(b[0]);
}
main();
