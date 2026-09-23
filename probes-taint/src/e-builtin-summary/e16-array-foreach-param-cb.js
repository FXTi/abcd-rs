// Family E probe (t-P4, the points-to arm): the callback reaches the
// gap site through a PARAMETER of a resolved local helper — the rung-1
// engine's caller fan-out resolves it to the caller's closure alloc
// (the b3 bridge, one engine two consumers), and the receiver param
// types Array through the same engine. The element taint enters the
// nested callback and its print fires.
// Ground truth: the callback receives the pushed TAINT — real flow.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.push(TAINT);
  const each = function (arr, cb) { arr.forEach(cb); };
  each(a, function (e) { print(e); });
}
main();
