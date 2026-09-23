// Family E probe (t-P5): RegExp.prototype.test — a pure match VERDICT
// (fresh boolean, the Object.is discipline: verdicts are control, not
// content). A tainted haystack must NOT taint the verdict; the clean
// sink pins the no-flow summary against the identity heuristic (which
// would taint any result whose operand is tainted). The receiver is a
// regexp LITERAL — es2abc lowers it to `new RegExp(...)`, so the family
// types through the t-P5 constructor-result arm (the corpus' r.test
// ×18 rescue).
// Ground truth: runtime-verified — r.test(tainted) is a boolean.
var TAINT = "tainted";
function main() {
  let r = /a+/;
  print(r.test(TAINT));
}
main();
