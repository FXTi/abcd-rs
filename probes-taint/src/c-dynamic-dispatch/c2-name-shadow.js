// Family C probe: a USER-DEFINED top-level `print` takes over the
// global binding — but name-keyed sink matching keys on
// TryGetGlobal("print"), so the sink fires on a call whose binding is
// user code (EXPECTED FP — the corpus' own reality: its call-site head
// is user globals named foo/f/testXxx; name keying cannot tell a
// redefined global from the host builtin. No rung closes this; recorded
// as dispatch-axis FP evidence for the rung-1→2 trigger discussion).
// (A LOCAL `function print` shadow does not exercise this axis: es2abc
// mangles local function names to `#*@0*#print`, which never matches.)
// Ground truth: the host print is never called — nothing is printed.
var TAINT = "tainted";
function print(x) { return x; }
function main() {
  print(TAINT);
}
main();
