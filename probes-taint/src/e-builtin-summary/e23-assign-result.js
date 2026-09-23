// Family E probe (t-P5): Object.assign's result identity — the call
// RESULT is param 0 (the mutated target), so the source literal's
// tainted field reaches `o.secret` through the fresh-object result
// value, not just through the e5 alias-flow shape (which names the
// target directly). The t-P5 deepening added Param(i)→Return on top of
// the alias flows. Single-assign shape: a second assign's unknown-base
// result would meet the first's heap fact through the load rule's
// may-alias wildcard (the e13 lesson) — the clean control lives in the
// mechanism twin (`assign_result_carries_source_taint`) instead.
// Ground truth: runtime-verified — o.secret IS the tainted field.
var TAINT = "tainted";
function main() {
  let o = Object.assign({}, { secret: TAINT });
  print(o.secret);
}
main();
