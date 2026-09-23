// Family E probe: Object.assign's alias_flow matches WHOLE-VALUE taint
// on param(1) only — the source literal's FIELD taint is heap-keyed
// and never enters the target object (KNOWN FN; a field-sensitive
// summary endpoint over heap facts — rung-1 modeling — closes it).
// Ground truth: assign copies secret onto o, so o.secret IS tainted.
var TAINT = "tainted";
function main() {
  let o = {};
  Object.assign(o, { secret: TAINT });
  print(o.secret);
}
main();
