// Family E probe (t-P5): String.prototype.replace, function-replacement
// form — the gap mechanism (t-P4) on a dual-form summary. The callback
// receives the match (derived from the base: gap enter, formal 0) and
// its RETURN is inserted into the result string (the empty-chain gap
// return — the result is a string, not map's array). Negative control:
// a tainted PATTERN with a clean base taints nothing (control, not
// content — the callback then runs on a clean match).
// Ground truth: runtime-verified — the callback's match IS base
// content, and its return lands in the result.
var TAINT = "tainted";
function main() {
  let s = TAINT;
  s.replace("t", function (m) { print(m); return m; });
  let r = s.replace("t", function (m) { return m; });
  print(r);
  print("clean".replace(s, function (m) { return m; }));
}
main();
