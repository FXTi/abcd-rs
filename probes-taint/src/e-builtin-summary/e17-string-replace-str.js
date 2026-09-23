// Family E probe (t-P5): String.prototype.replace, string-replacement
// form. The result's content derives from the BASE (the non-matched
// parts — and `$`-substituted group text is base content too) and from
// the REPLACEMENT (inserted verbatim). The PATTERN only selects what is
// replaced — control, not content (the repeat-count discipline, e10):
// a tainted pattern over a clean base must NOT taint the result (the
// identity heuristic would; the clean sink pins the summary's win).
// Ground truth: runtime-verified — the replaced strings carry the
// tainted parts exactly as annotated.
var TAINT = "tainted";
function main() {
  let s = TAINT;
  print(s.replace("a", "!"));
  print("clean".replace("a", s));
  print("clean".replace(s, "!"));
}
main();
