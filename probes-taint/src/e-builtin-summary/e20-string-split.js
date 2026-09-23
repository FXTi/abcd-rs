// Family E probe (t-P5): String.prototype.split — the result array's
// pieces derive from the base's content (Base→Return; the element read
// cuts one step). The SEPARATOR is removed, not inserted — control,
// not content: a tainted separator over a clean base taints nothing
// (the identity heuristic would; the clean sink pins the summary).
// Ground truth: runtime-verified — "x,y".split(tainted) is ["x,y"].
var TAINT = "tainted";
function main() {
  let s = TAINT;
  let parts = s.split("a");
  print(parts[0]);
  print("x,y".split(s)[0]);
}
main();
