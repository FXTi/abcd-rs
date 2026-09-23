// Family D probe: the thrown value is clean (FP guard, two clean
// sinks: the catch binding and the normal path after the try). The
// tainted local `t` is live across the try but never thrown nor
// printed — any hit here is an FP.
// Ground truth: both printed values are constants.
var TAINT = "tainted";
function main() {
  let t = TAINT;
  try {
    throw "clean";
  } catch (e) {
    print(e);
  }
  print("after");
}
main();
