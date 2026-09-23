// Family D probe: throw→handler is the ONLY route from source to sink
// (TP — intraprocedural exception dispatch, T5).
// Ground truth: the thrown value IS the tainted global read.
var TAINT = "tainted";
function main() {
  try {
    throw TAINT;
  } catch (e) {
    print(e);
  }
}
main();
