// (d) delegation whose delegate THROWS — the error propagates through
// the delegation to the consumer's try/catch.
function* boom() {
    yield "before";
    throw new Error("delegated-boom");
}

function* outer() {
    yield* boom();
    yield "after";
}

const it = outer();
const log = [];
try {
    let r = it.next();
    while (!r.done) {
        log.push(r.value);
        r = it.next();
    }
    log.push("completed");
} catch (e) {
    log.push("caught:" + e.message);
}
print(log.join(","));
