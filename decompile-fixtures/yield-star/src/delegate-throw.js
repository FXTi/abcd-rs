// (d) delegation whose delegate THROWS — error propagation through
// the delegation; the delegating generator's try/catch observes it.
function* boom() {
    yield "before";
    throw new Error("delegated-boom");
}

function* outer() {
    try {
        yield* boom();
        yield "unreachable";
    } catch (e) {
        yield "caught:" + e.message;
    }
    yield "after";
}

const log = [];
for (const v of outer()) {
    log.push(v);
}
print(log.join(","));
