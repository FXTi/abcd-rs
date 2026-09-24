// (a) sync generator delegating to another generator; the delegate's
// RETURN value becomes the yield* expression's value.
function* inner() {
    yield 1;
    yield 2;
    return "inner-done";
}

function* outer() {
    const ret = yield* inner();
    yield ret;
}

const log = [];
for (const v of outer()) {
    log.push(v);
}
print(log.join(","));
