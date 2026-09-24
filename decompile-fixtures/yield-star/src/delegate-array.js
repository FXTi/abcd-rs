// (b) sync yield* over a plain iterable (array) — delegation through
// the sync iterator protocol, no generator delegate.
function* outer() {
    yield 0;
    yield* [10, 20, 30];
    yield 99;
}

const log = [];
for (const v of outer()) {
    log.push(v);
}
print(log.join(","));
