// BAIL case: a hand-rolled iterator-protocol loop inside a generator —
// NOT `yield*`. The YieldStar fold must leave this loud.
function* outer() {
    const it = [1, 2, 3][Symbol.iterator]();
    let r = it.next();
    while (!r.done) {
        yield r.value;
        r = it.next();
    }
}

const log = [];
for (const v of outer()) {
    log.push(v);
}
print(log.join(","));
