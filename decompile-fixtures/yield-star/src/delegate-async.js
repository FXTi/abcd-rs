// (c) async generator with yield* — for-await consumption end.
async function* inner() {
    yield 1;
    yield 2;
    return "inner-done";
}

async function* outer() {
    const ret = yield* inner();
    yield ret;
}

async function main() {
    const log = [];
    for await (const v of outer()) {
        log.push(v);
    }
    print(log.join(","));
}

main();
