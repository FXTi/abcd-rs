# yield* (YieldStar) decompile fixtures (d-P15)

Standalone fixtures for the `yield*` delegation fold in `abcd-decompile`
(NOT part of `exports/corpus` — the corpus gates hard-assert fixture
counts; this directory is deliberately outside it).

Sources (`src/*.js`, hand-written, Apache-2.0 project origin):

- `delegate-gen.js` — sync `function*` delegating to another generator;
  the delegate's RETURN value is used (`const ret = yield* inner(); yield ret;`).
- `delegate-array.js` — sync `yield*` over a plain iterable (array);
  the delegation result is unused.
- `delegate-async.js` — `async function*` with `yield*` (for-await
  consumption end); the delegate's return value is used.
- `delegate-throw.js` — delegation whose delegate THROWS; the error
  propagates through the delegation to the consumer's try/catch.
  (The consumer loop's try-spanning-a-loop also exercises the
  structurer's try projection: fragmented pre-d-P16 [N69], one
  coalesced try/catch since.)
- `manual-iterator.js` — BAIL case: a hand-rolled iterator-protocol
  loop inside a generator (NOT `yield*`); the fold must leave it loud.

Compiled with the GHCR image's es2abc **24.0.0.0 / baseline** only
(single version/profile is deliberate — these feed shape goldens, not
the version matrix):

```sh
for f in delegate-gen delegate-array delegate-async delegate-throw manual-iterator; do
  docker run --rm --platform linux/amd64 --network none -v "$PWD:/work" \
    ghcr.io/fxti/arkcompiler-test:latest \
    compile --version 24.0.0.0 --profile baseline /work/src/$f.js /work/$f.abc
  docker run --rm --platform linux/amd64 --network none -v "$PWD:/work" \
    ghcr.io/fxti/arkcompiler-test:latest \
    disassemble /work/$f.abc /work/$f.pa
done
```

`*.abc` here is force-added over the top-level `*.abc` gitignore rule
(explicit d-P15 exception — these are the deliverable's inputs).

Node/ark behavior evidence (identical on both, `print` shimmed to
`console.log` under node):

- delegate-gen: `1,2,inner-done`
- delegate-array: `0,10,20,30,99`
- delegate-async: `1,2,inner-done`
- delegate-throw: `before,caught:delegated-boom`
- manual-iterator: `1,2,3`
