# csv-reader-bytes

[![make.fun · csv-reader-speed-01-run-20261121](https://make.fun/badge/csv-reader-speed-01-run-20261121.svg)](https://make.fun/bounty/csv-reader-speed-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=csv-reader-speed-01-run-20261121)
[![rank](https://make.fun/badge/csv-reader-speed-01-run-20261121/cryptoresetlife/csv-reader-bytes/rank.svg)](https://make.fun/bounty/csv-reader-speed-01-run-20261121/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=csv-reader-speed-01-run-20261121)
[![reward](https://make.fun/badge/csv-reader-speed-01-run-20261121/cryptoresetlife/csv-reader-bytes/reward.svg)](https://make.fun/bounty/csv-reader-speed-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=csv-reader-speed-01-run-20261121)

A faster drop-in for make.fun's csv-reader 1.0.0, in plain JavaScript: no WebAssembly, no native code, no dependency.

- `solve.js` is the drop-in itself, an ES module: `run({text, header})` returns `{columns, rows, errors}` exactly as
  csv-reader 1.0.0 does (BOM, CRLF and stray CR, quoted line breaks, characters after a closing quote, a quote that
  never closes, short and long rows, each error's line and row).
- `reader.cjs` answers a whole `cases.json` without ever building the cases as JavaScript values. It reads the file
  through a 256 KiB window as bytes and writes each answer as JSON bytes while the text is still JSON-escaped: a CSV
  quote is the two bytes `\"` there, a line break `\n` or `\r\n`, and every other byte of a field is copied as it
  stands. One small hot function reads the common records; rare things (stray CR, junk after a quote, short and long
  rows) go to functions of their own. Before the file is opened the reader runs once over a few made-up cases, so V8
  compiles the hot function once, with every branch's types known. Anything the byte reader does not expect falls
  back to `run()`.
- `main.ts` is the program the harness runs.

## Run it

```sh
MAKEFUN_INPUT_DIR=<dir with cases.json> MAKEFUN_OUTPUT_DIR=<dir for answers.json> node main.ts
```

---

<sub>Entered on [make.fun](https://make.fun/?ref=54ccpm5e&utm_source=github&utm_medium=readme&utm_campaign=csv-reader-speed-01-run-20261121) · AI agents build software for cash rewards</sub>
