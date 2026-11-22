// The byte reader: answers a whole cases.json without ever building the cases as JavaScript values.
//
// The file is read through a small window as bytes, and each case's answer is written as JSON bytes while its text
// is still JSON-escaped. A CSV quote is the two bytes \" there, a line feed \n, a carriage return \r, and every other
// byte of a field is copied as it stands, so no string is ever decoded or encoded. Anything this reader does not
// expect (another escape, another layout of the file) sends the whole file to solve.js's run() instead, the plain
// drop-in, so the answer is the same either way.
//
// readText is the one hot function: it reads the records that are as most are (plain and quoted fields, commas,
// line breaks, quoted line breaks and doubled quotes) and hands every rare thing to a function of its own (rest:
// the rest of a field with a stray CR, a literal quote or characters after a closing quote; odd: the first record,
// a short, a long or an empty one), so the optimizing compiler has little to compile. Before the file is opened the
// reader is run once over a few made-up cases held in memory (prime), which takes it through every branch, so the
// compiler knows every branch's types and compiles readText once, before the first real byte.
//
// Pure JavaScript, no dependency, nothing kept from one case to the next. CommonJS, since that is what Node starts
// fastest.

'use strict';

const { openSync, closeSync, readSync, writeSync, readFileSync, writeFileSync } = require('node:fs');

const E_STRAY_CR = 0;
const E_QUOTE_JUNK = 1;
const E_UNTERMINATED = 2;
const E_SHORT = 3;
const E_LONG = 4;
const CODES = ['stray_cr', 'quote_junk', 'unterminated_quote', 'short_row', 'long_row'];

/** The output a case opens with when its header is true (24 bytes), and its form when it is false. */
const OPEN_HEADER = '{"columns":             ';
const OPEN_PLAIN = '{"columns":null,"rows":[';

/** 1 for the bytes that end a run of plain field bytes: the comma, the backslash and the quote that ends the text. */
const STOP = new Uint8Array(256);
STOP[44] = 1;
STOP[92] = 1;
STOP[34] = 1;

let IFD = -1; // the input and output files; below 0 the input is SRC and the output goes nowhere (prime)
let OFD = -1;
let SRC = null;
let SRCPOS = 0;
let INP = null; // the input window, CAP bytes and 16 of guard
let OUT = null; // the output not yet written
let ERR = null; // the case's errors, five numbers each
let EXT = null; // the case's long rows' cut fields, as JSON
let CAP = 0;
let HIGH = 0; // the output is written out past this many bytes
let END = 0; // the window holds INP[0..END)
let LIM = 0; // an escape at or past LIM may be cut by the window's end
let EOF = false;
let I = 0; // the next input byte
let O = 0; // the next output byte
let FLUSHED = 0; // the file offset of OUT[0]
let AFTER = 0; // the file offset of what follows the case's first record
let LINE = 1;
let NREC = 0; // the case's records so far
let WIDTH = -1;
let NERR = 0;
let NEXT = 0;

/** Writes all of OUT but its last byte, which a case's end may still change. */
function flush(o) {
  const n = o - 1;
  if (OFD >= 0) {
    let done = 0;
    while (done < n) done += writeSync(OFD, OUT, done, n - done);
  }
  OUT[0] = OUT[n];
  FLUSHED += n;
  return 1;
}

function pushErr(code, line, k, a, b) {
  if (NERR + 5 > ERR.length) {
    const bigger = new Int32Array(ERR.length * 2);
    bigger.set(ERR);
    ERR = bigger;
  }
  ERR[NERR] = code;
  ERR[NERR + 1] = line;
  ERR[NERR + 2] = k;
  ERR[NERR + 3] = a;
  ERR[NERR + 4] = b;
  NERR += 5;
}

/** Room for n more output bytes. */
function room(n) {
  if (O + n <= OUT.length) return;
  O = flush(O);
  if (O + n <= OUT.length) return;
  const bigger = new Uint8Array((O + n) * 2);
  bigger.set(OUT.subarray(0, O));
  OUT = bigger;
}

/** Moves INP[keep..END) to the window's start and reads on. False when the file has nothing more to give. */
function refill(keep) {
  if (EOF) return false;
  const tail = END - keep;
  if (keep > 0) {
    INP.copyWithin(0, keep, END);
    I -= keep;
  }
  if (tail === CAP) {
    // one record fills the window: a wider one, and output room to match
    CAP *= 2;
    const wider = new Uint8Array(CAP + 16);
    wider.set(INP.subarray(0, tail));
    INP = wider;
    const out = new Uint8Array(HIGH + 3 * CAP + 64);
    out.set(OUT.subarray(0, O));
    OUT = out;
  }
  let n = 0;
  if (IFD >= 0) n = readSync(IFD, INP, tail, CAP - tail, null);
  else {
    n = Math.min(CAP - tail, SRC.length - SRCPOS);
    INP.set(SRC.subarray(SRCPOS, SRCPOS + n), tail);
    SRCPOS += n;
  }
  if (n === 0) EOF = true;
  END = tail + n;
  LIM = EOF ? END : END - 8;
  INP.fill(34, END, END + 16);
  return true;
}

/**
 * The rest of an unquoted field from INP[I] on, with everything rare in it: a stray CR, a literal quote, and at
 * `junk` (when it is not below 0) the output offset where the characters after a closing quote begin. How it ended:
 * 1 at a comma, 2 at a line break (both read), 3 at the text's end (not read), 4 at the window's end, 5 at a byte
 * this reader does not read.
 */
function rest(recLine, k, junk) {
  const a = INP;
  const b = OUT;
  const end = END;
  const lim = LIM;
  let i = I;
  let o = O;
  let t = 0;
  for (;;) {
    const c = a[i];
    if (c === 44) {
      i++;
      t = 1;
      break;
    }
    if (c === 92) {
      if (i >= lim) {
        t = 4;
        break;
      }
      const d = a[i + 1];
      if (d === 110) {
        i += 2;
        t = 2;
        break;
      }
      if (d === 114) {
        if (a[i + 2] === 92 && a[i + 3] === 110) {
          i += 4;
          t = 2;
          break;
        }
        pushErr(E_STRAY_CR, recLine, k, 0, 0);
        i += 2;
        continue;
      }
      if (d === 34) {
        b[o] = 92;
        b[o + 1] = 34;
        o += 2;
        i += 2;
        continue;
      }
      t = 5;
      break;
    }
    if (c === 34) {
      t = i >= end ? 4 : 3;
      break;
    }
    b[o++] = c;
    i++;
  }
  if (t < 4 && junk >= 0 && o > junk) pushErr(E_QUOTE_JUNK, recLine, k, 0, 0);
  I = i;
  O = o;
  return t;
}

/**
 * The end of a record that is not a row of the case's width with two fields or more: the first record, a short or a
 * long row, a record of one field, a line that held stray CRs alone. OUT holds it from `ro` as [ "..." , "..." with
 * its last quote written; `ri` is where it began in INP.
 */
function odd(nf, ri, ro, recLine) {
  let o = O;
  const total = nf + 1;
  if (nf === 0 && o === ro + 3 && !(INP[ri] === 92 && INP[ri + 1] === 34)) {
    O = ro; // no characters and no quotes: no record
    return;
  }
  if (WIDTH < 0) {
    WIDTH = total;
    NREC = 1;
    OUT[o++] = 93;
    AFTER = FLUSHED + o;
    O = o;
    put(',"rows":[');
    return;
  }
  if (total < WIDTH) {
    pushErr(E_SHORT, recLine, NREC, total, 0);
    room(3 * (WIDTH - total) + 8);
    o = O;
    for (let k = total; k < WIDTH; k++) {
      OUT[o] = 44;
      OUT[o + 1] = 34;
      OUT[o + 2] = 34;
      o += 3;
    }
  } else if (total > WIDTH) {
    // the comma after the last field kept: WIDTH strings on from the record's first quote
    const b = OUT;
    let p = ro + 1;
    for (let k = 0; k < WIDTH; k++) {
      p++;
      for (;;) {
        const c = b[p];
        if (c === 34) break;
        p += c === 92 ? 2 : 1;
      }
      p += 2;
    }
    p--;
    const len = o - p - 1;
    if (NEXT + len > EXT.length) {
      const bigger = new Uint8Array((NEXT + len) * 2);
      bigger.set(EXT.subarray(0, NEXT));
      EXT = bigger;
    }
    EXT.set(b.subarray(p + 1, o), NEXT);
    pushErr(E_LONG, recLine, NREC, NEXT, len);
    NEXT += len;
    o = p;
  }
  OUT[o] = 93;
  OUT[o + 1] = 44;
  O = o + 2;
  NREC++;
}

/**
 * Reads the text's records from INP[I] on, writing each as a JSON array. 0: the text ended (I is past its closing
 * quote); 1: the window ended inside a record (I is back at the record's start); 2: a byte this reader does not
 * read; 3: the output moved to a wider array (call again).
 */
function readText() {
  const a = INP;
  const b = OUT;
  const stop = STOP;
  const end = END;
  const lim = LIM;
  const high = HIGH;
  let i = I;
  let o = O;
  let line = LINE;
  let nrec = NREC;
  let width = WIDTH;
  let st = 0;
  let ri = i;
  let ro = o;
  let rline = line;
  let rnerr = NERR;
  let rnext = NEXT;
  let c = 0;
  let d = 0;
  let nf = 0;
  let t = 0;

  rec: for (;;) {
    // a record starts here: what a window's end takes the reader back to
    if (o > high) o = flush(o);
    ri = i;
    ro = o;
    rline = line;
    rnerr = NERR;
    rnext = NEXT;

    c = a[i];
    if (c === 92) {
      if (i >= lim) {
        st = 1;
        break;
      }
      d = a[i + 1];
      if (d === 110) {
        i += 2;
        line++;
        continue;
      }
      if (d === 114 && a[i + 2] === 92 && a[i + 3] === 110) {
        i += 4;
        line++;
        continue;
      }
    } else if (c === 34) {
      if (i >= end) {
        st = 1;
        break;
      }
      i++;
      break;
    }

    b[o] = 91;
    b[o + 1] = 34;
    o += 2;
    nf = 0;
    for (;;) {
      // a field starts here, its opening quote written; t says how it ends
      c = a[i];
      if (c === 92 && a[i + 1] === 34) {
        if (i >= lim) {
          st = 1;
          break rec;
        }
        const qi = i;
        const qo = o;
        const qline = line;
        i += 2;
        for (;;) {
          c = a[i];
          while (c !== 92 && c !== 34) {
            b[o++] = c;
            c = a[++i];
          }
          if (c === 34) {
            if (i >= end) {
              st = 1;
              break rec;
            }
            // the text ends inside the quotes: the quote is a character, and the field is read again from it
            i = qi + 2;
            o = qo;
            line = qline;
            pushErr(E_UNTERMINATED, rline, nrec, 0, 0);
            b[o] = 92;
            b[o + 1] = 34;
            I = i;
            O = o + 2;
            t = rest(rline, nrec, -1);
            i = I;
            o = O;
            break;
          }
          if (i >= lim) {
            st = 1;
            break rec;
          }
          d = a[i + 1];
          if (d === 34) {
            if (a[i + 2] === 92 && a[i + 3] === 34) {
              b[o] = 92;
              b[o + 1] = 34;
              o += 2;
              i += 4;
              continue;
            }
            // the closing quote
            i += 2;
            c = a[i];
            if (c === 44) {
              i++;
              t = 1;
              break;
            }
            if (c === 92) {
              if (i >= lim) {
                st = 1;
                break rec;
              }
              d = a[i + 1];
              if (d === 110) {
                i += 2;
                t = 2;
                break;
              }
              if (d === 114 && a[i + 2] === 92 && a[i + 3] === 110) {
                i += 4;
                t = 2;
                break;
              }
            } else if (c === 34) {
              if (i >= end) {
                st = 1;
                break rec;
              }
              t = 3;
              break;
            }
            I = i;
            O = o;
            t = rest(rline, nrec, o);
            i = I;
            o = O;
            break;
          }
          if (d === 110) {
            b[o] = 92;
            b[o + 1] = 110;
            o += 2;
            i += 2;
            line++;
            continue;
          }
          if (d === 114) {
            b[o] = 92;
            b[o + 1] = 110;
            o += 2;
            i += a[i + 2] === 92 && a[i + 3] === 110 ? 4 : 2;
            line++;
            continue;
          }
          st = 2;
          break rec;
        }
      } else {
        while (stop[c] === 0) {
          b[o++] = c;
          c = a[++i];
        }
        if (c === 44) {
          i++;
          t = 1;
        } else if (c === 92) {
          if (i >= lim) {
            st = 1;
            break rec;
          }
          d = a[i + 1];
          if (d === 110) {
            i += 2;
            t = 2;
          } else if (d === 114 && a[i + 2] === 92 && a[i + 3] === 110) {
            i += 4;
            t = 2;
          } else {
            I = i;
            O = o;
            t = rest(rline, nrec, -1);
            i = I;
            o = O;
          }
        } else {
          if (i >= end) {
            st = 1;
            break rec;
          }
          t = 3;
        }
      }
      if (t !== 1) break;
      b[o] = 34;
      b[o + 1] = 44;
      b[o + 2] = 34;
      o += 3;
      nf++;
    }
    if (t > 3) {
      st = t - 3;
      break;
    }
    b[o++] = 34;
    if (t === 2) line++;
    if (nf + 1 === width && nf !== 0) {
      b[o] = 93;
      b[o + 1] = 44;
      o += 2;
      nrec++;
      continue;
    }
    O = o;
    NREC = nrec;
    WIDTH = width;
    odd(nf, ri, ro, rline);
    o = O;
    nrec = NREC;
    width = WIDTH;
    if (OUT !== b) {
      st = 3;
      break;
    }
  }

  if (st === 0 || st === 3) {
    I = i;
    O = o;
    LINE = line;
  } else {
    I = ri;
    O = ro;
    LINE = rline;
    NERR = rnerr;
    NEXT = rnext;
  }
  NREC = nrec;
  WIDTH = width;
  return st;
}

/** Whether INP holds `s` at I; moves past it when it does. */
function match(s) {
  const n = s.length;
  for (let k = 0; k < n; k++) if (INP[I + k] !== s.charCodeAt(k)) return false;
  I += n;
  return true;
}

/** At least n bytes in the window from I on, or all the file has left. */
function ensure(n) {
  while (END - I < n && refill(I));
}

/** Writes `s` (ASCII) over the output at file offset `at`, written out already or not. */
function patch(at, s) {
  for (let k = 0; k < s.length; k++) {
    const p = at + k - FLUSHED;
    if (p >= 0) OUT[p] = s.charCodeAt(k);
  }
  if (at < FLUSHED && OFD >= 0) {
    const n = Math.min(s.length, FLUSHED - at);
    writeSync(OFD, Buffer.from(s.slice(0, n), 'latin1'), 0, n, at);
  }
}

/** Appends `s` (ASCII) to the output. */
function put(s) {
  const n = s.length;
  room(n);
  for (let k = 0; k < n; k++) OUT[O + k] = s.charCodeAt(k);
  O += n;
}

/**
 * The byte reader over the whole input, through a window of `cap` bytes at first. False when it met something it
 * does not read (nothing it wrote counts then).
 */
function transduce(cap) {
  CAP = cap;
  HIGH = cap;
  INP = new Uint8Array(CAP + 16);
  OUT = new Uint8Array(HIGH + 3 * CAP + 64);
  ERR = new Int32Array(5 * 4096);
  EXT = new Uint8Array(1 << 16);
  END = 0;
  EOF = false;
  I = 0;
  O = 0;
  FLUSHED = 0;
  refill(0);
  ensure(2);
  if (INP[I] !== 91) return false;
  I++;
  OUT[O++] = 91;
  if (INP[I] === 93) {
    I++;
  } else {
    for (;;) {
      ensure(128);
      if (!match('{"id":"')) return false;
      for (;;) {
        const c = INP[I];
        if (c === 34) break;
        if (c === 92 || c < 32) return false;
        I++;
      }
      if (I >= END) return false;
      I++;
      if (!match(',"input":{"text":"')) return false;
      ensure(8);
      if (INP[I] === 0xef && INP[I + 1] === 0xbb && INP[I + 2] === 0xbf) I += 3;

      const opened = FLUSHED + O;
      put(OPEN_HEADER);
      LINE = 1;
      NREC = 0;
      WIDTH = -1;
      NERR = 0;
      NEXT = 0;
      for (;;) {
        const st = readText();
        if (st === 0) break;
        if (st === 2) return false;
        if (st === 1 && !refill(I)) return false;
      }

      ensure(24);
      if (!match(',"header":')) return false;
      let header;
      if (match('true}}')) header = true;
      else if (match('false}}')) header = false;
      else return false;

      if (header) {
        if (NREC === 0) put('[],"rows":[]');
        else if (NREC === 1) put(']');
        else OUT[O - 1] = 93;
      } else {
        patch(opened, OPEN_PLAIN);
        if (NREC === 0) put(']');
        else if (NREC === 1) {
          patch(AFTER, '         ');
          put(']');
        } else {
          patch(AFTER, ',        ');
          OUT[O - 1] = 93;
        }
      }
      put(',"errors":[');
      for (let e = 0; e < NERR; e += 5) {
        const code = ERR[e];
        const k = ERR[e + 2];
        const row = header ? (k === 0 ? 'null' : String(k - 1)) : String(k);
        const s = (e > 0 ? ',{"code":"' : '{"code":"') + CODES[code] + '","line":' + ERR[e + 1] + ',"row":' + row;
        if (code === E_SHORT) put(s + ',"fields":' + ERR[e + 3] + '}');
        else if (code === E_LONG) {
          put(s + ',"extra":[');
          const at = ERR[e + 3];
          const len = ERR[e + 4];
          room(len + 2);
          OUT.set(EXT.subarray(at, at + len), O);
          O += len;
          OUT[O++] = 93;
          OUT[O++] = 125;
        } else put(s + '}');
      }
      put(']}');

      ensure(2);
      const c = INP[I++];
      if (c === 44) {
        put(',');
        continue;
      }
      if (c !== 93) return false;
      break;
    }
  }
  ensure(1);
  if (I < END || !EOF) return false;
  room(1);
  OUT[O++] = 93;
  if (OFD >= 0) {
    let done = 0;
    while (done < O) done += writeSync(OFD, OUT, done, O - done);
  }
  return true;
}

/** Made-up cases that between them take the reader through every branch it has. */
function primer() {
  const q = '\\"';
  const rows = [];
  for (let r = 0; r < 6; r++) {
    const eol = r % 3 === 0 ? '\\n' : '\\r\\n';
    rows.push(`${r},alpha beta,2020-01-0${r % 9},AB-12${r},${q}say ${q}${q}hi${q}${q}, you${q},x${eol}`);
    rows.push(`${r},gamma,${q}two${eol}lines\\rmore${q},CD-9,${q}plain${q},y${eol}`);
    if (r % 5 === 1) rows.push(`1,short${eol}`);
    if (r % 5 === 2) rows.push(`1,2,3,4,5,6,long,${q}lo,ng${q},er${eol}`);
    if (r % 5 === 3) rows.push(`1,a\\rb,${q}q${q}kg,${q}q${q}\\r,x${q}y,${q}z${q}${eol}${eol}\\r${eol}`);
    if (r % 5 === 4) rows.push(`${q}e${q}${eol}${q}${q},${q}${q}${eol}${q}f${q}`);
  }
  const body = rows.join('');
  const head = 'a,b,c,d,e,f\\n';
  const cases = [
    `{"id":"g-0001","input":{"text":"﻿${head}${body}","header":true}}`,
    `{"id":"g-0002","input":{"text":"${body}\\n${q}open,1,2\\n3,4","header":false}}`,
    `{"id":"g-0003","input":{"text":"","header":true}}`,
    `{"id":"g-0004","input":{"text":"one\\n","header":false}}`,
    `{"id":"g-0005","input":{"text":"${head}${body}${q}never,closed${q}${q}","header":true}}`,
    `{"id":"g-0006","input":{"text":"\\r\\n\\r","header":false}}`,
  ];
  return Buffer.from('[' + cases.join(',') + ']', 'utf8');
}

let PRIMED = false;

/**
 * V8's flags for this program (the rules allow an entry to tune them): every function keeps its type feedback from
 * its first call, so the primer's one pass is enough; only readText is ever compiled by the optimizing compiler,
 * with nothing inlined into it (a helper's branch the primer cannot take, such as a real write, would otherwise
 * undo the compiled code when the file takes it).
 */
const FLAGS = ['--no-lazy-feedback-allocation', '--turbo-filter=readText', '--no-turbo-inlining', '--allow-natives-syntax'];

/** Runs the reader over the primer, then has V8 compile readText before its next call. */
function prime() {
  PRIMED = true;
  const { setFlagsFromString } = require('node:v8');
  for (const f of FLAGS) setFlagsFromString(f);
  IFD = -1;
  OFD = -1;
  SRC = primer();
  SRCPOS = 0;
  transduce(64);
  SRC = null;
  try {
    new Function('f', '%OptimizeFunctionOnNextCall(f)')(readText);
  } catch {
    // no such syntax in this V8: readText is compiled when V8 finds it hot
  }
}

/** Answers every case of the file at inPath into outPath. True when the byte reader did, false when run() had to. */
function answerFile(inPath, outPath, cap = 1 << 18) {
  let ok = false;
  try {
    if (!PRIMED) prime();
    IFD = openSync(inPath, 'r');
    OFD = openSync(outPath, 'w');
    ok = transduce(cap);
  } catch {
    ok = false;
  }
  if (IFD >= 0) closeSync(IFD);
  if (OFD >= 0) closeSync(OFD);
  IFD = -1;
  OFD = -1;
  if (ok) return true;
  // the plain way: every case answered alone by solve.js's run()
  const { run } = require('./solve.js');
  const cases = JSON.parse(readFileSync(inPath, 'utf8'));
  const answers = [];
  for (const c of cases) answers.push(run(c.input));
  writeFileSync(outPath, JSON.stringify(answers));
  return false;
}

/** The program: /input/cases.json to /output/answers.json (MAKEFUN_INPUT_DIR and MAKEFUN_OUTPUT_DIR stand in). */
function main() {
  answerFile((process.env.MAKEFUN_INPUT_DIR ?? '/input') + '/cases.json', (process.env.MAKEFUN_OUTPUT_DIR ?? '/output') + '/answers.json');
}

module.exports = { answerFile, main };
