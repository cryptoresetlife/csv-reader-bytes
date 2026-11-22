// The byte reader: answers a whole cases.json without ever building the cases as JavaScript values.
//
// The file is read through a small window as bytes, and each case's answer is written as JSON bytes while its text
// is still JSON-escaped. A CSV quote is the two bytes \" there, a line feed \n, a carriage return \r, and every other
// byte of a field is copied as it stands, so no string is ever decoded or encoded. Anything this reader does not
// expect (another escape, another layout of the file, a record or an error list too large for its fixed memory)
// sends the whole file to solve.js's run() instead, the plain drop-in, so the answer is the same either way.
//
// The reading itself is Records below, written in the asm.js subset of JavaScript: whole numbers and one ArrayBuffer,
// nothing else. It is ordinary JavaScript and runs as such anywhere; an engine that knows the subset (V8 does)
// compiles it ahead of its first call, with no warm-up and no type guessing to undo. The rest of this file is the
// driver around it: the window, the files, each case's opening and closing bytes and its list of errors.
//
// Plain JavaScript source, no dependency, nothing kept from one case to the next. CommonJS, since that is what Node
// starts fastest.

const { openSync, closeSync, readSync, writeSync, readFileSync, writeFileSync } = require('node:fs');

// The one ArrayBuffer (4 MiB), by byte offset:
//        0  sixteen 32-bit numbers, the reader's state (the S_ indexes below)
//       64  the ready-made texts of an error (TEXTS): for each, where it is and how long, then the texts
//   IB      the input window: at most MAXCAP bytes of the file and 16 of guard
//   OB      the output not yet written: HIGH bytes before it is written out, and room for one window's records
//   EB      the case's errors, five 32-bit numbers each: code, line, record count, and two more for a short row's
//           fields or a long row's cut fields (where they are kept, and how many bytes)
//   XB      the case's long rows' cut fields, as the JSON they were written as
const HEAP_BYTES = 1 << 22;
const TB = 64;
const IB = 512;
const MAXCAP = 1 << 18;
const OB = 1 << 19;
const OEND = OB + MAXCAP + 3 * MAXCAP + 64;
const EB = 1 << 21;
const XB = 3 << 20;

const S_I = 0; // the next input byte
const S_O = 1; // the next output byte
const S_END = 2; // the window holds the bytes before END
const S_LIM = 3; // an escape at or past LIM may be cut by the window's end
const S_LINE = 4;
const S_NREC = 5; // the case's records so far
const S_WIDTH = 6;
const S_NERR = 7; // the 32-bit numbers the case's errors take so far
const S_NEXT = 8; // the bytes the case's cut fields take so far
const S_HIGH = 9; // the output is written out once it passes HIGH
const S_OEND = 10; // where the output's room ends
const S_BAD = 11; // set when the fixed memory is too small for the case: run() answers the file

/**
 * The records of a case's text, read from the window and written as JSON arrays. stdlib is the global object,
 * foreign the two functions it calls out to, heap the ArrayBuffer above.
 */
function Records(stdlib, foreign, heap) {
  'use asm';
  var H8 = new stdlib.Uint8Array(heap);
  var H32 = new stdlib.Int32Array(heap);
  var flush = foreign.flush; // writes the output out up to an offset; the offset to go on from
  var first = foreign.first; // told where the case's first record ends

  // One more error: its code (0 stray_cr, 1 quote_junk, 2 unterminated_quote, 3 short_row, 4 long_row), the line
  // its record starts on, the records before it, and two numbers more.
  function pushErr(code, line, k, a, b) {
    code = code | 0;
    line = line | 0;
    k = k | 0;
    a = a | 0;
    b = b | 0;
    var n = 0;
    var p = 0;
    n = H32[7] | 0;
    if ((n | 0) > 262000) {
      H32[11] = 1;
      return;
    }
    p = (2097152 + (n << 2)) | 0;
    H32[p >> 2] = code;
    H32[(p + 4) >> 2] = line;
    H32[(p + 8) >> 2] = k;
    H32[(p + 12) >> 2] = a;
    H32[(p + 16) >> 2] = b;
    H32[7] = (n + 5) | 0;
  }

  // The rest of an unquoted field, with everything rare in it: a stray CR, a literal quote, and from the output
  // offset `junk` on (when it is not below 0) the characters after a closing quote. How it ended: 1 at a comma,
  // 2 at a line break (both read), 3 at the text's end (not read), 4 at the window's end, 5 at a byte this reader
  // does not read.
  function rest(recLine, k, junk) {
    recLine = recLine | 0;
    k = k | 0;
    junk = junk | 0;
    var i = 0;
    var o = 0;
    var t = 0;
    var c = 0;
    var d = 0;
    var end = 0;
    var lim = 0;
    i = H32[0] | 0;
    o = H32[1] | 0;
    end = H32[2] | 0;
    lim = H32[3] | 0;
    for (;;) {
      c = H8[i >> 0] | 0;
      if ((c | 0) == 44) {
        i = (i + 1) | 0;
        t = 1;
        break;
      }
      if ((c | 0) == 92) {
        if ((i | 0) >= (lim | 0)) {
          t = 4;
          break;
        }
        d = H8[(i + 1) >> 0] | 0;
        if ((d | 0) == 110) {
          i = (i + 2) | 0;
          t = 2;
          break;
        }
        if ((d | 0) == 114) {
          if (((H8[(i + 2) >> 0] | 0) == 92) & ((H8[(i + 3) >> 0] | 0) == 110)) {
            i = (i + 4) | 0;
            t = 2;
            break;
          }
          pushErr(0, recLine, k, 0, 0);
          i = (i + 2) | 0;
          continue;
        }
        if ((d | 0) == 34) {
          H8[o >> 0] = 92;
          H8[(o + 1) >> 0] = 34;
          o = (o + 2) | 0;
          i = (i + 2) | 0;
          continue;
        }
        t = 5;
        break;
      }
      if ((c | 0) == 34) {
        if ((i | 0) >= (end | 0)) t = 4;
        else t = 3;
        break;
      }
      H8[o >> 0] = c;
      o = (o + 1) | 0;
      i = (i + 1) | 0;
    }
    if ((t | 0) < 4) {
      if ((junk | 0) >= 0) {
        if ((o | 0) > (junk | 0)) pushErr(1, recLine, k, 0, 0);
      }
    }
    H32[0] = i;
    H32[1] = o;
    return t | 0;
  }

  // The end of a record that is not a row of the case's width with two fields or more: the first record, a short
  // or a long row, a record of one field, a line with no characters or with stray CRs alone, the text's end. The
  // output holds it from `ro` as [ "..." , "..." with its last quote written; `ri` is where it began in the window.
  function odd(nf, ri, ro, recLine) {
    nf = nf | 0;
    ri = ri | 0;
    ro = ro | 0;
    recLine = recLine | 0;
    var o = 0;
    var total = 0;
    var width = 0;
    var nrec = 0;
    var k = 0;
    var p = 0;
    var c = 0;
    var len = 0;
    var nx = 0;
    var q = 0;
    var pad = 0;
    o = H32[1] | 0;
    nrec = H32[5] | 0;
    width = H32[6] | 0;
    total = (nf + 1) | 0;
    if (((nf | 0) == 0) & ((o | 0) == ((ro + 3) | 0))) {
      if (!(((H8[ri >> 0] | 0) == 92) & ((H8[(ri + 1) >> 0] | 0) == 34))) {
        H32[1] = ro; // no characters and no quotes: no record
        return;
      }
    }
    if ((width | 0) < 0) {
      H32[6] = total;
      H32[5] = 1;
      H8[o >> 0] = 93;
      o = (o + 1) | 0;
      first(o | 0);
      // ,"rows":[
      H8[o >> 0] = 44;
      H8[(o + 1) >> 0] = 34;
      H8[(o + 2) >> 0] = 114;
      H8[(o + 3) >> 0] = 111;
      H8[(o + 4) >> 0] = 119;
      H8[(o + 5) >> 0] = 115;
      H8[(o + 6) >> 0] = 34;
      H8[(o + 7) >> 0] = 58;
      H8[(o + 8) >> 0] = 91;
      H32[1] = (o + 9) | 0;
      return;
    }
    if ((total | 0) < (width | 0)) {
      pushErr(3, recLine, nrec, total, 0);
      if ((width | 0) > 300000) {
        H32[11] = 1;
        return;
      }
      pad = (((width - total) | 0) * 3) | 0;
      if (((o + pad + 8) | 0) > (H32[10] | 0)) {
        o = flush(o | 0) | 0;
        if (((o + pad + 8) | 0) > (H32[10] | 0)) {
          H32[11] = 1;
          H32[1] = o;
          return;
        }
      }
      for (k = total; (k | 0) < (width | 0); k = (k + 1) | 0) {
        H8[o >> 0] = 44;
        H8[(o + 1) >> 0] = 34;
        H8[(o + 2) >> 0] = 34;
        o = (o + 3) | 0;
      }
    } else if ((total | 0) > (width | 0)) {
      // the comma after the last field kept: `width` strings on from the record's first quote
      p = (ro + 1) | 0;
      for (k = 0; (k | 0) < (width | 0); k = (k + 1) | 0) {
        p = (p + 1) | 0;
        for (;;) {
          c = H8[p >> 0] | 0;
          if ((c | 0) == 34) break;
          if ((c | 0) == 92) p = (p + 2) | 0;
          else p = (p + 1) | 0;
        }
        p = (p + 2) | 0;
      }
      p = (p - 1) | 0;
      len = (o - p - 1) | 0;
      nx = H32[8] | 0;
      if ((len | 0) > ((1048576 - nx) | 0)) {
        H32[11] = 1;
        return;
      }
      q = (3145728 + nx) | 0;
      for (k = 0; (k | 0) < (len | 0); k = (k + 1) | 0) H8[(q + k) >> 0] = H8[(p + 1 + k) >> 0] | 0;
      pushErr(4, recLine, nrec, nx, len);
      H32[8] = (nx + len) | 0;
      o = p;
    }
    H8[o >> 0] = 93;
    H8[(o + 1) >> 0] = 44;
    H32[1] = (o + 2) | 0;
    H32[5] = (nrec + 1) | 0;
  }

  // Reads the text's records from the window on, writing each as a JSON array. 0: the text ended (the next input
  // byte is past its closing quote); 1: the window ended inside a record (the next input byte is back at the
  // record's start, and nothing of the record is kept); 2: this reader does not read the file.
  function readText() {
    var i = 0;
    var o = 0;
    var end = 0;
    var lim = 0;
    var high = 0;
    var line = 0;
    var nrec = 0;
    var width = 0;
    var st = 0;
    var ri = 0;
    var ro = 0;
    var rline = 0;
    var rnerr = 0;
    var rnext = 0;
    var c = 0;
    var d = 0;
    var nf = 0;
    var t = 0;
    var qi = 0;
    var qo = 0;
    var qline = 0;
    i = H32[0] | 0;
    o = H32[1] | 0;
    end = H32[2] | 0;
    lim = H32[3] | 0;
    line = H32[4] | 0;
    nrec = H32[5] | 0;
    width = H32[6] | 0;
    high = H32[9] | 0;

    rec: for (;;) {
      // a record starts here: what a window's end takes the reader back to
      if ((o | 0) > (high | 0)) o = flush(o | 0) | 0;
      ri = i;
      ro = o;
      rline = line;
      rnerr = H32[7] | 0;
      rnext = H32[8] | 0;
      H8[o >> 0] = 91;
      H8[(o + 1) >> 0] = 34;
      o = (o + 2) | 0;
      nf = 0;
      for (;;) {
        // plain bytes up to a comma, a backslash or the quote that ends the text
        c = H8[i >> 0] | 0;
        while (((c | 0) != 44) & ((c | 0) != 92) & ((c | 0) != 34)) {
          H8[o >> 0] = c;
          o = (o + 1) | 0;
          i = (i + 1) | 0;
          c = H8[i >> 0] | 0;
        }
        if ((c | 0) == 44) {
          H8[o >> 0] = 34;
          H8[(o + 1) >> 0] = 44;
          H8[(o + 2) >> 0] = 34;
          o = (o + 3) | 0;
          i = (i + 1) | 0;
          nf = (nf + 1) | 0;
          continue;
        }
        if ((c | 0) == 34) {
          if ((i | 0) >= (end | 0)) {
            st = 1;
            break rec;
          }
          t = 3;
          break;
        }
        if ((i | 0) >= (lim | 0)) {
          st = 1;
          break rec;
        }
        d = H8[(i + 1) >> 0] | 0;
        if ((d | 0) == 110) {
          i = (i + 2) | 0;
          t = 2;
          break;
        }
        if (((d | 0) == 114) & ((H8[(i + 2) >> 0] | 0) == 92) & ((H8[(i + 3) >> 0] | 0) == 110)) {
          i = (i + 4) | 0;
          t = 2;
          break;
        }
        if (((d | 0) == 34) & (((i | 0) == (ri | 0)) | ((H8[(i - 1) >> 0] | 0) == 44))) {
          // a quote where a field starts: a quoted field, copied up to a backslash or a quote
          qi = i;
          qo = o;
          qline = line;
          i = (i + 2) | 0;
          for (;;) {
            c = H8[i >> 0] | 0;
            while (((c | 0) != 92) & ((c | 0) != 34)) {
              H8[o >> 0] = c;
              o = (o + 1) | 0;
              i = (i + 1) | 0;
              c = H8[i >> 0] | 0;
            }
            if ((c | 0) == 34) {
              if ((i | 0) >= (end | 0)) {
                st = 1;
                break rec;
              }
              // the text ends inside the quotes: the quote is a character, and the field is read again from it
              line = qline;
              pushErr(2, rline, nrec, 0, 0);
              H8[qo >> 0] = 92;
              H8[(qo + 1) >> 0] = 34;
              H32[0] = (qi + 2) | 0;
              H32[1] = (qo + 2) | 0;
              t = rest(rline, nrec, -1) | 0;
              i = H32[0] | 0;
              o = H32[1] | 0;
              break;
            }
            if ((i | 0) >= (lim | 0)) {
              st = 1;
              break rec;
            }
            d = H8[(i + 1) >> 0] | 0;
            if ((d | 0) == 34) {
              if (((H8[(i + 2) >> 0] | 0) == 92) & ((H8[(i + 3) >> 0] | 0) == 34)) {
                H8[o >> 0] = 92;
                H8[(o + 1) >> 0] = 34;
                o = (o + 2) | 0;
                i = (i + 4) | 0;
                continue;
              }
              // the closing quote
              i = (i + 2) | 0;
              c = H8[i >> 0] | 0;
              if ((c | 0) == 44) {
                i = (i + 1) | 0;
                t = 1;
                break;
              }
              if ((c | 0) == 92) {
                if ((i | 0) >= (lim | 0)) {
                  st = 1;
                  break rec;
                }
                d = H8[(i + 1) >> 0] | 0;
                if ((d | 0) == 110) {
                  i = (i + 2) | 0;
                  t = 2;
                  break;
                }
                if (((d | 0) == 114) & ((H8[(i + 2) >> 0] | 0) == 92) & ((H8[(i + 3) >> 0] | 0) == 110)) {
                  i = (i + 4) | 0;
                  t = 2;
                  break;
                }
              } else if ((c | 0) == 34) {
                if ((i | 0) >= (end | 0)) {
                  st = 1;
                  break rec;
                }
                t = 3;
                break;
              }
              H32[0] = i;
              H32[1] = o;
              t = rest(rline, nrec, o) | 0;
              i = H32[0] | 0;
              o = H32[1] | 0;
              break;
            }
            if ((d | 0) == 110) {
              H8[o >> 0] = 92;
              H8[(o + 1) >> 0] = 110;
              o = (o + 2) | 0;
              i = (i + 2) | 0;
              line = (line + 1) | 0;
              continue;
            }
            if ((d | 0) == 114) {
              H8[o >> 0] = 92;
              H8[(o + 1) >> 0] = 110;
              o = (o + 2) | 0;
              if (((H8[(i + 2) >> 0] | 0) == 92) & ((H8[(i + 3) >> 0] | 0) == 110)) i = (i + 4) | 0;
              else i = (i + 2) | 0;
              line = (line + 1) | 0;
              continue;
            }
            st = 2;
            break rec;
          }
        } else {
          // a stray CR, a quote inside a field, or a byte this reader does not read
          H32[0] = i;
          H32[1] = o;
          t = rest(rline, nrec, -1) | 0;
          i = H32[0] | 0;
          o = H32[1] | 0;
        }
        if ((t | 0) != 1) break;
        H8[o >> 0] = 34;
        H8[(o + 1) >> 0] = 44;
        H8[(o + 2) >> 0] = 34;
        o = (o + 3) | 0;
        nf = (nf + 1) | 0;
      }
      if ((t | 0) > 3) {
        st = (t - 3) | 0;
        break;
      }
      H8[o >> 0] = 34;
      o = (o + 1) | 0;
      if ((t | 0) == 2) line = (line + 1) | 0;
      if ((((nf + 1) | 0) == (width | 0)) & ((nf | 0) != 0)) {
        H8[o >> 0] = 93;
        H8[(o + 1) >> 0] = 44;
        o = (o + 2) | 0;
        nrec = (nrec + 1) | 0;
      } else {
        H32[1] = o;
        H32[5] = nrec;
        H32[6] = width;
        odd(nf, ri, ro, rline);
        o = H32[1] | 0;
        nrec = H32[5] | 0;
        width = H32[6] | 0;
      }
      if (H32[11] | 0) {
        st = 2;
        break;
      }
      if ((t | 0) == 3) {
        i = (i + 1) | 0; // the quote that ends the text
        break;
      }
    }

    if ((st | 0) == 0) {
      H32[0] = i;
      H32[1] = o;
      H32[4] = line;
    } else {
      H32[0] = ri;
      H32[1] = ro;
      H32[4] = rline;
      H32[7] = rnerr;
      H32[8] = rnext;
    }
    H32[5] = nrec;
    H32[6] = width;
    return st | 0;
  }

  // Writes v, a whole number of 0 or more, in decimal at output offset o; the offset after it.
  function num(v, o) {
    v = v | 0;
    o = o | 0;
    var n = 0;
    var p = 0;
    var q = 0;
    if ((v | 0) < 10) {
      H8[o >> 0] = (48 + v) | 0;
      return (o + 1) | 0;
    }
    n = 2;
    p = 100;
    while ((p | 0) <= (v | 0)) {
      n = (n + 1) | 0;
      if ((n | 0) == 10) break;
      p = (p * 10) | 0;
    }
    for (q = (o + n - 1) | 0; (q | 0) >= (o | 0); q = (q - 1) | 0) {
      H8[q >> 0] = (48 + ((v | 0) % 10)) | 0;
      v = ((v | 0) / 10) | 0;
    }
    return (o + n) | 0;
  }

  // Copies ready-made text number t (the table at byte 64: where it is and how long) to output offset o; the
  // offset after it.
  function text(o, t) {
    o = o | 0;
    t = t | 0;
    var p = 0;
    var n = 0;
    var k = 0;
    p = H32[(64 + (t << 3)) >> 2] | 0;
    n = H32[(68 + (t << 3)) >> 2] | 0;
    for (k = 0; (k | 0) < (n | 0); k = (k + 1) | 0) H8[(o + k) >> 0] = H8[(p + k) >> 0] | 0;
    return (o + n) | 0;
  }

  // Writes the case's errors as a JSON array: each from its code's ready-made opening (texts 0 to 4), its numbers
  // digit by digit, a long row's cut fields as they were kept. `header` is 1 when the case's header is true: a
  // record's row is then one less than the records before it, and null for the first.
  function putErrors(header) {
    header = header | 0;
    var o = 0;
    var e = 0;
    var count = 0;
    var at = 0;
    var code = 0;
    var k = 0;
    var oend = 0;
    var from = 0;
    var len = 0;
    var j = 0;
    o = H32[1] | 0;
    count = H32[7] | 0;
    oend = H32[10] | 0;
    if ((count | 0) == 0) {
      H8[o >> 0] = 91;
      o = (o + 1) | 0;
    }
    for (e = 0; (e | 0) < (count | 0); e = (e + 5) | 0) {
      at = (2097152 + (e << 2)) | 0;
      code = H32[at >> 2] | 0;
      k = H32[(at + 8) >> 2] | 0;
      if (((o + 128) | 0) > (oend | 0)) o = flush(o | 0) | 0;
      j = o;
      o = text(o, code) | 0;
      if ((e | 0) == 0) H8[j >> 0] = 91; // the list's [ where a later error has its comma
      o = num(H32[(at + 4) >> 2] | 0, o) | 0;
      o = text(o, 5) | 0;
      if ((header | 0) == 0) o = num(k, o) | 0;
      else if ((k | 0) > 0) o = num((k - 1) | 0, o) | 0;
      else o = text(o, 6) | 0;
      if ((code | 0) == 3) {
        o = text(o, 7) | 0;
        o = num(H32[(at + 12) >> 2] | 0, o) | 0;
      } else if ((code | 0) == 4) {
        o = text(o, 8) | 0;
        from = (3145728 + (H32[(at + 12) >> 2] | 0)) | 0;
        len = H32[(at + 16) >> 2] | 0;
        if (((o + len + 8) | 0) > (oend | 0)) {
          o = flush(o | 0) | 0;
          if (((o + len + 8) | 0) > (oend | 0)) {
            H32[11] = 1;
            break;
          }
        }
        for (j = 0; (j | 0) < (len | 0); j = (j + 1) | 0) H8[(o + j) >> 0] = H8[(from + j) >> 0] | 0;
        o = (o + len) | 0;
        H8[o >> 0] = 93;
        o = (o + 1) | 0;
      }
      H8[o >> 0] = 125;
      o = (o + 1) | 0;
    }
    H8[o >> 0] = 93;
    H32[1] = (o + 1) | 0;
  }

  return { readText: readText, putErrors: putErrors };
}

/** The output a case opens with when its header is true (24 bytes), and its form when it is false. */
const OPEN_HEADER = '{"columns":             ';
const OPEN_PLAIN = '{"columns":null,"rows":[';

/**
 * The ready-made texts of an error, by number: how each code's error opens (a comma, which the first error's [
 * replaces, and up to its line), then what stands before its row, a null row, a short row's fields and a long row's
 * cut fields.
 */
const TEXTS = [
  ',{"code":"stray_cr","line":',
  ',{"code":"quote_junk","line":',
  ',{"code":"unterminated_quote","line":',
  ',{"code":"short_row","line":',
  ',{"code":"long_row","line":',
  ',"row":',
  'null',
  ',"fields":',
  ',"extra":[',
];

let IFD = -1; // the input and output files
let OFD = -1;
let H = null; // the ArrayBuffer as bytes (a Buffer, for Node's own copies) and as 32-bit numbers
let S = null;
let READ = null; // Records' readText and putErrors over it
let ERRORS = null;
let CAP = 0; // the window's size now
let EOF = false;
let FLUSHED = 0; // the file offset of the output's first byte in memory
let AFTER = 0; // the file offset of what follows the case's first record

/** Writes the output out up to offset o, but for its last byte, which a case's end may still change. */
function flush(o) {
  const n = o - 1 - OB;
  let done = 0;
  while (done < n) done += writeSync(OFD, H, OB + done, n - done);
  H[OB] = H[o - 1];
  FLUSHED += n;
  return OB + 1;
}

/** The case's first record ends at output offset o. */
function first(o) {
  AFTER = FLUSHED + (o - OB);
}

/** Room for n more output bytes. */
function room(n) {
  if (S[S_O] + n <= OEND) return;
  S[S_O] = flush(S[S_O]);
  if (S[S_O] + n > OEND) throw new RangeError('no room');
}

/** Moves the window's bytes from `keep` on to its start and reads on. False when there is nothing more to read. */
function refill(keep) {
  if (EOF) return false;
  const tail = S[S_END] - keep;
  if (keep > IB) {
    H.copyWithin(IB, keep, S[S_END]);
    S[S_I] -= keep - IB;
  }
  if (tail === CAP) {
    if (CAP === MAXCAP) return false; // one record wider than the widest window: run() answers the file
    CAP = Math.min(CAP * 2, MAXCAP);
  }
  const n = readSync(IFD, H, IB + tail, CAP - tail, null);
  if (n === 0) EOF = true;
  const end = IB + tail + n;
  S[S_END] = end;
  S[S_LIM] = EOF ? end : end - 8;
  H.fill(34, end, end + 16);
  return true;
}

/** Whether the window holds `s` at the next input byte; moves past it when it does. */
function match(s) {
  const n = s.length;
  const i = S[S_I];
  for (let k = 0; k < n; k++) if (H[i + k] !== s.charCodeAt(k)) return false;
  S[S_I] = i + n;
  return true;
}

/** At least n bytes in the window from the next input byte on, or all the file has left. */
function ensure(n) {
  while (S[S_END] - S[S_I] < n && refill(S[S_I]));
}

/** Writes `s` (ASCII) over the output at file offset `at`, written out already or not. */
function patch(at, s) {
  for (let k = 0; k < s.length; k++) {
    const p = at + k - FLUSHED;
    if (p >= 0) H[OB + p] = s.charCodeAt(k);
  }
  if (at < FLUSHED) {
    const n = Math.min(s.length, FLUSHED - at);
    writeSync(OFD, Buffer.from(s.slice(0, n), 'latin1'), 0, n, at);
  }
}

/** Appends `s` (ASCII) to the output. */
function put(s) {
  const n = s.length;
  room(n);
  const o = S[S_O];
  for (let k = 0; k < n; k++) H[o + k] = s.charCodeAt(k);
  S[S_O] = o + n;
}

/**
 * The byte reader over the whole input, through a window of `cap` bytes at first. False when it met something it
 * does not read (nothing it wrote counts then).
 */
function transduce(cap) {
  if (H === null) {
    const heap = new ArrayBuffer(HEAP_BYTES);
    H = Buffer.from(heap);
    S = new Int32Array(heap);
    let at = TB + 8 * TEXTS.length;
    for (let t = 0; t < TEXTS.length; t++) {
      S[(TB >> 2) + 2 * t] = at;
      S[(TB >> 2) + 2 * t + 1] = TEXTS[t].length;
      at += H.latin1Write(TEXTS[t], at);
    }
    const records = Records(globalThis, { flush, first }, heap);
    READ = records.readText;
    ERRORS = records.putErrors;
  }
  CAP = Math.min(cap, MAXCAP);
  EOF = false;
  FLUSHED = 0;
  S[S_I] = IB;
  S[S_END] = IB;
  S[S_O] = OB;
  S[S_HIGH] = OB + CAP;
  S[S_OEND] = OEND;
  S[S_BAD] = 0;
  refill(IB);
  ensure(2);
  if (H[S[S_I]] !== 91) return false;
  S[S_I]++;
  H[S[S_O]++] = 91;
  if (H[S[S_I]] === 93) {
    S[S_I]++;
  } else {
    for (;;) {
      ensure(128);
      if (!match('{"id":"')) return false;
      let i = S[S_I];
      for (;;) {
        const c = H[i];
        if (c === 34) break;
        if (c === 92 || c < 32) return false;
        i++;
      }
      if (i >= S[S_END]) return false;
      S[S_I] = i + 1;
      if (!match(',"input":{"text":"')) return false;
      ensure(8);
      i = S[S_I];
      if (H[i] === 0xef && H[i + 1] === 0xbb && H[i + 2] === 0xbf) S[S_I] = i + 3;

      const opened = FLUSHED + (S[S_O] - OB);
      put(OPEN_HEADER);
      S[S_LINE] = 1;
      S[S_NREC] = 0;
      S[S_WIDTH] = -1;
      S[S_NERR] = 0;
      S[S_NEXT] = 0;
      for (;;) {
        const st = READ();
        if (st === 0) break;
        if (st === 2) return false;
        if (!refill(S[S_I])) return false;
      }

      ensure(24);
      if (!match(',"header":')) return false;
      let header;
      if (match('true}}')) header = true;
      else if (match('false}}')) header = false;
      else return false;

      const nrec = S[S_NREC];
      if (header) {
        if (nrec === 0) put('[],"rows":[]');
        else if (nrec === 1) put(']');
        else H[S[S_O] - 1] = 93;
      } else {
        patch(opened, OPEN_PLAIN);
        if (nrec === 0) put(']');
        else if (nrec === 1) {
          patch(AFTER, '         ');
          put(']');
        } else {
          patch(AFTER, ',        ');
          H[S[S_O] - 1] = 93;
        }
      }
      put(',"errors":');
      room(16);
      ERRORS(header ? 1 : 0);
      if (S[S_BAD] !== 0) return false;
      put('}');

      ensure(2);
      const c = H[S[S_I]++];
      if (c === 44) {
        put(',');
        continue;
      }
      if (c !== 93) return false;
      break;
    }
  }
  ensure(1);
  if (S[S_I] < S[S_END] || !EOF) return false;
  room(1);
  H[S[S_O]++] = 93;
  const n = S[S_O] - OB;
  let done = 0;
  while (done < n) done += writeSync(OFD, H, OB + done, n - done);
  return true;
}

/** Answers every case of the file at inPath into outPath. True when the byte reader did, false when run() had to. */
function answerFile(inPath, outPath, cap = MAXCAP, close = true) {
  let ok = false;
  IFD = -1;
  OFD = -1;
  try {
    IFD = openSync(inPath, 'r');
    OFD = openSync(outPath, 'w');
    ok = transduce(cap);
  } catch {
    ok = false;
  }
  if (ok && !close) return true; // the program's own run: the files close as it exits
  if (IFD >= 0) closeSync(IFD);
  if (OFD >= 0) closeSync(OFD);
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
  answerFile((process.env.MAKEFUN_INPUT_DIR ?? '/input') + '/cases.json', (process.env.MAKEFUN_OUTPUT_DIR ?? '/output') + '/answers.json', MAXCAP, false);
}

module.exports = { answerFile, main };
