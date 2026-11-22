// A drop-in for csv-reader 1.0.0: run(input) is the reading of one {text, header} as {columns, rows, errors}.
//
// It reads the text once, left to right, and takes each field as a slice of it (joined slices where a doubled quote,
// a quoted line break or a stray CR cuts one), never a character at a time. main.ts answers a whole cases.json with
// reader.cjs, which does the same reading on the file's bytes; whatever that reader does not expect is answered here.
//
// Pure: no clock, no randomness, nothing kept from one call to the next. No dependency.

export function run(input) {
  const text = String(input.text);
  const header = input.header === true;
  const n = text.length;
  const rows = [];
  const errors = [];
  let columns = null;
  let width = -1;
  let pos = n > 0 && text.charCodeAt(0) === 0xfeff ? 1 : 0;
  let line = 1;

  for (;;) {
    // lines with no characters
    for (;;) {
      const c = text.charCodeAt(pos);
      if (c === 10) {
        pos++;
        line++;
      } else if (c === 13 && text.charCodeAt(pos + 1) === 10) {
        pos += 2;
        line++;
      } else break;
    }
    if (pos >= n) break;

    const recLine = line;
    const recRow = header && columns === null ? null : rows.length;
    const fields = [];
    let quoted = false;
    let term = 1; // 1: a comma ended the field, 2: a line break, 3: the end of the text

    while (term === 1) {
      let value = '';
      let junkFrom = -1; // the length of the value when the characters after its closing quote begin
      term = 0;
      quoted = text.charCodeAt(pos) === 34;
      if (quoted) {
        const openLine = line;
        let p = pos + 1;
        let seg = p;
        let closed = false;
        while (p < n) {
          const c = text.charCodeAt(p);
          if (c === 34) {
            if (text.charCodeAt(p + 1) === 34) {
              value += text.slice(seg, p + 1);
              p += 2;
              seg = p;
              continue;
            }
            value += text.slice(seg, p);
            p++;
            closed = true;
            break;
          }
          if (c === 13) {
            value += text.slice(seg, p) + '\n';
            line++;
            p += text.charCodeAt(p + 1) === 10 ? 2 : 1;
            seg = p;
            continue;
          }
          if (c === 10) line++;
          p++;
        }
        if (closed) {
          pos = p;
          if (pos >= n) term = 3;
          else {
            const c = text.charCodeAt(pos);
            if (c === 44) {
              pos++;
              term = 1;
            } else if (c === 10) {
              pos++;
              line++;
              term = 2;
            } else if (c === 13 && text.charCodeAt(pos + 1) === 10) {
              pos += 2;
              line++;
              term = 2;
            } else junkFrom = value.length;
          }
        } else {
          // never closed: the quote is a character, and what follows it is read again
          pos += 1;
          line = openLine;
          errors.push({ code: 'unterminated_quote', line: recLine, row: recRow });
          value = '"';
        }
      }
      if (term === 0) {
        let seg = pos;
        term = 3;
        while (pos < n) {
          const c = text.charCodeAt(pos);
          if (c === 44) {
            value += text.slice(seg, pos);
            pos++;
            term = 1;
            break;
          }
          if (c === 10) {
            value += text.slice(seg, pos);
            pos++;
            line++;
            term = 2;
            break;
          }
          if (c === 13) {
            value += text.slice(seg, pos);
            if (text.charCodeAt(pos + 1) === 10) {
              pos += 2;
              line++;
              term = 2;
              break;
            }
            errors.push({ code: 'stray_cr', line: recLine, row: recRow });
            pos++;
            seg = pos;
            continue;
          }
          pos++;
        }
        if (term === 3) value += text.slice(seg, pos);
        if (junkFrom >= 0 && value.length > junkFrom) errors.push({ code: 'quote_junk', line: recLine, row: recRow });
      }
      fields.push(value);
    }

    if (fields.length === 1 && fields[0] === '' && !quoted) continue;
    if (width < 0) width = fields.length;
    if (header && columns === null) {
      columns = fields;
      continue;
    }
    if (fields.length < width) {
      errors.push({ code: 'short_row', line: recLine, row: recRow, fields: fields.length });
      while (fields.length < width) fields.push('');
    } else if (fields.length > width) {
      errors.push({ code: 'long_row', line: recLine, row: recRow, extra: fields.splice(width) });
    }
    rows.push(fields);
  }
  return { columns: header ? (columns ?? []) : null, rows, errors };
}
