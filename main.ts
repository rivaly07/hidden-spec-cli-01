
// main.ts - mend, the CLI SPEC.md specifies (version 1).
// Node 22, standard library only; run as: node main.ts [options] [PATCH]

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

class Exit2 {
  readonly line: string;
  constructor(line: string) { this.line = line; }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) { this.code = code; this.path = path; }
}

const blank = (s: string): boolean => s.trim() === '';
const BS_CHAR = String.fromCharCode(92);
const isBlankLine = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes(BS_CHAR) && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

interface Doc { lines: string[]; br: string; final: boolean; }

function toDoc(text: string): Doc {
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  if (text === '') return { lines: [], br, final: false };
  const raw = text.split(br);
  const final = raw.length > 0 && raw[raw.length - 1] === '';
  if (final) raw.pop();
  return { lines: raw, br, final };
}

function fromDoc(d: Doc): string {
  if (d.lines.length === 0) return '';
  return d.lines.join(d.br) + (d.final ? d.br : '');
}

class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { old: string; new: string }[] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try { if (statSync(p).isFile()) v = readFileSync(p, 'utf8'); }
      catch { v = null; }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  doc(p: string): Doc | null {
    const t = this.get(p);
    return t === null ? null : toDoc(t);
  }
}

type Edit = (tree: Tree, strict: boolean) => void;

// ---------- format detection (section 4) ----------
function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.replace(/[ \t]+$/, '') === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------- matching lines (section 5) ----------
function trimTier(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.trim();
}
function eqTier(a: string, b: string, tier: number): boolean {
  return trimTier(a, tier) === trimTier(b, tier);
}
function matchTier(file: string[], O: string[], maxTier: number): { tier: number; occ: number[] } {
  for (let t = 0; t <= maxTier; t++) {
    if (O.length === 0) return { tier: t, occ: [] };
    const occ: number[] = [];
    for (let i = 0; i + O.length <= file.length; i++) {
      let ok = true;
      for (let j = 0; j < O.length; j++) {
        if (!eqTier(file[i + j]!, O[j]!, t)) { ok = false; break; }
      }
      if (ok) occ.push(i);
    }
    if (occ.length > 0) return { tier: t, occ };
  }
  return { tier: maxTier, occ: [] };
}
function leading(s: string): string {
  const m = s.match(/^[ \t]*/);
  return m ? m[0] : '';
}

interface NEntry { text: string; ctx: number; }
function analyzeBody(body: string[]): { O: string[]; N: NEntry[] } {
  const O: string[] = [];
  const N: NEntry[] = [];
  let oIdx = 0;
  for (const b of body) {
    if (b.charCodeAt(0) === 92) continue; // skip backslash marker lines
    if (b === '') {
      O.push(''); N.push({ text: '', ctx: oIdx }); oIdx++;
    } else if (b.startsWith(' ')) {
      O.push(b.slice(1)); N.push({ text: b.slice(1), ctx: oIdx }); oIdx++;
    } else if (b.startsWith('-')) {
      O.push(b.slice(1)); oIdx++;
    } else if (b.startsWith('+')) {
      N.push({ text: b.slice(1), ctx: -1 });
    }
  }
  return { O, N };
}
function buildN(file: string[], O: string[], N: NEntry[], start: number, tier: number): string[] {
  const F = leading(file[start] ?? '');
  const P = O.length > 0 ? leading(O[0]!) : '';
  return N.map((e) => {
    if (e.ctx >= 0) return file[start + e.ctx]!;
    if (tier === 2) {
      if (e.text !== '' && e.text.trim() !== '' && e.text.startsWith(P)) return F + e.text.slice(P.length);
      return e.text;
    }
    return e.text;
  });
}
function hasNoFinalBreak(body: string[]): boolean {
  let lastIdx = -1;
  for (let k = 0; k < body.length; k++) {
    const b = body[k];
    if (b.charCodeAt(0) === 92) continue;
    if (b === '' || b.startsWith(' ') || b.startsWith('+')) lastIdx = k;
  }
  if (lastIdx < 0) return false;
  for (let k = lastIdx + 1; k < body.length; k++) if (body[k].charCodeAt(0) === 92) return true;
  return false;
}

// ---------- unified diffs (section 6) ----------
interface Hunk { A: number; body: string[]; }

function parseUnified(lines: string[]): Edit[] {
  const edits: Edit[] = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const r = parseUnifiedSection(lines, i); edits.push(r.edit); i = r.next;
    } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const r = parseUnifiedSection(lines, i); edits.push(r.edit); i = r.next;
    } else if (line.startsWith('@@')) {
      throw new Exit2(`error: parse ${i + 1}`);
    } else {
      i++;
    }
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}
function stripAB(p: string): string {
  return p.startsWith('a/') || p.startsWith('b/') ? p.slice(2) : p;
}
function parsePathLine(line: string): string {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p === '/dev/null') return '/dev/null';
  return stripAB(p);
}
function parseUnifiedSection(lines: string[], start: number): { edit: Edit; next: number } {
  let i = start;
  let oldPath: string | null = null;
  let newPath: string | null = null;
  let creation = false;
  let deletion = false;

  if (lines[i]!.startsWith('diff --git ')) {
    const rest = lines[i]!.slice('diff --git '.length).trim();
    const sp = rest.split(/[\s]+/);
    if (sp.length < 2) throw new Exit2(`error: parse ${i + 1}`);
    oldPath = stripAB(sp[0]!);
    newPath = stripAB(sp[1]!);
    i++;
    while (i < lines.length) {
      const l = lines[i]!;
      if (l.startsWith('--- ') || l.startsWith('+++ ') || l.startsWith('@@') || l.startsWith('diff --git ')) break;
      if (l.startsWith('rename from ')) oldPath = l.slice('rename from '.length).trim();
      else if (l.startsWith('rename to ')) newPath = l.slice('rename to '.length).trim();
      else if (/^new file mode\b/.test(l)) creation = true;
      else if (/^deleted file mode\b/.test(l)) deletion = true;
      i++;
    }
  }

  if (i < lines.length && lines[i]!.startsWith('--- ')) {
    if (!(lines[i + 1] ?? '').startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
    oldPath = parsePathLine(lines[i]!);
    newPath = parsePathLine(lines[i + 1]!);
    i += 2;
  }

  const hunks: Hunk[] = [];
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
    if (l.startsWith('@@')) {
      const m = l.match(/^@@ -(\d+)(?:,\d+)? \+\d+(?:,\d+)? @@/);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const A = parseInt(m[1]!, 10);
      i++;
      const body: string[] = [];
      while (i < lines.length) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (b.startsWith('@@')) break;
        if (b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b.charCodeAt(0) === 92) { body.push(b); i++; }
        else if (b === '') { body.push(''); i++; }
        else break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      hunks.push({ A, body });
    } else {
      i++;
    }
  }

  const finalOld = oldPath;
  const finalNew = newPath;
  const isCreation = finalOld === null || finalOld === '/dev/null' || creation;
  const isDeletion = !isCreation && (finalNew === null || finalNew === '/dev/null' || deletion);

  const edit: Edit = (tree, strict) => {
    const op = finalOld === null || finalOld === '/dev/null' ? null : finalOld;
    const np = finalNew === null || finalNew === '/dev/null' ? null : finalNew;
    if (op !== null && !safe(op)) throw new Fail('unsafe', op);
    if (np !== null && !safe(np)) throw new Fail('unsafe', np);

    if (isCreation) {
      const target = np!;
      if (tree.get(target) !== null) throw new Fail('exists', target);
      tree.now.set(target, fromDoc(buildCreatedDoc(hunks)));
      return;
    }
    if (isDeletion) {
      const target = op!;
      if (tree.get(target) === null) throw new Fail('missing', target);
      tree.now.set(target, null);
      return;
    }
    if (op !== np) {
      const o = op!;
      const n = np!;
      if (tree.get(o) === null) throw new Fail('missing', o);
      if (tree.get(n) !== null) throw new Fail('exists', n);
      const result = applyHunks(tree.doc(o)!, hunks, strict, o);
      tree.now.set(n, fromDoc(result));
      tree.now.set(o, null);
      tree.moves.push({ old: o, new: n });
      return;
    }
    const t = op!;
    if (tree.get(t) === null) throw new Fail('missing', t);
    tree.now.set(t, fromDoc(applyHunks(tree.doc(t)!, hunks, strict, t)));
  };
  return { edit, next: i };
}

function buildCreatedDoc(hunks: Hunk[]): Doc {
  const out: string[] = [];
  let sawNoNl = false;
  for (const h of hunks) {
    const body = h.body;
    let lastPlus = -1;
    for (let k = 0; k < body.length; k++) if (body[k]!.startsWith('+')) lastPlus = k;
    for (let k = 0; k < body.length; k++) {
      const b = body[k]!;
      if (b.startsWith('+')) out.push(b.slice(1));
    }
    if (lastPlus >= 0) {
      for (let k = lastPlus + 1; k < body.length; k++) if (body[k].charCodeAt(0) === 92) sawNoNl = true;
    }
  }
  return { lines: out, br: '\n', final: !sawNoNl };
}

function applyHunks(base: Doc, hunks: Hunk[], strict: boolean, path: string): Doc {
  let lines = base.lines.slice();
  const br = base.br;
  let finalBreak = base.final;
  let d = 0;
  const maxTier = strict ? 0 : 2;

  for (const h of hunks) {
    const { O, N } = analyzeBody(h.body);
    const noFinal = hasNoFinalBreak(h.body);

    if (O.length === 0) {
      const at = Math.max(0, Math.min(h.A + d, lines.length));
      const atEnd = at >= lines.length;
      const ins = buildN(lines, O, N, at, maxTier);
      lines.splice(at, 0, ...ins);
      d += ins.length;
      if (atEnd) finalBreak = !noFinal;
    } else {
      const { tier, occ } = matchTier(lines, O, maxTier);
      if (occ.length === 0) throw new Fail('no-match', path);
      const target = h.A - 1 + d;
      let best = occ[0]!;
      let bestDist = Math.abs(best - target);
      for (const p of occ) {
        const dist = Math.abs(p - target);
        if (dist < bestDist || (dist === bestDist && p < best)) { best = p; bestDist = dist; }
      }
      const newLines = buildN(lines, O, N, best, tier);
      const matchedToEnd = best + O.length >= lines.length;
      lines.splice(best, O.length, ...newLines);
      if (matchedToEnd) finalBreak = !noFinal;
      d += newLines.length - O.length;
    }
  }
  return { lines, br, final: finalBreak };
}

// ---------- search/replace (section 7) ----------
function parseSearchReplace(lines: string[]): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let searchFrom = 0;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.replace(/[ \t]+$/, '') !== '<<<<<<< SEARCH') { i++; continue; }
    const searchLine = i;
    let path: string | null = null;
    for (let j = searchLine - 1; j >= searchFrom; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      const t = l.trim();
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    let k = searchLine + 1;
    const oldLines: string[] = [];
    while (k < lines.length && lines[k]!.replace(/[ \t]+$/, '') !== '=======') { oldLines.push(lines[k]!); k++; }
    if (k >= lines.length) throw new Exit2(`error: parse ${searchLine + 1}`);
    k++;
    const newLines: string[] = [];
    while (k < lines.length && lines[k]!.replace(/[ \t]+$/, '') !== '>>>>>>> REPLACE') { newLines.push(lines[k]!); k++; }
    if (k >= lines.length) throw new Exit2(`error: parse ${searchLine + 1}`);
    k++;
    const p = path;
    const O = oldLines.slice();
    const N = newLines.slice();
    edits.push((tree, strict) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (O.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, N.join('\n') + '\n');
        return;
      }
      if (tree.get(p) === null) throw new Fail('missing', p);
      const base = tree.doc(p)!;
      const maxTier = strict ? 0 : 2;
      const { tier, occ } = matchTier(base.lines, O, maxTier);
      if (occ.length === 0) throw new Fail('no-match', p);
      if (occ.length > 1) throw new Fail('ambiguous', p);
      const start = occ[0]!;
      const F = leading(base.lines[start]!);
      const P = leading(O[0]!);
      const newLines2 = N.map((text) => {
        if (tier === 2 && text !== '' && text.trim() !== '' && text.startsWith(P)) return F + text.slice(P.length);
        return text;
      });
      base.lines.splice(start, O.length, ...newLines2);
      tree.now.set(p, fromDoc(base));
    });
    prevPath = p;
    searchFrom = k;
    i = k;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

// ---------- v4a (section 8) ----------
interface V4AChunk { anchor: string | null; body: string[]; eof: boolean; }

function parseV4A(lines: string[]): Edit[] {
  const firstNonBlank = lines.findIndex((l) => !blank(l));
  if (firstNonBlank < 0) throw new Exit2('error: parse 1');
  if (lines[firstNonBlank]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${firstNonBlank + 1}`);
  let lastNonBlank = -1;
  for (let k = lines.length - 1; k >= 0; k--) { if (!blank(lines[k]!)) { lastNonBlank = k; break; } }
  if (lastNonBlank < 0 || lines[lastNonBlank]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);

  const edits: Edit[] = [];
  let i = firstNonBlank + 1;
  const end = lastNonBlank;
  while (i < end) {
    const l = lines[i]!;
    if (blank(l)) { i++; continue; }
    if (l.startsWith('*** Add File:')) {
      const p = l.slice('*** Add File:'.length).trim();
      i++;
      const fileLines: string[] = [];
      while (i < end) {
        const b = lines[i]!;
        if (b.startsWith('***')) break;
        if (b.startsWith('+')) { fileLines.push(b.slice(1)); i++; }
        else if (b === '') { fileLines.push(''); i++; }
        else break;
      }
      while (fileLines.length > 0 && fileLines[fileLines.length - 1] === '') fileLines.pop();
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, fileLines.join('\n') + '\n');
      });
    } else if (l.startsWith('*** Delete File:')) {
      const p = l.slice('*** Delete File:'.length).trim();
      i++;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
    } else if (l.startsWith('*** Update File:')) {
      const p = l.slice('*** Update File:'.length).trim();
      const updateLine = i + 1;
      i++;
      let moveTo: string | null = null;
      if (i < end && lines[i]!.startsWith('*** Move to:')) { moveTo = lines[i]!.slice('*** Move to:'.length).trim(); i++; }
      const chunks: V4AChunk[] = [];
      while (i < end) {
        const b = lines[i]!;
        if (b.startsWith('***') && b.trim() !== '*** End of File') break;
        if (b.trim() === '*** End of File') {
          if (chunks.length > 0) { chunks[chunks.length - 1]!.eof = true; i++; continue; }
          break;
        }
        if (blank(b)) { i++; continue; }
        const chunk = b.startsWith('@@') ? parseChunk(lines, i, end, b.slice(2).trim()) : parseChunk(lines, i, end, null, true);
        if (!chunk) throw new Exit2(`error: parse ${i + 1}`);
        chunks.push(chunk.chunk);
        i = chunk.next;
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLine}`);
      const mv = moveTo;
      edits.push((tree, strict) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        if (mv !== null) {
          if (!safe(mv)) throw new Fail('unsafe', mv);
          if (tree.get(mv) !== null) throw new Fail('exists', mv);
        }
        const result = applyChunks(tree.doc(p)!, chunks, strict, p);
        if (mv !== null) { tree.now.set(mv, fromDoc(result)); tree.now.set(p, null); tree.moves.push({ old: p, new: mv }); }
        else tree.now.set(p, fromDoc(result));
      });
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function parseChunk(lines: string[], i: number, end: number, anchor: string | null, firstBody = false): { chunk: V4AChunk; next: number } | null {
  if (!firstBody) i++;
  const body: string[] = [];
  let eof = false;
  while (i < end) {
    const c = lines[i]!;
    if (c.trim() === '*** End of File') { eof = true; i++; break; }
    if (c.startsWith('***')) break;
    if (c === '') { body.push(''); i++; }
    else if (c.startsWith(' ') || c.startsWith('-') || c.startsWith('+')) { body.push(c); i++; }
    else break;
  }
  let k = body.length;
  while (k > 0 && body[k - 1]!.trim() === '') k--;
  const trimmedBody = body.slice(0, k);
  return { chunk: { anchor: anchor === '' ? null : anchor, body: trimmedBody, eof }, next: i };
}

function applyChunks(base: Doc, chunks: V4AChunk[], strict: boolean, path: string): Doc {
  const lines = base.lines.slice();
  const br = base.br;
  let final = base.final;
  const maxTier = strict ? 0 : 2;
  let cursor = 0;

  for (const ch of chunks) {
    if (ch.anchor !== null) {
      let found = -1;
      const { occ } = matchTier(lines, [ch.anchor], maxTier);
      for (const p of occ) { if (p >= cursor) { found = p; break; } }
      if (found < 0) throw new Fail('no-match', path);
      cursor = found + 1;
    }
    const { O, N } = analyzeBody(ch.body);
    if (O.length === 0) {
      const at = ch.eof ? lines.length : cursor;
      const ins = buildN(lines, O, N, Math.min(at, lines.length), maxTier);
      lines.splice(at, 0, ...ins);
      cursor = at + ins.length;
    } else {
      let found = -1;
      let foundTier = maxTier;
      const m = matchTier(lines.slice(cursor), O, maxTier);
      if (m.occ.length > 0) {
        foundTier = m.tier;
        for (const p of m.occ) {
          const abs = p + cursor;
          if (ch.eof && abs + O.length !== lines.length) continue;
          found = abs;
          break;
        }
      }
      if (found < 0) throw new Fail('no-match', path);
      const newLines = buildN(lines, O, N, found, foundTier);
      lines.splice(found, O.length, ...newLines);
      cursor = found + newLines.length;
    }
  }
  return { lines, br, final };
}

// ---------- json edits (section 9) ----------
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  if (typeof o.path !== 'string') return null;
  const p = o.path;

  const requireFile = (tree: Tree): Doc => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return toDoc(t);
  };

  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const doc = requireFile(tree);
      const crlf = doc.br === '\r\n';
      const text = fromDoc(doc);
      const norm = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = norm(text);
      const old = norm(oldStr);
      let count = 0;
      let first = -1;
      for (let x = t.indexOf(old); x >= 0; x = t.indexOf(old, x + 1)) { count++; if (first < 0) first = x; }
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const out = t.slice(0, first) + norm(newStr) + t.slice(first + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const doc = requireFile(tree);
      if (line < 0 || line > doc.lines.length) throw new Fail('no-match', p);
      doc.lines.splice(line, 0, ...add);
      tree.now.set(p, fromDoc(doc));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try { v = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) { const e = jsonEdit(x); if (e === null) throw new Exit2(`error: parse ${first + 1}`); edits.push(e); }
    return edits;
  }
  lines.forEach((l, idx) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try { e = jsonEdit(JSON.parse(l)); } catch { e = null; }
    if (e === null) throw new Exit2(`error: parse ${idx + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------- run (sections 1, 2, 10) ----------
function cmpPath(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;

  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a === '--check') { if (check) return { code: 2, out: ['error: usage'] }; check = true; }
    else if (!ended && a === '--strict') { if (strict) return { code: 2, out: ['error: usage'] }; strict = true; }
    else if (!ended && a.startsWith('--format=')) {
      if (format !== null) return { code: 2, out: ['error: usage'] };
      const v = a.slice('--format='.length);
      if (!['auto', 'unified', 'search-replace', 'v4a', 'json'].includes(v)) return { code: 2, out: ['error: usage'] };
      format = v;
    } else if (!ended && a.startsWith('-') && a !== '-') {
      return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;

  let text = '';
  try { text = readFileSync(file ?? 0, 'utf8'); }
  catch { return { code: 2, out: ['error: no-patch'] }; }

  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };

  let edits: Edit[];
  try {
    switch (kind) {
      case 'unified': edits = parseUnified(lines); break;
      case 'search-replace': edits = parseSearchReplace(lines); break;
      case 'v4a': edits = parseV4A(lines); break;
      case 'json': edits = jsonEdits(text, lines); break;
      default: edits = [];
    }
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }

  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const snapNow = new Map(tree.now);
    const snapMoves = tree.moves.length;
    try { edit(tree, strict); }
    catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of snapNow) tree.now.set(k, v);
      tree.moves.length = snapMoves;
      fails.push(e);
    }
  }

  if (fails.length > 0) {
    return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  }

  const changed: string[] = [];
  for (const p of tree.now.keys()) if (tree.original(p) !== tree.now.get(p)) changed.push(p);
  changed.sort(cmpPath);

  const moveByNew = new Map<string, string>();
  for (const m of tree.moves) {
    if (tree.original(m.old) !== null && tree.get(m.old) === null && tree.original(m.new) === null && tree.get(m.new) !== null) moveByNew.set(m.new, m.old);
  }
  const moveOld = new Set<string>();
  for (const m of tree.moves) { if (moveByNew.get(m.new) === m.old) moveOld.add(m.old); }

  const rows: string[] = [];
  for (const p of changed) {
    if (moveByNew.has(p)) rows.push(`R ${moveByNew.get(p)} -> ${p}`);
    else if (tree.original(p) === null && tree.now.get(p) !== null) rows.push(`A ${p}`);
    else if (tree.original(p) !== null && tree.now.get(p) === null) { if (!moveOld.has(p)) rows.push(`D ${p}`); }
    else rows.push(`M ${p}`);
  }
  rows.sort((a, b) => {
    const pa = a.startsWith('R ') ? a.slice(2).split(' -> ')[1]! : a.slice(2);
    const pb = b.startsWith('R ') ? b.slice(2).split(' -> ')[1]! : b.slice(2);
    return cmpPath(pa, pb);
  });

  if (!check) {
    for (const p of changed) {
      const now = tree.now.get(p);
      if (now === null) rmSync(p, { force: true });
      else { mkdirSync(dirname(p), { recursive: true }); writeFileSync(p, now); }
    }
  }

  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // runTrial wired in runner.ts; left inert in practice mode.
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => l + '\n').join(''));
  process.exitCode = r.code;
}
