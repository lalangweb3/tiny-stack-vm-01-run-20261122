// tiny-stack-vm-01: exact interpreter for make.fun's tiny stack ISA v1.
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
// Opcode table: [byte, immediate bytes, pops, pushes]; -1 imm = unknown op.
const IMM = new Int8Array(256).fill(-1), POP = new Uint8Array(256), PSH = new Uint8Array(256);
for (const [o, i, a, b] of [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]]) {
  IMM[o] = i; POP[o] = a; PSH[o] = b;
}
const dg = new Uint8Array(12); // PRINT scratch: decimal digits, backwards
function run(p, inp) {
  const n = p.length, s = new Int32Array(256);
  let sp = 0;
  const c = new Int32Array(64);
  let cp = 0;
  const m = new Int32Array(256);
  const o = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, steps = 0;
  const done = (code) => ({ out: o.subarray(0, ol), code });
  for (;;) {
    if (steps === 1000000) return done(10); // step limit
    if (pc < 0 || pc >= n) return done(9); // pc outside program
    const op = p[pc], im = IMM[op];
    if (im < 0) return done(5); // unknown opcode
    if (pc + im >= n) return done(9); // immediate cut off
    steps++;
    if (sp < POP[op]) return done(2); // stack underflow
    if (sp - POP[op] + PSH[op] > 256) return done(3); // stack overflow
    const nx = pc + 1 + im;
    pc = nx;
    switch (op) {
      case 0: return done(0); // HALT
      case 1: s[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: s[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: s[sp] = s[sp - 1]; sp++; break; // DUP
      case 5: { const t = s[sp - 1]; s[sp - 1] = s[sp - 2]; s[sp - 2] = t; break; } // SWAP
      case 6: s[sp] = s[sp - 2]; sp++; break; // OVER
      case 7: { const a = s[sp - 3]; s[sp - 3] = s[sp - 2]; s[sp - 2] = s[sp - 1]; s[sp - 1] = a; break; } // ROT
      case 23: s[sp - 1] = (-s[sp - 1]) | 0; break; // NEG, wraps
      case 27: s[sp - 1] = ~s[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = s[sp - 1], a = s[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b); // exact low 32 bits
        else if (op === 19) {
          if (b === 0) return done(4);
          r = (a / b) | 0; // -2^31 / -1 wraps to -2^31 via |0
        } else if (op === 20) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0; // remainder keeps a's sign
        } else if (op === 21) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // unsigned
        } else if (op === 22) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0; // unsigned
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31); // arithmetic
        else if (op === 30) r = (a >>> (b & 31)) | 0; // logical
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp -= 2;
        s[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) {
          const v = s[--sp];
          take = op === 49 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return done(7); // call stack overflow
        c[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return done(8); // RET with empty call stack
        pc = c[--cp];
        break;
      case 64: {
        const ad = s[sp - 1];
        if (ad < 0 || ad > 255) return done(6);
        s[sp - 1] = m[ad];
        break;
      }
      case 65: {
        const ad = s[sp - 1], v = s[sp - 2];
        if (ad < 0 || ad > 255) return done(6);
        sp -= 2;
        m[ad] = v;
        break;
      }
      case 80: {
        const v = s[sp - 1];
        let u = v, neg = false;
        if (v < 0) { neg = true; u = v === -2147483648 ? 2147483648 : -v; }
        let d = 0;
        if (u === 0) dg[d++] = 48;
        while (u > 0) { dg[d++] = 48 + (u % 10); u = Math.floor(u / 10); }
        const len = d + (neg ? 1 : 0);
        if (ol + len > 65536) return done(11); // output limit, writes nothing
        sp--;
        let w = ol;
        if (neg) o[w++] = 45;
        while (d > 0) o[w++] = dg[--d];
        ol = w;
        break;
      }
      case 81:
        if (ol + 1 > 65536) return done(11);
        o[ol++] = s[--sp] & 255;
        break;
      case 82:
        s[sp++] = ip < inp.length ? inp[ip++] : -1; // -1 past end of input
        break;
      case 83:
        return done(s[--sp] & 255); // EXIT, low byte
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  // Answer only real instance directories; stray files in /input are ignored.
  if (!statSync(join(I, id)).isDirectory()) continue;
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
