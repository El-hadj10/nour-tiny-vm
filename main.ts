import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const ST = 256, CA = 64, MW = 256, LIM = 1000000, OM = 65536;
const T_OK = 0, T_UNDERFLOW = 2, T_OVERFLOW = 3, T_DIVZERO = 4, T_UNKNOWN = 5, T_MEM = 6, T_CALLFULL = 7, T_CALLEMPTY = 8, T_BADPC = 9, T_STEPLIMIT = 10, T_OUTOVERFLOW = 11;
const IMM = new Uint8Array(256).fill(255);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
const def = (o: number, i: number, p: number, q: number) => { IMM[o] = i; POP[o] = p; PSH[o] = q; };
def(0x00, 0, 0, 0);
def(0x01, 1, 0, 1);
def(0x02, 4, 0, 1);
def(0x03, 0, 1, 0);
def(0x04, 0, 1, 2);
def(0x05, 0, 2, 2);
def(0x06, 0, 2, 3);
def(0x07, 0, 3, 3);
for (let o = 0x10; o <= 0x16; o++) def(o, 0, 2, 1);
def(0x17, 0, 1, 1);
for (let o = 0x18; o <= 0x1a; o++) def(o, 0, 2, 1);
def(0x1b, 0, 1, 1);
for (let o = 0x1c; o <= 0x1e; o++) def(o, 0, 2, 1);
for (let o = 0x20; o <= 0x22; o++) def(o, 0, 2, 1);
def(0x30, 2, 0, 0);
def(0x31, 2, 1, 0);
def(0x32, 2, 1, 0);
def(0x33, 2, 0, 0);
def(0x34, 0, 0, 0);
def(0x40, 0, 1, 1);
def(0x41, 0, 2, 0);
def(0x50, 0, 1, 0);
def(0x51, 0, 1, 0);
def(0x52, 0, 0, 1);
def(0x53, 0, 1, 0);

const ENC = new TextEncoder();

function run(prog: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const D = new Int32Array(ST);
  const C = new Int32Array(CA);
  const M = new Int32Array(MW);
  const out = new Uint8Array(OM);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const ret = (code: number) => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === LIM) return ret(T_STEPLIMIT);
    if (pc < 0 || pc >= n) return ret(T_BADPC);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm === 255) return ret(T_UNKNOWN);
    if (pc + imm >= n) return ret(T_BADPC);
    steps++;
    const next = pc + 1 + imm;
    const pops = POP[op];
    const pushes = PSH[op];
    if (sp < pops) return ret(T_UNDERFLOW);
    if (sp - pops + pushes > ST) return ret(T_OVERFLOW);
    pc = next;
    switch (op) {
      case 0x00:
        return ret(T_OK);
      case 0x01: {
        let v = prog[next - 1];
        if (v >= 128) v -= 256;
        D[sp++] = v;
        break;
      }
      case 0x02:
        D[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r = 0;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return ret(T_DIVZERO);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return ret(T_DIVZERO);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15:
            if (b === 0) return ret(T_DIVZERO);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return ret(T_DIVZERO);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x17:
        D[sp - 1] = (-D[sp - 1]) | 0;
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: {
        if (csp === CA) return ret(T_CALLFULL);
        C[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      }
      case 0x34: {
        if (csp === 0) return ret(T_CALLEMPTY);
        pc = C[--csp];
        break;
      }
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= MW) return ret(T_MEM);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= MW) return ret(T_MEM);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = ENC.encode(String(D[sp - 1]));
        if (olen + bytes.length > OM) return ret(T_OUTOVERFLOW);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51: {
        if (olen + 1 > OM) return ret(T_OUTOVERFLOW);
        out[olen++] = D[--sp] & 255;
        break;
      }
      case 0x52:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return ret(D[--sp] & 255);
      default:
        return ret(T_UNKNOWN);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
