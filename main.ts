// Tiny stack VM (ISA v1), Node 22, stdlib only.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const MAX_STEPS = 1_000_000;
const MAX_OUT = 65_536;
const STACK_CAP = 256;
const CALL_CAP = 64;
const MEM_WORDS = 256;

type Answer = { bytes: Uint8Array; code: number };

function run(prog: Uint8Array, input: Uint8Array): Answer {
  const data = new Int32Array(STACK_CAP);
  const rets = new Int32Array(CALL_CAP);
  const mem = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(MAX_OUT);
  let sp = 0;
  let rp = 0;
  let pc = 0;
  let steps = 0;
  let ip = 0;
  let olen = 0;
  const done = (code: number): Answer => ({ bytes: out.slice(0, olen), code });
  for (;;) {
    if (steps === MAX_STEPS) return done(10);
    if (pc < 0 || pc >= prog.length) return done(9);
    const op = prog[pc];
    let imm = 0;
    let pops = 0;
    let pushes = 0;
    if (op < 0x08) {
      if (op === 0x01) { imm = 1; pushes = 1; }
      else if (op === 0x02) { imm = 4; pushes = 1; }
      else if (op === 0x03) pops = 1;
      else if (op === 0x04) { pops = 1; pushes = 2; }
      else if (op === 0x05) { pops = 2; pushes = 2; }
      else if (op === 0x06) { pops = 2; pushes = 3; }
      else if (op === 0x07) { pops = 3; pushes = 3; }
    } else if (op >= 0x10 && op <= 0x1e) {
      pops = op === 0x17 || op === 0x1b ? 1 : 2;
      pushes = 1;
    } else if (op >= 0x20 && op <= 0x22) {
      pops = 2;
      pushes = 1;
    } else if (op >= 0x30 && op <= 0x34) {
      if (op !== 0x34) imm = 2;
      if (op === 0x31 || op === 0x32) pops = 1;
    } else if (op === 0x40) {
      pops = 1;
      pushes = 1;
    } else if (op === 0x41) {
      pops = 2;
    } else if (op >= 0x50 && op <= 0x53) {
      if (op === 0x52) pushes = 1;
      else pops = 1;
    } else {
      return done(5);
    }
    if (pc + imm >= prog.length) return done(9);
    steps++;
    const nx = pc + 1 + imm;
    if (sp < pops) return done(2);
    if (sp - pops + pushes > STACK_CAP) return done(3);
    pc = nx;
    switch (op) {
      case 0x00:
        return done(0);
      case 0x01:
        data[sp++] = (prog[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        data[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        data[sp] = data[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = data[sp - 1];
        data[sp - 1] = data[sp - 2];
        data[sp - 2] = t;
        break;
      }
      case 0x06:
        data[sp] = data[sp - 2];
        sp++;
        break;
      case 0x07: {
        const t = data[sp - 3];
        data[sp - 3] = data[sp - 2];
        data[sp - 2] = data[sp - 1];
        data[sp - 1] = t;
        break;
      }
      case 0x10:
      case 0x11:
      case 0x12:
      case 0x13:
      case 0x14:
      case 0x15:
      case 0x16:
      case 0x18:
      case 0x19:
      case 0x1a:
      case 0x1c:
      case 0x1d:
      case 0x1e:
      case 0x20:
      case 0x21:
      case 0x22: {
        const b = data[sp - 1];
        const a = data[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return done(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return done(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15:
            if (b === 0) return done(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return done(4);
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
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        data[sp++] = r;
        break;
      }
      case 0x17:
        data[sp - 1] = (-data[sp - 1]) | 0;
        break;
      case 0x1b:
        data[sp - 1] = ~data[sp - 1];
        break;
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (!take) {
          const v = data[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (rp === CALL_CAP) return done(7);
        rets[rp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34:
        if (rp === 0) return done(8);
        pc = rets[--rp];
        break;
      case 0x40: {
        const addr = data[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return done(6);
        data[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = data[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return done(6);
        mem[addr] = data[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const s = String(data[sp - 1]);
        if (olen + s.length > MAX_OUT) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > MAX_OUT) return done(11);
        out[olen++] = data[--sp] & 255;
        break;
      case 0x52:
        data[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        return done(data[--sp] & 255);
      default:
        return done(5);
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const prog = readFileSync(join(IN_DIR, id, 'program.bin'));
  const input = readFileSync(join(IN_DIR, id, 'input.bin'));
  const ans = run(prog, input);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), ans.bytes);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${ans.code}\n`);
}
