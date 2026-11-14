#!/usr/bin/env python3
"""Generate vm_test/categories/ corpus + COVERAGE.json (gitignored)."""
from __future__ import annotations

import json
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "categories"
WRITTEN: list[str] = []  # "cat/name"

MAIN = r'''
int main(int argc, char** argv) {
    uint32_t x = (argc > 1) ? (uint32_t)strtoul(argv[1], 0, 0) : 123u;
    uint32_t y = (argc > 2) ? (uint32_t)strtoul(argv[2], 0, 0) : 456u;
    uint32_t r = obf_target(x, y);
    printf("R=%u\n", r);
    return (int)(r & 0xFFu);
}
'''

HDR = """\
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
"""

ANN = '__attribute__((noinline, annotate("obf: vm()")))'
ANN_SUPER = '__attribute__((noinline, annotate("obf: vm(superOps=1)")))'
ANN_CONST = '__attribute__((noinline, annotate("obf: vm(constInStream=1)")))'

BASE_EXPECT = {
    "must_match": [r"vm\.bytecode\b", r"@__vm_engine\b"],
}


def write(cat: str, name: str, body: str, expect: dict | None = None, ann: str = ANN):
    d = ROOT / cat
    d.mkdir(parents=True, exist_ok=True)
    src = d / f"{name}.c"
    src.write_text(HDR + "\n" + body.replace("{ANN}", ann) + "\n" + MAIN + "\n", encoding="utf-8")
    exp = expect or dict(BASE_EXPECT)
    (d / f"{name}.expect.json").write_text(json.dumps(exp, indent=2) + "\n", encoding="utf-8")
    WRITTEN.append(f"{cat}/{name}")


def write_ll(cat: str, name: str, ir: str, expect: dict | None = None):
    d = ROOT / cat
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{name}.ll").write_text(ir, encoding="utf-8")
    exp = expect or dict(BASE_EXPECT)
    (d / f"{name}.expect.json").write_text(json.dumps(exp, indent=2) + "\n", encoding="utf-8")
    WRITTEN.append(f"{cat}/{name}")


def ll_main_boilerplate() -> str:
    return r'''
@.str.r = private unnamed_addr constant [6 x i8] c"R=%u\0A\00"
declare i64 @strtoul(ptr, ptr, i32)
declare i32 @printf(ptr, ...)

define i32 @main(i32 %argc, ptr %argv) {
entry:
  %x0 = add i32 123, 0
  %y0 = add i32 456, 0
  %has1 = icmp sgt i32 %argc, 1
  br i1 %has1, label %lx, label %go
lx:
  %ap1 = getelementptr inbounds ptr, ptr %argv, i64 1
  %s1 = load ptr, ptr %ap1
  %xv = call i64 @strtoul(ptr %s1, ptr null, i32 0)
  %x1 = trunc i64 %xv to i32
  %has2 = icmp sgt i32 %argc, 2
  br i1 %has2, label %ly, label %go_x
ly:
  %ap2 = getelementptr inbounds ptr, ptr %argv, i64 2
  %s2 = load ptr, ptr %ap2
  %yv = call i64 @strtoul(ptr %s2, ptr null, i32 0)
  %y1 = trunc i64 %yv to i32
  br label %go_xy
go_x:
  br label %go_xy
go:
  %r0 = call i32 @obf_target(i32 %x0, i32 %y0)
  br label %print
go_xy:
  %xx = phi i32 [ %x1, %ly ], [ %x1, %go_x ]
  %yy = phi i32 [ %y1, %ly ], [ %y0, %go_x ]
  %r1 = call i32 @obf_target(i32 %xx, i32 %yy)
  br label %print
print:
  %r = phi i32 [ %r0, %go ], [ %r1, %go_xy ]
  call i32 (ptr, ...) @printf(ptr @.str.r, i32 %r)
  %ret = and i32 %r, 255
  ret i32 %ret
}
'''


def ll_ann_globals() -> str:
    return r'''
@llvm.global.annotations = appending global [1 x { ptr, ptr, ptr, i32, ptr }] [
  { ptr, ptr, ptr, i32, ptr } { ptr @obf_target, ptr @.str.ann, ptr poison, i32 0, ptr poison }
], section "llvm.metadata"
@.str.ann = private unnamed_addr constant [10 x i8] c"obf: vm()\00"
'''


def cat_int32():
    write("01_int32", "test_binop_all", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t a = x + 0x11111111u;
    uint32_t b = y ? y : 1u;
    uint32_t r = 0;
    r ^= (a + b);
    r ^= (a - b);
    r ^= (a * b);
    r ^= (a & b);
    r ^= (a | b);
    r ^= (a ^ b);
    r ^= (a << (b & 31u));
    r ^= (a >> (b & 31u));
    r ^= (uint32_t)((int32_t)a >> (int32_t)(b & 31u));
    r ^= (uint32_t)((int32_t)a / (int32_t)b);
    r ^= (a / b);
    r ^= (uint32_t)((int32_t)a % (int32_t)b);
    r ^= (a % b);
    return r;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.binop"]})

    write("01_int32", "test_cast", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint8_t  a8  = (uint8_t)x;
    int8_t   s8  = (int8_t)y;
    uint16_t a16 = (uint16_t)x;
    int16_t  s16 = (int16_t)y;
    uint32_t r = 0;
    r ^= (uint32_t)a8;
    r ^= (uint32_t)(int32_t)s8;
    r ^= (uint32_t)a16;
    r ^= (uint32_t)(int32_t)s16;
    r ^= (uint32_t)(uint8_t)(x + y);
    r ^= (uint32_t)(uint16_t)(x * y);
    r ^= (x & 1u) ? 1u : 0u;
    return r;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.cast"]})

    write("01_int32", "test_icmp_select", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t r = 0;
    r += (x == y);
    r += (x != y);
    r += (x < y);
    r += (x > y);
    r += (x <= y);
    r += (x >= y);
    r += ((int32_t)x < (int32_t)y);
    r += ((int32_t)x > (int32_t)y);
    r += ((int32_t)x <= (int32_t)y);
    r += ((int32_t)x >= (int32_t)y);
    uint32_t s = (x & 1u) ? (x + y) : (x - y);
    return r ^ s;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.icmp", r"vm\.opc\.select"]})

    write("01_int32", "test_loadi", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t k0 = 0xA5A5A5A5u;
    uint32_t k1 = 0x12345678u;
    uint32_t k2 = 0xF00DFACEu;
    return (x ^ k0) + (y ^ k1) + k2;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.loadi"]}, ann=ANN_CONST)


def cat_int64():
    write("02_int64", "test_binop64_all", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint64_t a = ((uint64_t)x << 32) | (uint64_t)y;
    uint64_t b = ((uint64_t)y << 32) | (uint64_t)(x | 1u);
    uint64_t r = 0;
    r ^= a + b;
    r ^= a - b;
    r ^= a * b;
    r ^= a & b;
    r ^= a | b;
    r ^= a ^ b;
    r ^= a << (b & 63ull);
    r ^= a >> (b & 63ull);
    r ^= (uint64_t)((int64_t)a >> (int64_t)(b & 63ull));
    r ^= (uint64_t)((int64_t)a / (int64_t)b);
    r ^= a / b;
    r ^= (uint64_t)((int64_t)a % (int64_t)b);
    r ^= a % b;
    return (uint32_t)(r ^ (r >> 32));
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.binop64"]})

    write("02_int64", "test_cast64", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint64_t r = 0;
    r ^= (uint64_t)(uint8_t)x;
    r ^= (uint64_t)(int64_t)(int8_t)y;
    r ^= (uint64_t)(uint16_t)x;
    r ^= (uint64_t)(int64_t)(int16_t)y;
    r ^= (uint64_t)x;
    r ^= (uint64_t)(int64_t)(int32_t)y;
    uint64_t wide = ((uint64_t)x << 40) | ((uint64_t)y << 8) | 0xAAull;
    r ^= (uint8_t)wide;
    r ^= (uint16_t)wide;
    r ^= (uint32_t)wide;
    r ^= (wide & 1ull);
    return (uint32_t)(r ^ (r >> 32));
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.cast64"]})

    write("02_int64", "test_icmp64_select", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint64_t a = ((uint64_t)x << 32) | y;
    uint64_t b = ((uint64_t)y << 32) | x;
    uint32_t r = 0;
    r += (a == b);
    r += (a != b);
    r += (a < b);
    r += (a > b);
    r += ((int64_t)a < (int64_t)b);
    r += ((int64_t)a >= (int64_t)b);
    uint64_t s = (x & 1u) ? (a + b) : (a ^ b);
    return r ^ (uint32_t)(s ^ (s >> 32));
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.icmp64", r"vm\.opc\.select"]})

    write("02_int64", "test_loadi64", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint64_t k0 = 0x0123456789ABCDEFull;
    uint64_t k1 = 0xFEDCBA9876543210ull;
    uint64_t a = ((uint64_t)x << 32) | y;
    uint64_t r = (a ^ k0) + k1;
    return (uint32_t)(r ^ (r >> 32));
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.loadi64"]}, ann=ANN_CONST)


def cat_control():
    write("03_control", "test_jmp_jmpc", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t r = x;
    if (x & 1u) {
        r = r + y;
    } else {
        r = r - y;
    }
    if (y > 10u) {
        r ^= 0x55u;
        if (x > y) r += 3u;
        else r += 7u;
    } else {
        r ^= 0xAAu;
    }
    return r;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.jmp", r"vm\.opc\.jmpc"]})

    write("03_control", "test_switch", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t r = 0;
    switch (x & 7u) {
        case 0: r = x + y; break;
        case 1: r = x - y; break;
        case 2: r = x ^ y; break;
        case 3: r = x | y; break;
        case 4: r = x & y; break;
        case 5: r = x * (y | 1u); break;
        case 6: r = (x << 1) + y; break;
        default: r = x ^ 0xFFu ^ y; break;
    }
    return r;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.switch"]})

    write("03_control", "test_ret_void_side", r'''
static uint32_t G;

{ANN}
void obf_side(uint32_t x, uint32_t y) {
    G = x ^ y ^ 0x1234u;
}

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    G = 0;
    obf_side(x, y);
    return G;
}
''', BASE_EXPECT)


def cat_memory():
    write("04_memory", "test_load_store_widths", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint8_t  b8[8];
    uint16_t b16[4];
    uint32_t b32[4];
    uint64_t b64[2];
    for (int i = 0; i < 8; i++) b8[i] = (uint8_t)(x + (uint32_t)i);
    for (int i = 0; i < 4; i++) b16[i] = (uint16_t)(y + (uint32_t)i * 3u);
    for (int i = 0; i < 4; i++) b32[i] = x ^ y ^ (uint32_t)i;
    b64[0] = ((uint64_t)x << 32) | y;
    b64[1] = ((uint64_t)y << 32) | x;
    b8[(x ^ y) & 7u] ^= (uint8_t)y;
    b16[(x) & 3u] += (uint16_t)x;
    b32[(y) & 3u] ^= x + y;
    b64[x & 1u] += 1ull;
    uint32_t r = 0;
    for (int i = 0; i < 8; i++) r ^= b8[i];
    for (int i = 0; i < 4; i++) r ^= b16[i];
    for (int i = 0; i < 4; i++) r ^= b32[i];
    r ^= (uint32_t)b64[0] ^ (uint32_t)(b64[0] >> 32);
    r ^= (uint32_t)b64[1] ^ (uint32_t)(b64[1] >> 32);
    return r;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [
        r"vm\.opc\.load8", r"vm\.opc\.store8",
        r"vm\.opc\.load16", r"vm\.opc\.store16",
        r"vm\.opc\.load32", r"vm\.opc\.store32",
        r"vm\.opc\.load64", r"vm\.opc\.store64",
    ]})

    write("04_memory", "test_load_store_ptr", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t a = x, b = y, c = x ^ y;
    uint32_t *slots[3] = { &a, &b, &c };
    uint32_t *p = slots[x % 3u];
    uint32_t *q = slots[y % 3u];
    *p = *p + 1u;
    slots[1] = q;
    uint32_t *rptr = slots[(x ^ y) % 3u];
    return *rptr ^ a ^ b ^ c;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [
        r"vm\.opc\.loadptr", r"vm\.opc\.storeptr",
    ]})

    write("04_memory", "test_gep", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t buf[16];
    for (uint32_t i = 0; i < 16; i++) buf[i] = i * 0x10001u ^ x ^ y;
    uint32_t idx = (x + y) & 15u;
    buf[idx] += buf[(idx + 3u) & 15u];
    return buf[idx] ^ buf[(idx + 7u) & 15u];
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.gep"]})

    write("04_memory", "test_gep64", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint8_t buf[64];
    for (int i = 0; i < 64; i++) buf[i] = (uint8_t)(i ^ (int)x ^ (int)y);
    /* large signed const offset → OP_GEP64 path (elemsz=1 byte offset) */
    uint8_t *base = buf;
    uint64_t off = (uint64_t)(x & 31u) + 0x100000000ull; /* > i32, then wrap via mask */
    (void)off;
    /* variable i64 index */
    uint64_t idx = (uint64_t)((x * 3u + y) & 63u);
    uint8_t *p = base + idx;
    *p ^= (uint8_t)y;
    /* force a const GEP whose absolute byte offset needs i64 when applied to a
       synthetic large displacement through uintptr arithmetic materialization */
    uintptr_t fake = (uintptr_t)base + (uintptr_t)0x0000000100000000ull;
    uintptr_t back = fake - (uintptr_t)0x0000000100000000ull;
    uint8_t *q = (uint8_t *)back;
    q[(y & 31u)] ^= (uint8_t)x;
    uint32_t r = 0;
    for (int i = 0; i < 64; i++) r = (r * 131u) + buf[i];
    return r;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.gep64"]})

    write("04_memory", "test_i1_mem", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    _Bool flags[8];
    for (int i = 0; i < 8; i++) flags[i] = ((x >> i) & 1u) != 0u;
    flags[y & 7u] = !flags[y & 7u];
    uint32_t r = 0;
    for (int i = 0; i < 8; i++) if (flags[i]) r |= (1u << i);
    return r ^ y;
}
''', BASE_EXPECT)


def cat_float():
    write("05_float", "test_binop_f", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    double a = (double)x + 0.5;
    double b = (double)(y ? y : 1u) + 0.25;
    float  fa = (float)x + 1.5f;
    float  fb = (float)(y ? y : 1u) + 0.75f;
    double r = 0.0;
    r += a + b;
    r += a - b;
    r += a * b;
    r += a / b;
    r += fmod(a, b);
    r += -a;
    float fr = 0.f;
    fr += fa + fb;
    fr += fa - fb;
    fr += fa * fb;
    fr += fa / fb;
    fr += fmodf(fa, fb);
    fr += -fa;
    r += (double)fr;
    return (uint32_t)(long)(r * 1000.0) ^ x ^ y;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.binop_f", r"vm\.opc\.fneg"]})

    write("05_float", "test_fcmp_select_f", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    double a = (double)x;
    double b = (double)y;
    uint32_t r = 0;
    r += (a == b);
    r += (a != b);
    r += (a < b);
    r += (a > b);
    r += (a <= b);
    r += (a >= b);
    double s = (x & 1u) ? (a + b) : (a - b);
    return r ^ (uint32_t)(long)s;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.fcmp", r"vm\.opc\.select_f"]})

    write("05_float", "test_fcast", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    float  f = (float)(int32_t)x;
    double d = (double)f;
    float  f2 = (float)d;
    int32_t si = (int32_t)d;
    uint32_t ui = (uint32_t)d;
    int64_t si64 = (int64_t)d;
    uint64_t ui64 = (uint64_t)((y ? y : 1u));
    double from_i = (double)(int32_t)y;
    double from_u = (double)x;
    double from_i64 = (double)si64;
    double from_u64 = (double)ui64;
    float from_si = (float)(int32_t)x;
    uint32_t r = (uint32_t)si ^ ui ^ (uint32_t)si64 ^ (uint32_t)ui64;
    r ^= (uint32_t)(long)(d + from_i + from_u + from_i64 + from_u64 + (double)from_si + (double)f2);
    return r;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [
        r"vm\.opc\.fcast_ff", r"vm\.opc\.fcast_fv", r"vm\.opc\.fcast_vf",
        r"vm\.opc\.fcast_fv64", r"vm\.opc\.fcast_v64f",
    ]})

    write("05_float", "test_float_mem_f64", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    double buf[4];
    buf[0] = (double)x;
    buf[1] = (double)y;
    buf[2] = buf[0] + buf[1];
    buf[3] = buf[0] * buf[1];
    buf[(x ^ y) & 3u] += 1.0;
    double s = buf[0] + buf[1] + buf[2] + buf[3];
    return (uint32_t)(long)(s * 10.0);
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.load_f", r"vm\.opc\.store_f"]})

    write("05_float", "test_float_mem_f32", r'''
static float GBUF[8];

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    for (int i = 0; i < 8; i++) GBUF[i] = (float)(x + (uint32_t)i) * 0.5f;
    GBUF[y & 7u] += (float)y;
    float *p = &GBUF[(x ^ y) & 7u];
    *p = *p * 1.5f;
    float s = 0.f;
    for (int i = 0; i < 8; i++) s += GBUF[i];
    return (uint32_t)(long)(s * 100.f);
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.load_f32", r"vm\.opc\.store_f32"]})

    write("05_float", "test_ret_f_via_bits", r'''
{ANN}
double obf_d(uint32_t x, uint32_t y) {
    return (double)x * 0.5 + (double)y * 0.25;
}

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    double d = obf_d(x, y);
    return (uint32_t)(long)(d * 1000.0);
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.ret_f"]})


def cat_ptr():
    write("06_ptr", "test_ptrtoint_inttoptr", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t buf[4] = { x, y, x ^ y, x + y };
    uintptr_t pi = (uintptr_t)&buf[(x ^ y) & 3u];
    uint32_t *p = (uint32_t *)pi;
    *p ^= 0x55u;
    /* i32 path when truncated */
    unsigned pi32 = (unsigned)(uintptr_t)(void *)&buf[0];
    uint32_t *q = (uint32_t *)(uintptr_t)pi32;
    return *p ^ *q ^ buf[1] ^ buf[2];
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [
        r"vm\.opc\.ptrtoint", r"vm\.opc\.ptrtoint64",
        r"vm\.opc\.inttoptr", r"vm\.opc\.inttoptr64",
    ]})

    write("06_ptr", "test_icmp_ptr_select", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t a = x, b = y;
    uint32_t *p = &a;
    uint32_t *q = (x & 1u) ? &a : &b;
    uint32_t r = 0;
    r += (p == q);
    r += (p != q);
    uint32_t *s = (y & 1u) ? p : &b;
    return r ^ *s ^ a ^ b;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [
        r"vm\.opc\.icmp_ptr", r"vm\.opc\.select",
    ]})

    write("06_ptr", "test_ret_ptr", r'''
static uint32_t SLOT;

{ANN}
uint32_t *obf_get(uint32_t x, uint32_t y) {
    SLOT = x ^ y;
    return &SLOT;
}

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t *p = obf_get(x, y);
    return *p;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.ret_ptr"]})


def cat_calls():
    write("07_calls", "test_call_int_void_ptr", r'''
__attribute__((noinline)) static uint32_t helper_int(uint32_t a, uint32_t b) {
    return a * 3u + b;
}
__attribute__((noinline)) static void helper_void(uint32_t *p, uint32_t v) {
    *p ^= v;
}
__attribute__((noinline)) static uint32_t *helper_ptr(uint32_t *p) {
    return p;
}

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t t = helper_int(x, y);
    helper_void(&t, y);
    uint32_t *p = helper_ptr(&t);
    return *p;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [
        r"vm\.opc\.call_int", r"vm\.opc\.call_void", r"vm\.opc\.call_ptr",
    ]})

    write("07_calls", "test_call_i64_f", r'''
__attribute__((noinline)) static uint64_t helper_i64(uint64_t a, uint64_t b) {
    return a ^ (b * 0x9E3779B97F4A7C15ull);
}
__attribute__((noinline)) static double helper_f(double a, double b) {
    return a * 2.0 + b;
}

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint64_t u = helper_i64(((uint64_t)x << 32) | y, ((uint64_t)y << 32) | x);
    double d = helper_f((double)x, (double)y);
    return (uint32_t)(u ^ (u >> 32)) ^ (uint32_t)(long)(d * 10.0);
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [
        r"vm\.opc\.call_int64", r"vm\.opc\.call_f",
    ]})

    write("07_calls", "test_call_narrow", r'''
__attribute__((noinline)) static uint8_t  h8(uint8_t a, uint8_t b) { return (uint8_t)(a + b); }
__attribute__((noinline)) static uint16_t h16(uint16_t a, uint16_t b) { return (uint16_t)(a ^ b); }
__attribute__((noinline)) static _Bool    h1(uint32_t a, uint32_t b) { return a > b; }

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t r = h8((uint8_t)x, (uint8_t)y);
    r ^= h16((uint16_t)x, (uint16_t)y);
    r ^= h1(x, y) ? 1u : 0u;
    return r;
}
''', BASE_EXPECT)

    # CALL_PAIR via C returning a struct {void*; long}
    write("07_calls", "test_call_pair", r'''
typedef struct { void *p; int64_t n; } Pair;

__attribute__((noinline)) static Pair make_pair(uint32_t x, uint32_t y) {
    static uint32_t storage;
    storage = x ^ y;
    Pair r;
    r.p = &storage;
    r.n = ((int64_t)x << 32) | (int64_t)y;
    return r;
}

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    Pair pr = make_pair(x, y);
    uint32_t *ip = (uint32_t *)pr.p;
    return *ip ^ (uint32_t)pr.n ^ (uint32_t)(pr.n >> 32);
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.call_pair"]})


def cat_legalize():
    write("08_legalize", "test_mem_expand", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint8_t src[64];
    uint8_t dst[64];
    for (int i = 0; i < 64; i++) src[i] = (uint8_t)(i ^ (int)x);
    memset(dst, (int)(y & 0xFFu), 64);
    memcpy(dst, src, 48);
    memmove(dst + 8, dst, 40);
    uint32_t r = 0;
    for (int i = 0; i < 64; i++) r = r * 33u + dst[i];
    return r;
}
''', {**BASE_EXPECT, "must_match_any": [
        [r"__vm_memcpy_loop", r"__vm_memset_loop", r"@memcpy", r"@memset", r"@memmove"],
    ]})

    write("08_legalize", "test_switch_i16", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint16_t c = (uint16_t)(x & 7u);
    uint32_t r;
    switch (c) {
        case 0: r = x + y; break;
        case 1: r = x - y; break;
        case 2: r = x ^ y; break;
        case 3: r = x | y; break;
        default: r = x * (y | 1u); break;
    }
    return r;
}
''', BASE_EXPECT)

    write("08_legalize", "test_agg_load", r'''
typedef struct { uint32_t a; uint32_t b; } Pair32;

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    Pair32 s = { x, y };
    Pair32 *p = &s;
    Pair32 t = *p; /* aggregate load → scalarized */
    return t.a ^ t.b ^ (t.a + t.b);
}
''', BASE_EXPECT)

    write("08_legalize", "test_phi_demote", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t r;
    if (x & 1u) r = x + y;
    else r = x ^ y;
    for (uint32_t i = 0; i < ((y & 7u) + 1u); i++) {
        r = r * 3u + i;
    }
    return r;
}
''', BASE_EXPECT)

    # odd-int via bitfield
    write("08_legalize", "test_odd_bitfield", r'''
typedef struct {
    unsigned a : 3;
    unsigned b : 5;
    unsigned c : 7;
    unsigned d : 11;
} Pack;

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    Pack p;
    p.a = x & 7u;
    p.b = y & 31u;
    p.c = (x ^ y) & 127u;
    p.d = (x + y) & 2047u;
    p.a ^= 1u;
    p.b += 1u;
    return (uint32_t)p.a | ((uint32_t)p.b << 3) | ((uint32_t)p.c << 8) | ((uint32_t)p.d << 15);
}
''', {**BASE_EXPECT, "must_match_any": [
        [r"__vm_il_extract", r"__vm_il_deposit", r"vm\.bytecode\b"],
    ]})


def cat_shells():
    write("09_shells", "test_nat_math", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    double a = (double)x + 0.3;
    double b = (double)y + 0.7;
    double r = ceil(a) + floor(b) + trunc(a * 0.5) + round(b * 0.25);
    return (uint32_t)(long)(r * 10.0) ^ x;
}
''', {**BASE_EXPECT, "must_match_any": [
        [r"__vm_nat\.", r"@ceil", r"@floor", r"@trunc", r"@round", r"llvm\.ceil", r"llvm\.floor"],
    ]})

    write("09_shells", "test_varargs_split", r'''
#include <stdarg.h>

{ANN}
uint32_t obf_sum(uint32_t n, ...) {
    va_list ap;
    va_start(ap, n);
    uint32_t s = 0;
    for (uint32_t i = 0; i < n; i++) s += va_arg(ap, uint32_t);
    va_end(ap);
    return s;
}

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    return obf_sum(4u, x, y, x ^ y, x + y);
}
''', {**BASE_EXPECT, "must_match_any": [
        [r"__vm_core_va_", r"vm\.bytecode\b"],
    ]})

    write("09_shells", "test_sret_odd_pair", r'''
typedef struct { uint32_t a; uint32_t b; } Pair32;

{ANN}
Pair32 obf_make(uint32_t x, uint32_t y) {
    Pair32 r = { x + 1u, y + 2u };
    return r;
}

{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    Pair32 p = obf_make(x, y);
    return p.a ^ p.b;
}
''', {**BASE_EXPECT, "must_match_any": [
        [r"__vm_core_sret_", r"__vm_sret_", r"vm\.bytecode\b"],
    ]})


def cat_superops():
    write("10_superops", "test_muladd", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t a = x + 1u, b = y + 2u, c = x ^ y ^ 3u;
    uint32_t p0 = a * b + c;
    uint32_t p1 = b * c + a;
    uint32_t p2 = c * a + b;
    return p0 ^ p1 ^ p2;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.muladd"]}, ann=ANN_SUPER)

    write("10_superops", "test_shladd", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t a = x, b = y & 7u, c = x ^ y;
    uint32_t p0 = (a << b) + c;
    uint32_t p1 = (c << (b ^ 1u)) + a;
    return p0 ^ p1;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.shladd"]}, ann=ANN_SUPER)

    write("10_superops", "test_cmpsel", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t t = x + y;
    uint32_t f = x ^ y;
    uint32_t r0 = (x < y) ? t : f;
    uint32_t r1 = (x == y) ? (t + 1u) : (f + 2u);
    return r0 ^ r1;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.cmpsel"]}, ann=ANN_SUPER)

    write("10_superops", "test_andcmpz", r'''
{ANN}
uint32_t obf_target(uint32_t x, uint32_t y) {
    uint32_t m0 = (x & y) == 0u;
    uint32_t m1 = (x & 0xFFu) != 0u;
    uint32_t m2 = ((x ^ y) & 0x80000000u) == 0u;
    return m0 + m1 * 2u + m2 * 4u + x + y;
}
''', {**BASE_EXPECT, "must_match": BASE_EXPECT["must_match"] + [r"vm\.opc\.andcmpz"]}, ann=ANN_SUPER)


def _ll_header() -> str:
    return (
        'target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"\n'
        'target triple = "x86_64-unknown-linux-gnu"\n'
        + ll_ann_globals()
    )


def write_odd_i_narrow():
    """i3/i5 leftover SSA (≤64 promote path)."""
    body = r'''
define i32 @obf_target(i32 %x, i32 %y) {
entry:
  %t3 = trunc i32 %x to i3
  %t5 = trunc i32 %y to i5
  %z3 = zext i3 %t3 to i32
  %z5 = zext i5 %t5 to i32
  %s3 = sext i3 %t3 to i32
  %add = add i32 %z3, %z5
  %xor = xor i32 %add, %s3
  ret i32 %xor
}
'''
    write_ll("08_legalize", "test_odd_i3_i5", _ll_header() + body + ll_main_boilerplate(), dict(BASE_EXPECT))


def write_odd_ssa_promote(width: int):
    """Pass-3 general ≤64 SSA: arith/logic/shift/div/icmp/select/mem."""
    ty = f"i{width}"
    body = f'''
define i32 @obf_target(i32 %x, i32 %y) {{
entry:
  %a = zext i32 %x to {ty}
  %b0 = zext i32 %y to {ty}
  %one = add {ty} %b0, 1
  %s = add {ty} %a, %one
  %d = sub {ty} %s, %a
  %m = mul {ty} %d, %one
  %xo = xor {ty} %m, %a
  %oa = or {ty} %xo, %a
  %an = and {ty} %oa, %m
  %sh = shl {ty} %an, 3
  %ls = lshr {ty} %sh, 1
  %as = ashr {ty} %ls, 1
  %q = udiv {ty} %as, %one
  %r = urem {ty} %q, %one
  %cmp = icmp ult {ty} %r, %a
  %sel = select i1 %cmp, {ty} %r, {ty} %a
  %p = alloca {ty}, align 8
  store {ty} %sel, ptr %p, align 8
  %ld = load {ty}, ptr %p, align 8
  %out = trunc {ty} %ld to i32
  ret i32 %out
}}
'''
    write_ll(
        "08_legalize",
        f"test_odd_i{width}_ssa",
        _ll_header() + body + ll_main_boilerplate(),
        dict(BASE_EXPECT),
    )


def write_odd_bitfield_wide(width: int):
    """Container i88/i104 over a byte buffer: extract + deposit → __vm_il_*.

    Seed with legal i32 stores (no zext-to-iN). Odd typed ops are only the
    load→lshr→and→trunc extract and store or(and(load,clear),shl) deposit.
    """
    ty = f"i{width}"
    nbytes = (width + 7) // 8
    field_mask = 0x7F
    clear = ((1 << width) - 1) ^ (field_mask << 8)
    body = f'''
define i32 @obf_target(i32 %x, i32 %y) {{
entry:
  %buf = alloca [{nbytes} x i8], align 16
  call void @llvm.memset.p0.i64(ptr %buf, i8 0, i64 {nbytes}, i1 false)
  store i32 %x, ptr %buf, align 4
  %p4 = getelementptr inbounds i8, ptr %buf, i64 4
  store i32 %y, ptr %p4, align 4

  ; --- extract bits [8..14] ---
  %ld0 = load {ty}, ptr %buf, align 16
  %sh0 = lshr {ty} %ld0, 8
  %and0 = and {ty} %sh0, {field_mask}
  %fld = trunc {ty} %and0 to i7
  %fld32 = zext i7 %fld to i32

  ; --- deposit new field from (x^y); and-mask required so peelInsert Width≤64 ---
  %ld1 = load {ty}, ptr %buf, align 16
  %cleared = and {ty} %ld1, {clear}
  %nv = xor i32 %x, %y
  %nv7 = trunc i32 %nv to i7
  %nvW = zext i7 %nv7 to {ty}
  %nvM = and {ty} %nvW, {field_mask}
  %ins = shl {ty} %nvM, 8
  %newv = or {ty} %cleared, %ins
  store {ty} %newv, ptr %buf, align 16

  %ld2 = load {ty}, ptr %buf, align 16
  %sh2 = lshr {ty} %ld2, 8
  %and2 = and {ty} %sh2, {field_mask}
  %fld2 = trunc {ty} %and2 to i7
  %fld232 = zext i7 %fld2 to i32
  %r = xor i32 %fld32, %fld232
  %r2 = add i32 %r, %x
  ret i32 %r2
}}

declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg)
'''
    expect = {
        "must_match": [r"vm\.bytecode\b", r"@__vm_engine\b"],
        "must_match_any": [[r"__vm_il_extract", r"__vm_il_deposit"]],
    }
    write_ll(
        "08_legalize",
        f"test_odd_i{width}_bitfield",
        _ll_header() + body + ll_main_boilerplate(),
        expect,
    )


def write_odd_int_ll():
    write_odd_i_narrow()
    # ≤64 and >64 containers via extract/deposit (runtime-proven on install)
    write_odd_bitfield_wide(40)
    write_odd_bitfield_wide(56)
    write_odd_bitfield_wide(88)
    write_odd_bitfield_wide(104)
    # Pass-3 SSA promote path (needs Impl dead-root scrub)
    write_odd_ssa_promote(40)
    write_odd_ssa_promote(56)


def build_coverage() -> dict:
    """Map every required OP_* / pattern / odd width → test id(s)."""
    # Each key lists tests that intentionally exercise it.
    opcodes: dict[str, list[str]] = {
        "OP_LOADI": ["01_int32/test_loadi"],
        "OP_BINOP": ["01_int32/test_binop_all"],
        "OP_ICMP": ["01_int32/test_icmp_select"],
        "OP_CAST": ["01_int32/test_cast"],
        "OP_SELECT": [
            "01_int32/test_icmp_select",
            "02_int64/test_icmp64_select",
            "06_ptr/test_icmp_ptr_select",
        ],
        "OP_RET_INT": ["01_int32/test_binop_all", "02_int64/test_binop64_all"],
        "OP_LOADI64": ["02_int64/test_loadi64"],
        "OP_BINOP64": ["02_int64/test_binop64_all"],
        "OP_CAST64": ["02_int64/test_cast64"],
        "OP_ICMP64": ["02_int64/test_icmp64_select"],
        "OP_JMP": ["03_control/test_jmp_jmpc"],
        "OP_JMPC": ["03_control/test_jmp_jmpc"],
        "OP_SWITCH": ["03_control/test_switch"],
        "OP_RET_VOID": ["03_control/test_ret_void_side"],
        "OP_LOAD8": ["04_memory/test_load_store_widths", "04_memory/test_i1_mem"],
        "OP_STORE8": ["04_memory/test_load_store_widths", "04_memory/test_i1_mem"],
        "OP_LOAD16": ["04_memory/test_load_store_widths"],
        "OP_STORE16": ["04_memory/test_load_store_widths"],
        "OP_LOAD32": ["04_memory/test_load_store_widths"],
        "OP_STORE32": ["04_memory/test_load_store_widths"],
        "OP_LOAD64": ["04_memory/test_load_store_widths"],
        "OP_STORE64": ["04_memory/test_load_store_widths"],
        "OP_LOADPTR": ["04_memory/test_load_store_ptr"],
        "OP_STOREPTR": ["04_memory/test_load_store_ptr"],
        "OP_GEP": ["04_memory/test_gep"],
        "OP_GEP64": ["04_memory/test_gep64"],
        "OP_LOADI_F": ["05_float/test_binop_f"],
        "OP_BINOP_F": ["05_float/test_binop_f"],
        "OP_FNEG": ["05_float/test_binop_f"],
        "OP_FCMP": ["05_float/test_fcmp_select_f"],
        "OP_SELECT_F": ["05_float/test_fcmp_select_f"],
        "OP_FCAST_FF": ["05_float/test_fcast"],
        "OP_FCAST_FV": ["05_float/test_fcast"],
        "OP_FCAST_FV64": ["05_float/test_fcast"],
        "OP_FCAST_VF": ["05_float/test_fcast"],
        "OP_FCAST_V64F": ["05_float/test_fcast"],
        "OP_LOAD_F": ["05_float/test_float_mem_f64"],
        "OP_STORE_F": ["05_float/test_float_mem_f64"],
        "OP_LOAD_F32": ["05_float/test_float_mem_f32"],
        "OP_STORE_F32": ["05_float/test_float_mem_f32"],
        "OP_RET_F": ["05_float/test_ret_f_via_bits"],
        "OP_PTRTOINT": ["06_ptr/test_ptrtoint_inttoptr"],
        "OP_PTRTOINT64": ["06_ptr/test_ptrtoint_inttoptr"],
        "OP_INTTOPTR": ["06_ptr/test_ptrtoint_inttoptr"],
        "OP_INTTOPTR64": ["06_ptr/test_ptrtoint_inttoptr"],
        "OP_ICMP_PTR": ["06_ptr/test_icmp_ptr_select"],
        "OP_RET_PTR": ["06_ptr/test_ret_ptr"],
        "OP_CALL_VOID": ["07_calls/test_call_int_void_ptr"],
        "OP_CALL_INT": ["07_calls/test_call_int_void_ptr", "07_calls/test_call_narrow"],
        "OP_CALL_PTR": ["07_calls/test_call_int_void_ptr"],
        "OP_CALL_INT64": ["07_calls/test_call_i64_f"],
        "OP_CALL_F": ["07_calls/test_call_i64_f"],
        "OP_CALL_PAIR": ["07_calls/test_call_pair"],
        "OP_MULADD": ["10_superops/test_muladd"],
        "OP_SHLADD": ["10_superops/test_shladd"],
        "OP_CMPSEL": ["10_superops/test_cmpsel"],
        "OP_ANDCMPZ": ["10_superops/test_andcmpz"],
    }
    patterns = {
        "LEGALIZE_MEM_EXPAND": ["08_legalize/test_mem_expand"],
        "LEGALIZE_SWITCH_NON_I32": ["08_legalize/test_switch_i16"],
        "LEGALIZE_AGG_LOAD": ["08_legalize/test_agg_load"],
        "LEGALIZE_PHI_DEMOTE": ["08_legalize/test_phi_demote"],
        "LEGALIZE_ODD_SSA": [
            "08_legalize/test_odd_i3_i5",
            "08_legalize/test_odd_i40_ssa",
            "08_legalize/test_odd_i56_ssa",
            "08_legalize/test_odd_bitfield",
        ],
        "LEGALIZE_ODD_BITFIELD": [
            "08_legalize/test_odd_bitfield",
            "08_legalize/test_odd_i40_bitfield",
            "08_legalize/test_odd_i56_bitfield",
            "08_legalize/test_odd_i88_bitfield",
            "08_legalize/test_odd_i104_bitfield",
        ],
        "SHELL_VARARGS": ["09_shells/test_varargs_split"],
        "SHELL_SRET": ["09_shells/test_sret_odd_pair"],
        "SHELL_NAT": ["09_shells/test_nat_math"],
    }
    odd_widths = {
        "3": ["08_legalize/test_odd_i3_i5"],
        "5": ["08_legalize/test_odd_i3_i5"],
        "40": [
            "08_legalize/test_odd_i40_bitfield",
            "08_legalize/test_odd_i40_ssa",
        ],
        "56": [
            "08_legalize/test_odd_i56_bitfield",
            "08_legalize/test_odd_i56_ssa",
        ],
        "88": ["08_legalize/test_odd_i88_bitfield"],
        "104": ["08_legalize/test_odd_i104_bitfield"],
    }
    return {
        "opcodes": opcodes,
        "patterns": patterns,
        "odd_widths": odd_widths,
        "dead_opcodes": ["OP_MOVR", "OP_MOVR_F"],
        "tests": sorted(WRITTEN),
    }


def main():
    if ROOT.exists():
        shutil.rmtree(ROOT)
    ROOT.mkdir(parents=True, exist_ok=True)
    WRITTEN.clear()

    cat_int32()
    cat_int64()
    cat_control()
    cat_memory()
    cat_float()
    cat_ptr()
    cat_calls()
    cat_legalize()
    cat_shells()
    cat_superops()
    write_odd_int_ll()

    cov = build_coverage()
    # Every coverage-claimed test must have been written.
    claimed: set[str] = set()
    for m in (cov["opcodes"], cov["patterns"], cov["odd_widths"]):
        for tests in m.values():
            claimed.update(tests)
    missing = sorted(claimed - set(WRITTEN))
    if missing:
        raise SystemExit(f"coverage claims tests that were not generated: {missing}")

    (ROOT / "COVERAGE.json").write_text(json.dumps(cov, indent=2) + "\n", encoding="utf-8")
    print(f"generated {len(WRITTEN)} tests under {ROOT}")


if __name__ == "__main__":
    main()
