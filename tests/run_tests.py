#!/usr/bin/env python3
"""Test harness for the Lean MessagePack codec.

Three layers, all settled against independent expectations:

1. Fixed cases: one value of every family and every width, the
   integer boundaries on both sides of every width step with
   their exact canonical bytes, the same values carried in wider
   forms than they need, and the length forms at their steps.

2. A differential against a strict oracle written here from the
   specification (plain byte code): random values in all
   families are encoded by the oracle, read by the Lean tool,
   and the answer must be the canonical reprint. Random values
   are also encoded in wider forms than they need and must read
   back to the canonical form.

3. A differential against Python's `msgpack` library when it is
   importable: its `packb` output is checked against the
   oracle's canonical bytes and fed to the Lean tool, and the
   oracle's canonical bytes are checked through its `unpackb`.
   When the library is absent, the run says so and the oracle
   carries accept and reject alone.

Mutations of one nested value (truncation at every length, the
never used marker 0xc1 at every position, byte flips at every
position, and crafted length overruns) are settled by comparing
the Lean answer with the oracle's answer on the same bytes.

Results are written to tests/TEST-RESULTS.md. Seed 20261026.

Usage: python3 tests/run_tests.py [--skip-build]
Run it with an interpreter that has `msgpack` installed to get
the library differential; without it that part is skipped and
the results file says so.
"""

import os
import random
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EXE = os.path.join(ROOT, ".lake", "build", "bin", "messagepack")
SEED = 20261026
MAXU64 = (1 << 64) - 1
MINI64 = -(1 << 63)

failures = []


def check(cond, label, detail=""):
    if not cond:
        failures.append(f"{label}: {detail}")
        print(f"FAIL {label}: {detail}")


# ---------------------------------------------------------------------------
# Batch runner: one process for many requests.
# ---------------------------------------------------------------------------

class Tool:
    def __init__(self):
        self.lines = []

    def ask(self, line):
        self.lines.append(line)
        return len(self.lines) - 1

    def run(self):
        proc = subprocess.run([EXE], input="\n".join(self.lines) + "\n",
                              capture_output=True, text=True, timeout=1200)
        if proc.returncode != 0:
            raise RuntimeError(f"tool exited {proc.returncode}: {proc.stderr[:500]}")
        self.answers = proc.stdout.splitlines()
        if len(self.answers) != len(self.lines):
            raise RuntimeError(
                f"answer count {len(self.answers)} != request count {len(self.lines)}")
        return self.answers


def req(bs):
    return "parse " + ",".join(str(b) for b in bs)


def want_ok(canon):
    return "ok:" + ",".join(str(b) for b in canon)


# ---------------------------------------------------------------------------
# Value representation in the harness:
#   ("nil",) ("bool", b) ("int", n) ("f32", pattern) ("f64", pattern)
#   ("str", bytes) ("bin", bytes) ("arr", [v...])
#   ("map", [(k, v)...]) ("ext", code, bytes)
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Oracle: canonical encoder (with optional wider forms) and strict decoder,
# written from the specification.
# ---------------------------------------------------------------------------

INT_FORMS = [
    # (name, marker or None for fix forms, width, min, max)
    ("u8", 0xCC, 1, 0, 0xFF),
    ("u16", 0xCD, 2, 0, 0xFFFF),
    ("u32", 0xCE, 4, 0, 0xFFFFFFFF),
    ("u64", 0xCF, 8, 0, MAXU64),
    ("i8", 0xD0, 1, -128, 127),
    ("i16", 0xD1, 2, -32768, 32767),
    ("i32", 0xD2, 4, -(1 << 31), (1 << 31) - 1),
    ("i64", 0xD3, 8, MINI64, -MINI64 - 1),
]


def enc_int_canonical(n):
    if 0 <= n <= 127:
        return bytes([n])
    if -32 <= n < 0:
        return bytes([n + 256])
    if n >= 0:
        for _, marker, w, _, hi in INT_FORMS[:4]:
            if n <= hi:
                return bytes([marker]) + n.to_bytes(w, "big")
    else:
        for _, marker, w, lo, _ in INT_FORMS[4:]:
            if lo <= n:
                return bytes([marker]) + (n % (1 << (8 * w))).to_bytes(w, "big")
    raise ValueError(n)


def enc_int_form(n, form):
    name, marker, w, lo, hi = form
    assert lo <= n <= hi, (n, name)
    return bytes([marker]) + (n % (1 << (8 * w))).to_bytes(w, "big")


def valid_int_forms(n):
    out = []
    if 0 <= n <= 127:
        out.append("posfix")
    if -32 <= n < 0:
        out.append("negfix")
    for form in INT_FORMS:
        if form[3] <= n <= form[4]:
            out.append(form[0])
    return out


def len_forms(fix_base, fix_bits, markers, length):
    """Every header form that holds this length, smallest first.
    `markers` is the family's (marker, width) list; the fix form
    comes first when the family has one and the length fits."""
    forms = []
    if fix_base is not None and length < (1 << fix_bits):
        forms.append(bytes([fix_base + length]))
    for marker, w in markers:
        if length <= (1 << (8 * w)) - 1:
            forms.append(bytes([marker]) + length.to_bytes(w, "big"))
    return forms


def pick(forms, rng=None, widen=False):
    if widen and rng is not None:
        return rng.choice(forms)
    return forms[0]


def enc_value(v, rng=None, widen=False):
    tag = v[0]
    if tag == "nil":
        return b"\xc0"
    if tag == "bool":
        return b"\xc3" if v[1] else b"\xc2"
    if tag == "int":
        n = v[1]
        if widen and rng is not None:
            form = rng.choice(valid_int_forms(n))
            if form == "posfix":
                return bytes([n])
            if form == "negfix":
                return bytes([n + 256])
            return enc_int_form(n, next(f for f in INT_FORMS if f[0] == form))
        return enc_int_canonical(n)
    if tag == "f32":
        return b"\xca" + v[1].to_bytes(4, "big")
    if tag == "f64":
        return b"\xcb" + v[1].to_bytes(8, "big")
    if tag == "str":
        head = pick(len_forms(0xA0, 5, [(0xD9, 1), (0xDA, 2), (0xDB, 4)],
                              len(v[1])), rng, widen)
        return head + v[1]
    if tag == "bin":
        head = pick(len_forms(None, 0, [(0xC4, 1), (0xC5, 2), (0xC6, 4)],
                              len(v[1])), rng, widen)
        return head + v[1]
    if tag == "arr":
        head = pick(len_forms(0x90, 4, [(0xDC, 2), (0xDD, 4)],
                              len(v[1])), rng, widen)
        return head + b"".join(enc_value(x, rng, widen) for x in v[1])
    if tag == "map":
        head = pick(len_forms(0x80, 4, [(0xDE, 2), (0xDF, 4)],
                              len(v[1])), rng, widen)
        return head + b"".join(
            enc_value(k, rng, widen) + enc_value(x, rng, widen) for k, x in v[1])
    if tag == "ext":
        code, data = v[1], v[2]
        tb = bytes([code % 256])
        n = len(data)
        fixed = {1: 0xD4, 2: 0xD5, 4: 0xD6, 8: 0xD7, 16: 0xD8}
        use_fix = n in fixed and not (widen and rng is not None and rng.random() < 0.5)
        if use_fix:
            return bytes([fixed[n]]) + tb + data
        if n <= 0xFF:
            return b"\xc7" + n.to_bytes(1, "big") + tb + data
        if n <= 0xFFFF:
            return b"\xc8" + n.to_bytes(2, "big") + tb + data
        return b"\xc9" + n.to_bytes(4, "big") + tb + data
    raise ValueError(tag)


class Reject(Exception):
    pass


def dec_at(bs, i):
    if i >= len(bs):
        raise Reject()
    m = bs[i]
    i += 1
    if m <= 0x7F:
        return ("int", m), i
    if 0x80 <= m <= 0x8F:
        return dec_seq(bs, i, m - 0x80, True)
    if 0x90 <= m <= 0x9F:
        return dec_seq(bs, i, m - 0x90, False)
    if 0xA0 <= m <= 0xBF:
        return dec_bytes(bs, i, m - 0xA0, "str")
    if m == 0xC0:
        return ("nil",), i
    if m == 0xC1:
        raise Reject()
    if m == 0xC2:
        return ("bool", False), i
    if m == 0xC3:
        return ("bool", True), i
    if m in (0xC4, 0xC5, 0xC6):
        w = 1 << (m - 0xC4)
        ln, i = dec_uint(bs, i, w)
        return dec_bytes(bs, i, ln, "bin")
    if m in (0xC7, 0xC8, 0xC9):
        w = 1 << (m - 0xC7)
        ln, i = dec_uint(bs, i, w)
        return dec_ext(bs, i, ln)
    if m == 0xCA:
        p, i = dec_uint(bs, i, 4)
        return ("f32", p), i
    if m == 0xCB:
        p, i = dec_uint(bs, i, 8)
        return ("f64", p), i
    if 0xCC <= m <= 0xCF:
        w = 1 << (m - 0xCC)
        u, i = dec_uint(bs, i, w)
        return ("int", u), i
    if 0xD0 <= m <= 0xD3:
        w = 1 << (m - 0xD0)
        u, i = dec_uint(bs, i, w)
        return ("int", u - (1 << (8 * w)) if u >= (1 << (8 * w - 1)) else u), i
    if 0xD4 <= m <= 0xD8:
        ln = (1, 2, 4, 8, 16)[m - 0xD4]
        return dec_ext(bs, i, ln)
    if m in (0xD9, 0xDA, 0xDB):
        w = 1 << (m - 0xD9)
        ln, i = dec_uint(bs, i, w)
        return dec_bytes(bs, i, ln, "str")
    if m in (0xDC, 0xDD):
        w = 2 << (m - 0xDC)
        cnt, i = dec_uint(bs, i, w)
        return dec_seq(bs, i, cnt, False)
    if m in (0xDE, 0xDF):
        w = 2 << (m - 0xDE)
        cnt, i = dec_uint(bs, i, w)
        return dec_seq(bs, i, cnt, True)
    if m >= 0xE0:
        return ("int", m - 256), i
    raise Reject()


def dec_uint(bs, i, w):
    if i + w > len(bs):
        raise Reject()
    return int.from_bytes(bs[i:i + w], "big"), i + w


def dec_bytes(bs, i, ln, tag):
    if i + ln > len(bs):
        raise Reject()
    return (tag, bytes(bs[i:i + ln])), i + ln


def dec_ext(bs, i, ln):
    if i + 1 + ln > len(bs):
        raise Reject()
    tb = bs[i]
    code = tb - 256 if tb >= 128 else tb
    return ("ext", code, bytes(bs[i + 1:i + 1 + ln])), i + 1 + ln


def dec_seq(bs, i, cnt, is_map):
    out = []
    if is_map:
        for _ in range(cnt):
            k, i = dec_at(bs, i)
            x, i = dec_at(bs, i)
            out.append((k, x))
        return ("map", out), i
    for _ in range(cnt):
        x, i = dec_at(bs, i)
        out.append(x)
    return ("arr", out), i


def oracle_parse(bs):
    try:
        v, i = dec_at(bs, 0)
    except Reject:
        return None
    if i != len(bs):
        return None
    return v


# ---------------------------------------------------------------------------
# Random values. The full pool is oracle only. The msgpack pool is the part
# the Python library can express: ascii strings, real floats (float64),
# extension codes 0 to 127, scalar map keys.
# ---------------------------------------------------------------------------

INT_EDGES = [0, 1, 2, 31, 32, 63, 64, 100, 127, 128, 200, 255, 256, 1000,
             65535, 65536, 70000, (1 << 32) - 1, 1 << 32, (1 << 40),
             (1 << 63) - 1, 1 << 63, MAXU64,
             -1, -2, -31, -32, -33, -100, -128, -129, -1000,
             -32768, -32769, -(1 << 31), -(1 << 31) - 1, MINI64]


def rand_int(rng):
    r = rng.random()
    if r < 0.45:
        return rng.choice(INT_EDGES)
    if r < 0.65:
        return rng.randint(-200, 300)
    if r < 0.85:
        return rng.randint(-(1 << 31), 1 << 32)
    return rng.randint(MINI64, MAXU64)


def rand_bytes(rng, n):
    return bytes(rng.randrange(256) for _ in range(n))


def gen_value(rng, depth, mp):
    choices = ["nil", "bool", "int", "f64", "str", "bin", "ext"]
    if not mp:
        choices += ["f32", "f64pat"]
    if depth < 3:
        choices += ["arr", "map", "arr", "map"]
    tag = rng.choice(choices)
    if tag == "nil":
        return ("nil",)
    if tag == "bool":
        return ("bool", rng.random() < 0.5)
    if tag == "int":
        return ("int", rand_int(rng))
    if tag == "f32":
        return ("f32", rng.randrange(1 << 32))
    if tag == "f64pat":
        return ("f64", rng.randrange(1 << 64))
    if tag == "f64":
        x = rng.choice([0.0, 1.0, -1.5, 3.141592653589793, 1e300, -1e-300,
                        rng.uniform(-1e6, 1e6), rng.uniform(-1, 1)])
        return ("f64", struct.unpack(">Q", struct.pack(">d", x))[0])
    if tag == "str":
        n = rng.choice([0, 1, 3, 5, 20, 31, 32, 33, 100, 255, 256])
        if mp:
            return ("str", bytes(rng.choice(b"abcdefghij _-.")
                                 for _ in range(n)))
        return ("str", rand_bytes(rng, n))
    if tag == "bin":
        n = rng.choice([0, 1, 2, 7, 40, 255, 256])
        return ("bin", rand_bytes(rng, n))
    if tag == "ext":
        n = rng.choice([0, 1, 2, 3, 4, 5, 8, 16, 17, 40])
        code = rng.randrange(0, 128) if mp else rng.randint(-128, 127)
        return ("ext", code, rand_bytes(rng, n))
    if tag == "arr":
        n = rng.choice([0, 1, 2, 3, 5, 15, 16, 17])
        return ("arr", [gen_value(rng, depth + 1, mp) for _ in range(n)])
    if tag == "map":
        n = rng.choice([0, 1, 2, 3, 15, 16])
        pairs = []
        if mp:
            seen = set()
            for _ in range(n):
                while True:
                    kt = rng.choice(["int", "str", "bool", "nil"])
                    if kt == "int":
                        # 0 and 1 stay out: as Python dict keys they
                        # would collide with False and True.
                        k = ("int", rng.randrange(2, 1000))
                    elif kt == "str":
                        k = ("str", bytes(rng.choice(b"keyabc")
                                          for _ in range(rng.randrange(1, 5))))
                    elif kt == "bool":
                        k = ("bool", rng.random() < 0.5)
                    else:
                        k = ("nil",)
                    if k not in seen:
                        seen.add(k)
                        break
                pairs.append((k, gen_value(rng, depth + 1, mp)))
        else:
            for _ in range(n):
                pairs.append((gen_value(rng, depth + 1, mp),
                              gen_value(rng, depth + 1, mp)))
        return ("map", pairs)
    raise ValueError(tag)


# ---------------------------------------------------------------------------
# msgpack pool conversion.
# ---------------------------------------------------------------------------

def to_py(v):
    tag = v[0]
    if tag == "nil":
        return None
    if tag == "bool":
        return v[1]
    if tag == "int":
        return v[1]
    if tag == "f64":
        return struct.unpack(">d", struct.pack(">Q", v[1]))[0]
    if tag == "f32":
        return struct.unpack(">f", struct.pack(">I", v[1]))[0]
    if tag == "str":
        return v[1].decode("utf-8")
    if tag == "bin":
        return v[1]
    if tag == "arr":
        return [to_py(x) for x in v[1]]
    if tag == "map":
        return {to_py(k): to_py(x) for k, x in v[1]}
    if tag == "ext":
        import msgpack
        return msgpack.ExtType(v[1], v[2])
    raise ValueError(tag)


# ---------------------------------------------------------------------------
# Test sections.
# ---------------------------------------------------------------------------

def fixed_cases():
    tool = Tool()
    cases = []  # (label, input bytes, expected answer)
    spec_values = [
        ("nil", ("nil",), bytes([0xC0])),
        ("false", ("bool", False), bytes([0xC2])),
        ("true", ("bool", True), bytes([0xC3])),
        ("pos fixint 0", ("int", 0), bytes([0x00])),
        ("pos fixint 42", ("int", 42), bytes([0x2A])),
        ("string abc", ("str", b"abc"), bytes([0xA3, 0x61, 0x62, 0x63])),
        ("empty string", ("str", b""), bytes([0xA0])),
        ("empty array", ("arr", []), bytes([0x90])),
        ("empty map", ("map", []), bytes([0x80])),
        ("float32 1.0", ("f32", 1065353216), bytes([0xCA, 0x3F, 0x80, 0, 0])),
        ("float64 1.0", ("f64", 4607182418800017408),
         bytes([0xCB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0])),
        ("bin 8", ("bin", b"\x01\x02"), bytes([0xC4, 2, 1, 2])),
        ("ext fixext1", ("ext", 5, b"\xaa"), bytes([0xD4, 5, 0xAA])),
        ("ext fixext1 code -1", ("ext", -1, b"\xaa"), bytes([0xD4, 0xFF, 0xAA])),
        ("nested", ("arr", [("int", 1),
                            ("map", [(("str", b"a"), ("bool", True))])]),
         bytes([0x92, 0x01, 0x81, 0xA1, 0x61, 0xC3])),
    ]
    for label, v, bs in spec_values:
        check(enc_value(v) == bs, f"fixed/{label}",
              "oracle canonical bytes differ from the spec bytes")
        cases.append((label, bs, want_ok(enc_value(v))))
    # one of every integer width, canonical
    width_cases = [
        ("uint8 200", 200, bytes([0xCC, 200])),
        ("uint16 1000", 1000, bytes([0xCD, 0x03, 0xE8])),
        ("uint32 70000", 70000, bytes([0xCE, 0, 1, 0x11, 0x70])),
        ("uint64 2^40", 1 << 40, bytes([0xCF, 0, 0, 1, 0, 0, 0, 0, 0])),
        ("int8 -100", -100, bytes([0xD0, 0x9C])),
        ("int16 -1000", -1000, bytes([0xD1, 0xFC, 0x18])),
        ("int32 -70000", -70000, bytes([0xD2, 0xFF, 0xFE, 0xEE, 0x90])),
        ("int64 -2^40", -(1 << 40),
         bytes([0xD3, 0xFF, 0xFF, 0xFF, 0, 0, 0, 0, 0])),
    ]
    for label, n, bs in width_cases:
        check(enc_value(("int", n)) == bs, f"fixed/{label}",
              "oracle canonical bytes differ from the width bytes")
        cases.append((label, bs, want_ok(bs)))
    # one of every remaining width form
    form_cases = [
        ("bin16", ("bin", bytes(300)), None),
        ("bin32", None, bytes([0xC6, 0, 0, 0, 2, 9, 9])),
        ("str8", ("str", b"x" * 40), None),
        ("str16", ("str", b"y" * 300), None),
        ("str32", None, bytes([0xDB, 0, 0, 0, 3]) + b"abc"),
        ("array16", ("arr", [("int", 1)] * 16), None),
        ("array32", None, bytes([0xDD, 0, 0, 0, 1, 7])),
        ("map16", ("map", [(("int", i), ("int", i)) for i in range(16)]), None),
        ("map32", None, bytes([0xDF, 0, 0, 0, 1, 1, 2])),
        ("ext8 len 3", ("ext", 9, b"abc"), None),
        ("ext16", None, bytes([0xC8, 0, 3, 9]) + b"abc"),
        ("ext32", None, bytes([0xC9, 0, 0, 0, 2, 9]) + b"ab"),
        ("fixext2", ("ext", 3, b"ab"), bytes([0xD5, 3]) + b"ab"),
        ("fixext4", ("ext", 3, b"abcd"), bytes([0xD6, 3]) + b"abcd"),
        ("fixext8", ("ext", 3, bytes(8)), bytes([0xD7, 3]) + bytes(8)),
        ("fixext16", ("ext", 3, bytes(16)), bytes([0xD8, 3]) + bytes(16)),
    ]
    for label, v, bs in form_cases:
        if v is not None:
            bs_in = enc_value(v)
        else:
            bs_in = bs
            v = oracle_parse(bs_in)
            check(v is not None, f"fixed/{label}", "oracle cannot read its bytes")
        cases.append((label, bs_in, want_ok(enc_value(v))))
    for label, bs, expected in cases:
        idx = tool.ask(req(bs))
        cases[cases.index((label, bs, expected))] = (label, bs, expected, idx)
    answers = tool.run()
    for label, bs, expected, idx in cases:
        check(answers[idx] == expected, f"fixed/{label}",
              f"input {list(bs)}: got {answers[idx]}, want {expected}")
    return len(cases)


def boundary_cases():
    tool = Tool()
    entries = []
    bounds = [127, 128, 255, 256, 65535, 65536, (1 << 32) - 1, 1 << 32,
              MAXU64, -1, -32, -33, -128, -129, -32768, -32769,
              -(1 << 31), -(1 << 31) - 1, MINI64]
    for n in bounds:
        canon = enc_int_canonical(n)
        idx = tool.ask(req(canon))
        entries.append((f"boundary canonical {n}", idx, want_ok(canon)))
        for form in valid_int_forms(n):
            if form in ("posfix", "negfix"):
                continue
            f = next(x for x in INT_FORMS if x[0] == form)
            wide = enc_int_form(n, f)
            if wide == canon:
                continue
            idx = tool.ask(req(wide))
            entries.append((f"boundary {n} in {form}", idx, want_ok(canon)))
    # length form steps
    len_steps = [
        ("str 31", ("str", b"s" * 31)), ("str 32", ("str", b"s" * 32)),
        ("str 255", ("str", b"s" * 255)), ("str 256", ("str", b"s" * 256)),
        ("bin 255", ("bin", bytes(255))), ("bin 256", ("bin", bytes(256))),
        ("array 15", ("arr", [("nil",)] * 15)),
        ("array 16", ("arr", [("nil",)] * 16)),
        ("map 15", ("map", [(("nil",), ("nil",))] * 15)),
        ("map 16", ("map", [(("int", i), ("nil",)) for i in range(16)])),
    ]
    for label, v in len_steps:
        canon = enc_value(v)
        idx = tool.ask(req(canon))
        entries.append((f"length {label}", idx, want_ok(canon)))
    answers = tool.run()
    for label, idx, expected in entries:
        check(answers[idx] == expected, f"boundary/{label}",
              f"got {answers[idx]}, want {expected}")
    return len(entries)


def oracle_differential(rng, count):
    tool = Tool()
    entries = []
    for _ in range(count):
        v = gen_value(rng, 0, mp=False)
        canon = enc_value(v)
        widen = rng.random() < 0.5
        bs = enc_value(v, rng, widen) if widen else canon
        idx = tool.ask(req(bs))
        entries.append((idx, want_ok(canon), list(bs)))
    answers = tool.run()
    agree = 0
    for idx, expected, bs in entries:
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, "oracle differential",
                  f"input {bs[:60]}: got {answers[idx]}, want {expected}")
    return len(entries), agree


def msgpack_differential(rng, count):
    import msgpack
    tool = Tool()
    entries = []
    named = []
    agree = 0
    for _ in range(count):
        v = gen_value(rng, 0, mp=True)
        py = to_py(v)
        packed = msgpack.packb(py, use_bin_type=True)
        canon = enc_value(v)
        if bytes(packed) != canon:
            named.append(
                f"packb bytes differ for {v[0]}: {list(packed)[:40]} "
                f"vs canonical {list(canon)[:40]}")
            check(False, "msgpack canonical", named[-1])
            continue
        back = msgpack.unpackb(canon, raw=False, strict_map_key=False)
        check(back == py or (isinstance(py, float) and back == py),
              "msgpack unpackb", f"value level mismatch for {v[0]}")
        idx = tool.ask(req(bytes(packed)))
        entries.append((idx, want_ok(canon), list(packed)))
    answers = tool.run()
    for idx, expected, bs in entries:
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, "msgpack differential",
                  f"input {bs[:60]}: got {answers[idx]}, want {expected}")
    return len(entries), agree, named


def mutation_cases(rng):
    nested = ("arr", [
        ("int", 300),
        ("str", b"hello"),
        ("map", [(("int", 1), ("arr", [("bool", True), ("nil",)])),
                 (("str", b"k"), ("bin", b"\x01\x02"))]),
        ("ext", -3, b"\x09\x08\x07\x06"),
        ("f64", 4609434218613702656),  # 1.5
        ("int", -1000),
    ])
    nb = enc_value(nested)
    tool = Tool()
    entries = []

    def settle(label, bs):
        v = oracle_parse(bs)
        expected = want_ok(enc_value(v)) if v is not None else "none"
        idx = tool.ask(req(bs))
        entries.append((label, idx, expected))

    for cut in range(len(nb)):
        settle(f"truncate {cut}", nb[:cut])
    for off in range(len(nb)):
        mut = nb[:off] + b"\xc1" + nb[off + 1:]
        settle(f"c1 at {off}", bytes(mut))
    for off in range(len(nb)):
        mut = bytearray(nb)
        mut[off] = (mut[off] + 1) % 256
        settle(f"flip +1 at {off}", bytes(mut))
        mut2 = bytearray(nb)
        mut2[off] = 0
        settle(f"flip 0 at {off}", bytes(mut2))
    overruns = [
        ("str8 claims 10, has 3", bytes([0xD9, 10]) + b"abc"),
        ("bin16 claims 256, has 2", bytes([0xC5, 1, 0, 9, 9])),
        ("array16 claims 5, has 2", bytes([0xDC, 0, 5, 1, 2])),
        ("map32 claims 2^32-1", bytes([0xDF, 255, 255, 255, 255])),
        ("ext8 claims 9, has 2", bytes([0xC7, 9, 5, 1, 2])),
        ("str32 claims 2^32-1", bytes([0xDB, 255, 255, 255, 255])),
        ("uint16 cut", bytes([0xCD])),
        ("uint64 cut", bytes([0xCF, 1, 2, 3])),
        ("int64 cut", bytes([0xD3, 0x80])),
        ("fixext4 cut", bytes([0xD6, 5, 1, 2])),
        ("array count runs out", bytes([0x93, 1, 2])),
        ("lone c1", bytes([0xC1])),
        ("c1 inside array", bytes([0x92, 1, 0xC1])),
        ("empty input", b""),
        ("trailing byte", bytes([0x01, 0x02])),
    ]
    for label, bs in overruns:
        idx = tool.ask(req(bs))
        entries.append((label, idx, "none"))
        check(oracle_parse(bs) is None, f"mutation/{label}",
              "oracle reads an overrun case")
    answers = tool.run()
    agree = 0
    for label, idx, expected in entries:
        if answers[idx] == expected:
            agree += 1
        else:
            check(False, f"mutation/{label}",
                  f"got {answers[idx]}, want {expected}")
    return len(entries), agree


def protocol_cases():
    lines = ["parse 192", "parse", "parse 01", "parse 256", "parse 1,2",
             "bogus 1", "parse 1 2", "Parse 192", "parse 0", ""]
    expected = ["ok:192", "none", "error", "error", "none",
                "error", "error", "error", "ok:0"]
    proc = subprocess.run([EXE], input="\n".join(lines) + "\n",
                          capture_output=True, text=True, timeout=120)
    got = proc.stdout.splitlines()
    check(got == expected, "protocol", f"got {got}, want {expected}")
    return len(expected)


# ---------------------------------------------------------------------------

def main():
    if "--skip-build" not in sys.argv:
        subprocess.run(["lake", "build"], cwd=ROOT, check=True,
                       capture_output=True, text=True, timeout=1200)
    rng = random.Random(SEED)
    sections = []

    n_fixed = fixed_cases()
    sections.append(("Fixed cases from the spec (every family and width)",
                     n_fixed, n_fixed))
    n_bounds = boundary_cases()
    sections.append(("Integer width boundaries and length form steps",
                     n_bounds, n_bounds))

    n_or, a_or = oracle_differential(rng, 3000)
    sections.append(("Oracle differential, random values (seed 20261026)",
                     n_or, a_or))

    try:
        import msgpack
        mp_version = ".".join(str(x) for x in msgpack.version)
        mp_present = True
    except ImportError:
        mp_present = False
        mp_version = None
    named = []
    if mp_present:
        n_mp, a_mp, named = msgpack_differential(rng, 2000)
        sections.append((f"msgpack {mp_version} differential (packb and unpackb)",
                         n_mp, a_mp))
    n_mut, a_mut = mutation_cases(rng)
    sections.append(("Mutations of one nested value, settled by the oracle",
                     n_mut, a_mut))
    n_proto = protocol_cases()
    sections.append(("Line protocol cases", n_proto, n_proto))

    failed = len(failures)
    lines = []
    lines.append("# Test results: messagepack")
    lines.append("")
    lines.append(f"Seed: {SEED}. Tool: the Lean command line program, "
                 "one process per section, requests batched.")
    lines.append("")
    if mp_present:
        lines.append(f"Python's `msgpack` library was importable in the "
                     f"interpreter that ran this harness (version "
                     f"{mp_version}); the library differential ran.")
    else:
        lines.append("Python's `msgpack` library was NOT importable in "
                     "the interpreter that ran this harness; the library "
                     "differential did not run, and the strict oracle "
                     "carried accept and reject alone.")
    lines.append("")
    lines.append("| Section | Inputs | Agreements |")
    lines.append("| --- | --- | --- |")
    for name, total, agree in sections:
        lines.append(f"| {name} | {total} | {agree} |")
    lines.append("")
    if not mp_present:
        lines.append("Named differences from the msgpack library: not "
                     "applicable, the library did not run.")
    elif named:
        lines.append("Named differences from the msgpack library:")
        for d in named[:20]:
            lines.append(f"- {d}")
    else:
        lines.append("Named differences from the msgpack library: none. "
                     "Its `packb` bytes matched the canonical bytes on "
                     "every value it was given, and `unpackb` read the "
                     "canonical bytes back to the same values.")
    lines.append("")
    if failed:
        lines.append(f"Failures: {failed}.")
        for f in failures[:40]:
            lines.append(f"- {f}")
    else:
        lines.append("Failures: none.")
    lines.append("")
    with open(os.path.join(HERE, "TEST-RESULTS.md"), "w") as fh:
        fh.write("\n".join(lines))
    total = sum(t for _, t, _ in sections)
    agree = sum(a for _, _, a in sections)
    print(f"sections={len(sections)} inputs={total} agreements={agree} "
          f"failures={failed} msgpack={'yes ' + mp_version if mp_present else 'no'}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
