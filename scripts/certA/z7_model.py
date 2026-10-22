"""Untrusted Python model of the Lean A-certificate algorithm for Z7 (`ZetaIrrational/Z7/CertA/Defs.lean`).

It mirrors the Lean definitions exactly (offsets, residues, the per-candidate closed form, events, rounding) and is
used only to check the design against `handoff/zeta7/f4_certA_exact.py` before the kernel run.
Usage: python z7_model.py [check N | total]
"""
import sys
from fractions import Fraction as Fr
from math import floor, ceil

BLOCKS = [(d, 1) for d in range(1, 19)]          # (d, m): delta = d/80
G = Fr(547, 120)
OFFS = [0, -220, 240, 460] + [s for d, _ in BLOCKS for s in (3 * d, 240 - 3 * d)]


def qr(P, Q, s):
    B = s * P
    M = 240 * Q
    return B // M, B % M                          # floor division, as Int.ediv/emod for M > 0


def estar_int(x):
    P, Q = x.numerator, x.denominator
    qX, rX = P // Q, 240 * (P % Q)
    pre = [(m, qr(P, Q, 3 * d), qr(P, Q, 240 - 3 * d)) for d, m in BLOCKS]
    qn, q240, q460 = qr(P, Q, -220), qr(P, Q, 240), qr(P, Q, 460)
    best = 0
    for s in OFFS:
        ri = qr(P, Q, s)[1]
        for right in (False, True):
            eb = lambda r: 1 if right else (0 if ri == r else 1)
            lt = lambda r: 1 if ri < r else 0
            T = sum(m * (1 + (-qa - lt(ra)) - (-qb - lt(rb) + eb(rb))) for m, (qa, ra), (qb, rb) in pre)
            c = 5 * (-qn[0] - lt(qn[1])) + 5 * ((-q240[0] - lt(q240[1]) + eb(q240[1])) - (-q460[0] - lt(q460[1]) + eb(q460[1])))
            V = T - c
            cond = (ri < rX) if right else (ri <= rX)
            kmax = qX - (0 if cond else 1)
            has1 = any(m > 0 and max(1, qa + lt(ra)) <= qb + lt(rb) - eb(rb) and max(1, qa + lt(ra)) <= kmax
                       for m, (qa, ra), (qb, rb) in pre)
            S0 = sum(m for m, (qa, ra), (qb, rb) in pre if (-qa - lt(ra)) >= 0 and (-qb - lt(rb) + eb(rb)) <= 0)
            v0 = 0 if S0 == 0 else (V - 1 if T - S0 >= 1 else 0)
            v1 = V + 4 if has1 else 0
            best = max(best, v0, v1)
    return best


def estar(x):
    return estar_int(x) - G * floor(x)


FAMS = sorted({Fr(0), Fr(-11, 12), Fr(1), Fr(23, 12)} | {Fr(d, 80) for d, _ in BLOCKS} | {1 - Fr(d, 80) for d, _ in BLOCKS})


def events(X=400):
    cuts = [1 + Fr(j, 20) for j in range(40)] + [3 + Fr(j, 2) for j in range(2 * (X - 3) + 1)]
    ev = set(cuts)
    for s1 in FAMS:
        for s2 in FAMS:
            if s2 < s1:
                ds = s1 - s2
                for m in range(floor(1 * ds), ceil(X * ds) + 1):
                    v = Fr(m) / ds
                    if 1 < v < X:
                        ev.add(v)
    return sorted(ev)


def term_units(a, b):
    t = estar((a + b) / 2) * (1 / a - 1 / b) * 2 ** 96
    return -((-t.numerator) // t.denominator)


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'total'
    if mode == 'check':
        sys.path.insert(0, r'C:\Users\Shawn Krisman\math\handoff\zeta7')
        import f4_certA_exact as ref
        runs, Gr, fams = ref.setup(Fr(11, 12), [(Fr(d, 80), m) for d, m in BLOCKS])
        assert Gr == G
        import random
        random.seed(1)
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
        ev = events()
        bad = 0
        for i in range(N):
            j = random.randrange(len(ev) - 1)
            x = (ev[j] + ev[j + 1]) / 2
            e1 = estar(x); e2 = ref.e_star(x, runs, [(Fr(d, 80), m) for d, m in BLOCKS], Gr, fams)
            if e1 != e2:
                bad += 1; print('MISMATCH', x, e1, e2)
        print('checked', N, 'bad', bad)
    else:
        ev = events()
        print('events', len(ev), 'intervals', len(ev) - 1)
        tot = sum(term_units(a, b) for a, b in zip(ev[:-1], ev[1:]))
        print('bodyUnits', tot, 'target 778841997893779320302794447562', tot == 778841997893779320302794447562)
