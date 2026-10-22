"""Generator for the Z7 saddle-point certificate data (UNTRUSTED; every claim is re-checked by the Lean kernel).

Instance Z7 of PROOF_ZETA §9: r = 11/12, eighteen blocks delta = k/80 (k = 1..18, m = 1), q = 240, phase 3 pi:
    f(x) = Psi(x) - 3 pi i x,   Psi(x) = sum_i c_i alpha_i log alpha_i,   alpha_i = s_i x + kappa_i,
with the 40 factors (5, x), (5, 11/12 - x), (5, x + 23/12), (-5, x + 1), and per block (1, x + k/80), (-1, x + 1 - k/80).

What it does (mpmath, 50 digits; nothing here is trusted):
 1. Newton for the saddle x0 (f'(x0) = 0) from the seed 0.8921643 + 0.1829121 i; rational centre c0 (25 digits) and
    Y ~ 1/Psi''(c0) for the contraction test.
 2. The descent direction d = v/|v|, v = 1 + u, u = -conj(Psi''(x0))/|Psi''(x0)| (so Psi''(x0) d^2 = -K), oriented
    so that x0 + rho d leads to +i infinity.
 3. RK4 traces of the steepest-descent ODE from x0 +- rho d (rho = RHO) down to the real axis (x_c) and up to
    Im x >= YTOP; greedy simplification of each trace into a rational polyline (vertices rounded to 1e-12) against a
    conservative float model of the Lean segment check `segOK` (threshold T0).
 4. Lower bounds m_i for |alpha_i| on the disc closedBall(c0, rho + R0) (for the Psi''' bound `d3bnd`).
 5. Writes `ZetaIrrational/Z7/Interval/ConstZ7.lean` (saddle constants) and `PolyDataZ7.lean` (polyline data).

Usage (from lean_zeta7/):  python scripts/saddle/gen_saddle_Z7.py
"""

import os
from fractions import Fraction as Fr
from mpmath import mp, mpf, mpc, log, pi, findroot, sqrt, atan2, exp, nint

mp.dps = 30

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, 'ZetaIrrational', 'Z7', 'Interval')

PHASE = 3
RHO = Fr(1, 20)            # Taylor-disc radius
R0 = Fr(1, 10 ** 12)       # contraction-ball radius
T0 = Fr(-101367, 10 ** 4)  # far threshold: Re f <= T0 off the Taylor segment (Re Omega ~ -10.1167485)
YTOP = mpf(12)             # the upper trace stops at Im x >= YTOP
SAFETY = mpf('0.6')        # use only this fraction of the margin T0 - X in the float model of segOK
CHUNK = 8                  # vertices per kernel-check chunk
NL = chr(10)               # write LF line endings on every platform

FAC = [(5, 1, Fr(0)), (5, -1, Fr(11, 12)), (5, 1, Fr(23, 12)), (-5, 1, Fr(1))]
for k in range(1, 19):
    FAC += [(1, 1, Fr(k, 80)), (-1, 1, 1 - Fr(k, 80))]
F = [(c, s, mpf(k.numerator) / k.denominator) for c, s, k in FAC]


def q2m(q):
    return mpf(q.numerator) / q.denominator


def alphas(x):
    return [(c, s, s * x + k) for c, s, k in F]


def psi(x):
    return sum(c * a * log(a) for c, s, a in alphas(x))


def d1(x):
    return sum(c * s * (log(a) + 1) for c, s, a in alphas(x))


def d2(x):
    return sum(c * s * s / a for c, s, a in alphas(x))


def f(x):
    return psi(x) - PHASE * pi * 1j * x


def g(x):
    return d1(x) - PHASE * pi * 1j


def h(x):
    return f(x).real


def box_minabs(lo_re, hi_re, lo_im, hi_im, s, k):
    """min |s x + k| over the box (alpha is an affine image of the box: distance from 0 to the image box)."""
    ar = sorted([s * lo_re + k, s * hi_re + k])
    ai = sorted([s * lo_im, s * hi_im])
    dr = 0 if ar[0] <= 0 <= ar[1] else min(abs(ar[0]), abs(ar[1]))
    di = 0 if ai[0] <= 0 <= ai[1] else min(abs(ai[0]), abs(ai[1]))
    return sqrt(dr ** 2 + di ** 2)


def C_model(a, b):
    """Conservative float model of sqrt(normSq(d2psiBr(segBox a b))): sum |c| sqrt2 max|alpha| / min|alpha|^2."""
    lo_re, hi_re = min(a.real, b.real), max(a.real, b.real)
    lo_im, hi_im = min(a.imag, b.imag), max(a.imag, b.imag)
    tot = mpf(0)
    for c, s, k in F:
        m = box_minabs(lo_re, hi_re, lo_im, hi_im, s, k)
        if m == 0:
            return mpf('inf')
        # box inversion conj(B)/normSq(B): each part up to max|.| / min|alpha|^2
        mx = max(abs(s * x + k) for x in (mpc(lo_re, lo_im), mpc(lo_re, hi_im), mpc(hi_re, lo_im), mpc(hi_re, hi_im)))
        tot += abs(c) * sqrt(2) * mx / m ** 2
    return tot


def seg_ok_model(a, b, T):
    e = b - a
    ha, hb = h(a), h(b)
    la = (g(a) * e).real
    lb = (g(b) * (-e)).real
    X = max(ha + max(0, la) / 2, hb + max(0, lb) / 2)
    L2 = abs(e) ** 2
    return X + C_model(a, b) * L2 / 4 <= T - (1 - SAFETY) * (T - X) if X < T else False


def rnd(x, den=10 ** 12):
    return Fr(int(nint(x * den)), den)


def toq(z):
    return (rnd(z.real), rnd(z.imag))


def qc(v):
    return mpc(q2m(v[0]), q2m(v[1]))


def trace(start, sing):
    def vel(x):
        gg = g(x)
        return -gg.conjugate() / abs(gg)

    pts = [start]
    x = start
    for _ in range(200000):
        dist = min(abs(x - s_) for s_ in sing)
        hh = min(mpf('0.005'), dist / 40)
        k1 = vel(x); k2 = vel(x + hh / 2 * k1); k3 = vel(x + hh / 2 * k2); k4 = vel(x + hh * k3)
        xn = x + hh / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        if xn.imag <= 0:
            t = x.imag / (x.imag - xn.imag)
            pts.append(mpc(x.real + t * (xn.real - x.real), 0))
            return pts, 'real'
        pts.append(xn)
        x = xn
        if x.imag >= YTOP:
            return pts, 'top'
    return pts, 'stuck'


def simplify(start_q, pts, T, real_end):
    """Greedy: from the current rational vertex, jump to the farthest trace point whose segment passes the model."""
    out = []
    cur = start_q
    i = 0
    n = len(pts)
    while i < n - 1:
        best = None
        j = i + 1
        while j < n:
            cand = toq(pts[j])
            if real_end and j == n - 1:
                cand = (cand[0], Fr(0))
            if seg_ok_model(qc(cur), qc(cand), T):
                best = (j, cand)
                j += 1 if j - i < 8 else max(1, (j - i) // 8)
            else:
                break
        if best is None:
            raise RuntimeError(f'no admissible segment from {cur} (trace index {i})')
        i, cand = best
        out.append(cand)
        cur = cand
    return out


def lean_q(q):
    if q.denominator == 1:
        return f'{q.numerator}'
    if (q * 10 ** 12).denominator == 1:
        return f'{int(q * 10 ** 12)} / 10 ^ 12'
    return f'{q.numerator} / {q.denominator}'


def lean_pt(v):
    return f'({lean_q(v[0])}, {lean_q(v[1])})'


def main():
    sing = [-k / s for c, s, k in F]
    x0 = findroot(g, mpc('0.8921643', '0.1829121'))
    Om = f(x0)
    print('x0 =', x0)
    print('Omega =', Om)
    print('sin(240 Im Omega) =', mp.sin(240 * Om.imag))
    cRe, cIm = Fr(int(nint(x0.real * 10 ** 25)), 10 ** 25), Fr(int(nint(x0.imag * 10 ** 25)), 10 ** 25)
    c0 = mpc(q2m(cRe), q2m(cIm))
    w = d2(c0)
    Yc = 1 / w
    Yre, Yim = Fr(int(nint(Yc.real * 10 ** 18)), 10 ** 18), Fr(int(nint(Yc.imag * 10 ** 18)), 10 ** 18)
    K = abs(d2(x0))
    print('K =', K, ' |g(c0)| =', abs(g(c0)))
    u = -d2(x0).conjugate() / K
    v = 1 + u
    d = v / abs(v)
    assert abs(d2(x0) * d * d + K) < mpf(10) ** -20
    rho = q2m(RHO)
    tr = {}
    for sgn in (1, -1):
        pts, how = trace(x0 + sgn * rho * d, sing)
        tr[how] = (sgn, pts)
    assert set(tr) == {'real', 'top'}, tr.keys()
    dsign = tr['top'][0]
    print('orientation sign of d (towards the top):', dsign)
    # disc endpoints in the oriented direction
    dd = dsign * d
    eplus, eminus = x0 + rho * dd, x0 - rho * dd
    print('h(x0 +- rho d) - Re Omega =', h(eplus) - Om.real, h(eminus) - Om.real)
    T = q2m(T0)
    up_pts = tr['top'][1]
    dn_pts = tr['real'][1]
    upStart, dnStart = toq(eplus), toq(eminus)
    up = simplify(upStart, up_pts, T, False)
    dn = simplify(dnStart, dn_pts, T, True)
    xc = dn[-1][0]
    print('upper vertices:', len(up), ' lower vertices:', len(dn), ' x_c =', float(xc), ' x_top =', up[-1])
    # Psi''' bound data on closedBall(c0, rho + R0): m_i <= |alpha_i(c0)| - |s_i| (rho + R0), rounded down
    rr = q2m(RHO + R0)
    ms = []
    for c, s, k in F:
        m = abs(s * c0 + k) - abs(s) * rr
        assert m > 0
        ms.append(int(mp.floor(m * 10 ** 6 * (1 - mpf(10) ** -9))))
    M = sum(abs(c) / (mpf(mi) / 10 ** 6) ** 2 for (c, s, k), mi in zip(F, ms))
    print('Mcert ~', M, ' M rho =', M * rho, ' 3K/2 =', 3 * K / 2)

    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, 'ConstZ7.lean'), 'w', encoding='utf-8', newline=NL) as fh:
        fh.write(CONST_TMPL.format(cRe=int(cRe * 10 ** 25), cIm=int(cIm * 10 ** 25), Yre=int(Yre * 10 ** 18),
                                   Yim=int(Yim * 10 ** 18),
                                   ms=', '.join(str(m) for m in ms)))
    chunks = [up[i:i + CHUNK] for i in range(0, len(up), CHUNK)]
    body = []
    body.append(f'/-- Start of the upper polyline (rounded `x₀ + ρ d`). -/\ndef upStart : ℚ × ℚ := {lean_pt(upStart)}\n')
    prev = 'upStart'
    names = []
    for ci, ch in enumerate(chunks, 1):
        if ci > 1:
            body.append(f'/-- Start of chunk {ci}. -/\ndef upA{ci} : ℚ × ℚ := lastPt {prev} upC{ci - 1}\n')
            prev = f'upA{ci}'
        body.append(f'/-- Upper polyline, chunk {ci}. -/\ndef upC{ci} : List (ℚ × ℚ) :=\n  [' +
                    ',\n    '.join(lean_pt(p) for p in ch) + ']\n')
        names.append(f'upC{ci}')
    nest = names[-1]
    for nm in reversed(names[:-1]):
        nest = f'{nm} ++ ({nest})' if '++' in nest else f'{nm} ++ {nest}'
    body.append(f'/-- Rational vertices of the upper contour piece, after `upStart`, ending at `xtop`. -/\n'
                f'def upPts : List (ℚ × ℚ) := {nest}\n')
    body.append(f'/-- Start of the lower polyline (rounded `x₀ - ρ d`). -/\ndef dnStart : ℚ × ℚ := {lean_pt(dnStart)}\n')
    body.append('/-- Rational vertices of the lower contour piece, after `dnStart`, ending at `x_c` (real). -/\n'
                'def dnPts : List (ℚ × ℚ) :=\n  [' + ',\n    '.join(lean_pt(p) for p in dn) + ']\n')
    body.append(f'/-- The top vertex. -/\ndef xtop : ℚ × ℚ := {lean_pt(up[-1])}\n')
    body.append(f'/-- The real crossing point `x_c`. -/\ndef xc : ℚ := {lean_q(xc)}\n')
    body.append(f'/-- The last vertex before `x_c` on the lower polyline. -/\ndef firstB : ℚ × ℚ := {lean_pt(dn[-2])}\n')
    with open(os.path.join(OUT, 'PolyDataZ7.lean'), 'w', encoding='utf-8', newline=NL) as fh:
        fh.write(POLY_HEAD.format(n_up=len(up), n_dn=len(dn), nchunks=len(chunks), T0=lean_q(T0)))
        fh.write('\n'.join(body))
        fh.write('\nend ZetaIrr.Z7.Interval\n')
    print('chunks:', len(chunks))


CONST_TMPL = """/-
# Z7 saddle constants (generated by `scripts/saddle/gen_saddle_Z7.py`; untrusted data)

* `cRe + i cIm`: a rational point (25 digits) near the Newton root of `Ψ' = 3πi` from the seed
  `0.8921643 + 0.1829121 i` (PROOF_ZETA §9, `f5_saddle_cert.jsonl`);
* `Yre + i Yim ≈ 1/Ψ''(c0)` (contraction factor of `Interval/Newton.lean`);
* `facMs`: lower bounds `10⁶ m_i ≤ 10⁶ (|α_i(c0)| - |s_i| (ρ + R0))` for the `Ψ'''` bound on the Taylor disc.

Every use is re-checked by `decide +kernel` (`SaddleZ7.lean`).

Status: complete (data only, no `sorry`).
-/
import Mathlib.Data.Rat.Defs

namespace ZetaIrr.Z7.Interval

def cRe : ℚ := {cRe} / 10 ^ 25
def cIm : ℚ := {cIm} / 10 ^ 25
def Yre : ℚ := {Yre} / 10 ^ 18
def Yim : ℚ := {Yim} / 10 ^ 18

/-- `10⁶ m_i`, in the order of `facZ7`. -/
def facMs : List ℕ :=
  [{ms}]

end ZetaIrr.Z7.Interval
"""

POLY_HEAD = """/-
# Contour data for the Z7 saddle certificate (PROOF_ZETA §6.3, instance Z7)

Rational vertices of the steepest-descent contour of `h = Re f`, `f = Ψ - 3πi x`:
* the upper polyline `upStart, upPts` ({n_up} vertices) from (the rounding of) `x₀ + ρ d` to `xtop`,
  split into {nchunks} chunks `upC1, …` whose kernel checks live in separate files (`UpChunk*.lean`);
* the lower polyline `dnStart, dnPts` ({n_dn} vertices) from (the rounding of) `x₀ - ρ d` down to the
  real point `x_c < 11/12`.

Generated by `scripts/saddle/gen_saddle_Z7.py` (RK4 trace of the steepest-descent ODE from `x₀ ± ρ d`,
`ρ = 1/20`, vertices rounded to `10⁻¹²`, greedy simplification against a float model of the Lean
checks); every claim is re-checked by `decide +kernel` in the files that use this data.

Constants: far threshold `T0 = {T0}` (`Re Ω ≈ -10.1167485`), sector constants `amin = 1/100`,
`Amax = 2.76` (`η = π - 2.76 > 0.38`).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Interval.FacZ7
import ZetaIrrational.Fam.Interval.Chunks

namespace ZetaIrr.Z7.Interval

open ZetaIrr.Interval ZetaIrr.Fam.Interval

/-- The far threshold `T0`: `Re f ≤ T0` off the Taylor segment. -/
def T0 : ℚ := {T0}

/-- Sector constants of (S4). -/
abbrev amin : ℚ := 1 / 100
abbrev Amax : ℚ := 276 / 100

"""

if __name__ == '__main__':
    main()
