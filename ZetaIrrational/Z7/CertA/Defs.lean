/-
# The A-certificate for instance Z7: definitions

`PROOF_ZETA.md` §5.1 and `handoff/zeta7/f4_certA_exact.py`.

Instance Z7: zero runs `[1, rn]` and `[-(1+r)n, -n-1]` of multiplicity 5, `r = 11/12`, blocks
`δ_j = k_j/80` (`k_j = 1, …, 18`, multiplicity 1) from `ZetaIrr.Z7.blocks`, `G = 547/120`.

This file contains
* the **specification** of PROOF_ZETA §5.1 for `x = n/p`, `y = k/p`: block count `Sfun`, pole
  counts `Pfun`, `Ptot`, zero hits `cfun`, the three-case `bracket` (`y ≥ 1`; `y < 1` and
  `P ≥ 1`; `y < 1` and `P = 0`), and `gfun = bracket` where `S(y) > 0`, `0` where `S(y) = 0`.
  Since `S(0) = 0` (no block contains `0`), `sup_{0 ≤ y ≤ x} gfun x y = max(0, sup_{S(y)>0} bracket)`,
  which is PROOF_ZETA's `e*(x) + G⌊x⌋`;
* the **floor-data form** `Phi`: `gfun x y` only depends on the floors and ceilings of `y - c` for
  the finitely many offsets `c = σ/240 · x` listed in `offsets`;
* the **computable** `eStarInt x`: a max over the residues `σP mod 240Q` (`x = P/Q`) of one
  closed-form candidate value each (`cand`), proved equal to `max_{0 ≤ y ≤ x} gfun x y` in
  `Z7/CertA/Sound.lean`, `Z7/CertA/Attain.lean`;
* the **event points** in `[1, X]` (same set as `f4_certA_exact.py`: chunk cuts, integers, and
  crossings `m/(s₁ - s₂)` of the breakpoint line families `y = s x + j`);
* the rounded body sum `bodyUnits` (each term rounded *up* to a multiple of `2^-96`, as in the
  Python) and the tail `(S+15)/X + G/(2(X-1))`.

Everything here is a definition; no proofs.

Status: complete (definitions only, no `sorry`).
-/
import ZetaIrrational.FamilyZ7

namespace ZetaIrr.Z7.CertA

open Finset

/-! ## Specification (PROOF_ZETA §5.1) -/

/-- `δ = d/80`. -/
def dlt (d : ℕ) : ℚ := (d : ℚ) / 80

/-- `r = 11/12`. -/
def rr : ℚ := 11 / 12

/-- `S(y) = Σ_j m_j [δ_j x ≤ y ≤ (1-δ_j) x]`. -/
def Sfun (x y : ℚ) : ℕ :=
  (blocks.map fun b => if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0).sum

/-- `P_j(y)` of §5.1, with the out-of-block indicator terms. -/
def Pfun (d : ℕ) (x y : ℚ) : ℤ :=
  if dlt d * x ≤ y ∧ y ≤ (1 - dlt d) * x then
    ⌊y - dlt d * x⌋ + ⌊(1 - dlt d) * x - y⌋
  else if y < dlt d * x then
    ⌊(1 - dlt d) * x - y⌋ - ⌊dlt d * x - y⌋ + (if Int.fract (dlt d * x - y) = 0 then 1 else 0)
  else
    ⌊y - dlt d * x⌋ - ⌊y - (1 - dlt d) * x⌋ + (if Int.fract (y - (1 - dlt d) * x) = 0 then 1 else 0)

/-- `P(y) = Σ_j m_j P_j(y)`. -/
def Ptot (x y : ℚ) : ℤ := (blocks.map fun b => (b.2 : ℤ) * Pfun b.1 x y).sum

/-- The zero hits `c(y) = 5(⌊y + rx⌋ - ⌊y⌋) + 5(⌈y - x⌉ - ⌈y - (1+r)x⌉)`. -/
def cfun (x y : ℚ) : ℤ := 5 * (⌊y + rr * x⌋ - ⌊y⌋) + 5 * (⌈y - x⌉ - ⌈y - (1 + rr) * x⌉)

/-- The bracket of §5.1: `S + 4 - c + P` if `y ≥ 1`; `S - 1 - c + P` if `y < 1` and `P ≥ 1`;
`0` if `y < 1` and `P = 0`. -/
def bracket (x y : ℚ) : ℤ :=
  if 1 ≤ y then (Sfun x y : ℤ) + 4 - cfun x y + Ptot x y
  else if 1 ≤ Ptot x y then (Sfun x y : ℤ) - 1 - cfun x y + Ptot x y
  else 0

/-- The bracket where some block contains `y`, and `0` elsewhere. -/
def gfun (x y : ℚ) : ℤ := if Sfun x y = 0 then 0 else bracket x y

/-! ## Offsets and the floor-data form -/

/-- An offset `σ` stands for the breakpoint family `y = σ/240 · x + j`, `j ∈ ℤ`. -/
def offVal (x : ℚ) (o : ℤ) : ℚ := (o : ℚ) / 240 * x

/-- Left block end `δ x`: `σ = 3d`. -/
def aOff (d : ℕ) : ℤ := 3 * (d : ℤ)
/-- Right block end `(1-δ) x`: `σ = 240 - 3d`. -/
def bOff (d : ℕ) : ℤ := 240 - 3 * (d : ℤ)

/-- All offsets on which `gfun x ·` depends: `0` (`⌊y⌋`), `-220` (`⌊y + rx⌋`), `240` (`⌈y - x⌉`),
`460` (`⌈y - (1+r)x⌉`), and the block ends. -/
def offsets : List ℤ :=
  0 :: (-220) :: 240 :: 460 :: blocks.flatMap fun b => [aOff b.1, bOff b.1]

/-- One block's `m_j [in block]` from the floor data `Fa = ⌊y - δx⌋`, `Cb = ⌈y - (1-δ)x⌉`. -/
def blockS (m Fa Cb : ℤ) : ℤ := if 0 ≤ Fa ∧ Cb ≤ 0 then m else 0

/-- One block's `m_j P_j` from the floor/ceiling data `Fa, Ca, Fb, Cb`. -/
def blockP (m Fa Ca Fb Cb : ℤ) : ℤ :=
  if 0 ≤ Fa ∧ Cb ≤ 0 then m * (Fa - Cb)
  else if Fa < 0 then m * (Ca - Cb + if Fa = Ca then 1 else 0)
  else m * (Fa - Fb + if Fb = Cb then 1 else 0)

/-- `gfun` as a function of floor data `F o = ⌊y - c_o⌋`, `C o = ⌈y - c_o⌉`. -/
def Phi (F C : ℤ → ℤ) : ℤ :=
  let S := (blocks.map fun b => blockS b.2 (F (aOff b.1)) (C (bOff b.1))).sum
  let P := (blocks.map fun b =>
    blockP b.2 (F (aOff b.1)) (C (aOff b.1)) (F (bOff b.1)) (C (bOff b.1))).sum
  let c := 5 * (F (-220) - F 0) + 5 * (C 240 - C 460)
  if S = 0 then 0
  else if 1 ≤ F 0 then S + 4 - c + P
  else if 1 ≤ P then S - 1 - c + P
  else 0

/-! ## The computable `e*` (integer scaling) -/

/-- For `x = P/Q` and `M = 240 Q`, the scaled offset `M · offVal x σ = σP`, split as `q M + r`
with `0 ≤ r < M`. -/
def qrOf (P Q : ℤ) (o : ℤ) : ℤ × ℤ := (o * P / (240 * Q), o * P % (240 * Q))

/-- Floor of `y - c_l` at the candidate `y = k + r_i/M`, where `c_l` has data `(q_l, r_l)`. -/
def flAt (k ri : ℤ) (ql : ℤ × ℤ) : ℤ := k - ql.1 - (if ri < ql.2 then 1 else 0)

/-- The correction `⌈·⌉ - ⌊·⌋ ∈ {0, 1}` at the candidate (`right = false`), or `1` for the right
limit `y + 0` (`right = true`). -/
def ebAt (ri : ℤ) (right : Bool) (ql : ℤ × ℤ) : ℤ := if right then 1 else if ri = ql.2 then 0 else 1

/-- Ceiling of `y - c_l` at `y = k + r_i/M` (`right = false`), or the floor-plus-one of the
right limit (`right = true`). -/
def clAt (k ri : ℤ) (right : Bool) (ql : ℤ × ℤ) : ℤ := flAt k ri ql + ebAt ri right ql

/-- Precomputed per-block data `(m, (q_a, r_a), (q_b, r_b))` for `x = P/Q`. -/
def preOf (P Q : ℤ) : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ)) :=
  blocks.map fun b => ((b.2 : ℤ), qrOf P Q (aOff b.1), qrOf P Q (bOff b.1))

/-- `Phi` at a candidate `y = k + r_i/M` (or its right limit), from precomputed data;
`qn, q2, q3` are the data of the offsets `-220, 240, 460`. -/
def phiAt (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (qn q2 q3 : ℤ × ℤ) (k ri : ℤ) (right : Bool) : ℤ :=
  let S := (pre.map fun e => blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2)).sum
  let P := (pre.map fun e => blockP e.1 (flAt k ri e.2.1) (clAt k ri right e.2.1)
    (flAt k ri e.2.2) (clAt k ri right e.2.2)).sum
  let c := 5 * (flAt k ri qn - k) + 5 * (clAt k ri right q2 - clAt k ri right q3)
  if S = 0 then 0
  else if 1 ≤ k then S + 4 - c + P
  else if 1 ≤ P then S - 1 - c + P
  else 0

/-- `S + P` in closed form, `T = Σ m (1 + F_a - C_b)` (independent of `k`; evaluated at `k = 0`). -/
def Tval (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (ri : ℤ) (right : Bool) : ℤ :=
  (pre.map fun e => e.1 * (1 + flAt 0 ri e.2.1 - clAt 0 ri right e.2.2)).sum

/-- The zero hits `c`, independent of `k` (evaluated at `k = 0`). -/
def cval (qn q2 q3 : ℤ × ℤ) (ri : ℤ) (right : Bool) : ℤ :=
  5 * flAt 0 ri qn + 5 * (clAt 0 ri right q2 - clAt 0 ri right q3)

/-- The largest valid `k` for residue `r_i`: `k M + r_i ≤ 240 P` (`right = false`) or `< 240 P`
(`right = true`), where `240 P = q_X M + r_X`. -/
def kmax (qX rX ri : ℤ) (right : Bool) : ℤ :=
  qX - (if (if right then ri < rX else ri ≤ rX) then 0 else 1)

/-- Some block (with `m > 0`) contains a valid candidate `k ≥ 1`: block `e` contains `k` iff
`q_a + [r_i < r_a] ≤ k ≤ q_b + [r_i < r_b] - e_b`. -/
def has1 (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (qX rX ri : ℤ) (right : Bool) : Bool :=
  pre.any fun e => decide (0 < e.1 ∧
    max 1 (e.2.1.1 + (if ri < e.2.1.2 then 1 else 0)) ≤
      e.2.2.1 + (if ri < e.2.2.2 then 1 else 0) - ebAt ri right e.2.2 ∧
    max 1 (e.2.1.1 + (if ri < e.2.1.2 then 1 else 0)) ≤ kmax qX rX ri right)

/-- The best value over all candidates `y = k + r_i/M` (or right limits) with residue `r_i`:
at `k = 0` it is `phiAt … 0`; for `k ≥ 1` inside some block it is `T + 4 - c`. -/
def cand (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (qn q2 q3 : ℤ × ℤ) (qX rX ri : ℤ) (right : Bool) :
    ℤ :=
  max (phiAt pre qn q2 q3 0 ri right)
    (if has1 pre qX rX ri right then Tval pre ri right + 4 - cval qn q2 q3 ri right else 0)

/-- `max_{0 ≤ y ≤ x} gfun x y` (an integer), computed over the breakpoint residues. -/
def eStarInt (x : ℚ) : ℤ :=
  let P := x.num
  let Q : ℤ := x.den
  let pre := preOf P Q
  let qn := qrOf P Q (-220)
  let q2 := qrOf P Q 240
  let q3 := qrOf P Q 460
  let qX := P / Q
  let rX := 240 * (P % Q)
  offsets.foldl (fun acc o =>
      let ri := (qrOf P Q o).2
      max acc (max (cand pre qn q2 q3 qX rX ri false) (cand pre qn q2 q3 qX rX ri true)))
    0

/-- `e*(x) = max(0, sup_{0 ≤ y ≤ x, S(y) > 0} bracket(x, y)) - G⌊x⌋` (computable; see
`Z7/CertA/Sound.lean` and `Z7/CertA/Attain.lean`), for `x ≥ 1`. For `x < 1` it is `0`. -/
def eStar (x : ℚ) : ℚ := if 1 ≤ x then (eStarInt x : ℚ) - G * ⌊x⌋ else 0

/-! ## Event points -/

/-- The slopes `s` of the breakpoint line families `y = s x + j` of `f4_certA_exact.py`
(`= σ/240` for the offsets `σ`). -/
def fams : List ℚ :=
  (([0, -11 / 12, 1, 23 / 12] : List ℚ) ++
    blocks.flatMap (fun b : ℕ × ℕ => ([dlt b.1, 1 - dlt b.1] : List ℚ))).dedup

/-- Crossings in `(lo, hi)` of the families with slopes `s₁ > s₂`: `x = m / (s₁ - s₂)`. -/
def crossPair (lo hi : ℚ) (s₁ s₂ : ℚ) : List ℚ :=
  if s₂ < s₁ then
    let ds := s₁ - s₂
    let m0 := ⌊lo * ds⌋
    let m1 := ⌈hi * ds⌉
    ((List.range ((m1 - m0).toNat + 1)).map fun i : ℕ => ((m0 + (i : ℤ) : ℤ) : ℚ) / ds).filter
      fun v => lo < v ∧ v < hi
  else []

/-- All crossings in `(lo, hi)`. -/
def crossings (lo hi : ℚ) : List ℚ :=
  fams.flatMap fun s₁ => fams.flatMap fun s₂ => crossPair lo hi s₁ s₂

/-- The chunk cuts of `f4_certA_exact.py`: `1 + j/20` (`j < 40`) and `3 + j/2`
(`0 ≤ j ≤ 2(X-3)`). They include every integer in `[1, X]`. -/
def cuts (X : ℕ) : List ℚ :=
  (List.range 40).map (fun j : ℕ => 1 + (j : ℚ) / 20) ++
    (List.range (2 * (X - 3) + 1)).map (fun j : ℕ => 3 + (j : ℚ) / 2)

/-- Remove adjacent duplicates. -/
def dedupAdj : List ℚ → List ℚ
  | a :: b :: l => if a = b then dedupAdj (b :: l) else a :: dedupAdj (b :: l)
  | l => l

/-- The sorted event points in `[1, X]`. -/
def events (X : ℕ) : List ℚ :=
  dedupAdj ((cuts X ++ crossings 1 X).mergeSort (fun a b => decide (a ≤ b)))

/-! ## The certificate sums -/

/-- Sum of `g a b` over consecutive pairs `(a, b)` of a list. -/
def pairSum {β : Type} [AddCommMonoid β] (g : ℚ → ℚ → β) : List ℚ → β
  | a :: b :: l => g a b + pairSum g (b :: l)
  | _ => 0

/-- The exact body `A_body = Σ_ℓ e*(mid_ℓ) (1/x_{ℓ-1} - 1/x_ℓ)`. -/
def ABody (X : ℕ) : ℚ := pairSum (fun a b => eStar ((a + b) / 2) * (1 / a - 1 / b)) (events X)

/-- One term rounded up to a multiple of `2^-96` (in units of `2^-96`). -/
def termUnits (a b : ℚ) : ℤ := ⌈eStar ((a + b) / 2) * (1 / a - 1 / b) * 2 ^ 96⌉

/-- The rounded body, in units of `2^-96`. -/
def bodyUnits (X : ℕ) : ℤ := pairSum termUnits (events X)

/-- `E_tail = S + 15 = 33`; tail bound `E_tail/X + G/(2(X-1))` (PROOF_ZETA (5.2), (5.4)). -/
def tail (X : ℕ) : ℚ := 33 / X + G / (2 * ((X : ℚ) - 1))

end ZetaIrr.Z7.CertA
