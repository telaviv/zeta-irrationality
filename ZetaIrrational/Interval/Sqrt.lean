/-
# Verified enclosure of `Real.sqrt` on rational intervals

`sqrtIV I`: rational Newton iterates (rounded to `2^{-64}`) give candidate endpoints, which are
then *checked* by squaring (`sqrtWith`), so soundness does not depend on the iteration.
-/
import ZetaIrrational.Interval.CBox
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ZetaIrr.Interval

open IV

/-- `[lo, hi]` if `lo² ≤ a`, `b ≤ hi²` and `0 ≤ lo ≤ hi`, else `top`. -/
def sqrtWith (lo hi : ℚ) : IV → IV
  | top => top
  | ival a b => if 0 ≤ lo ∧ lo ^ 2 ≤ a ∧ 0 ≤ hi ∧ b ≤ hi ^ 2 then ival lo hi else top

lemma mem_sqrtWith (lo hi : ℚ) {I : IV} {x : ℝ} (hx : I.mem x) :
    (sqrtWith lo hi I).mem (Real.sqrt x) := by
  cases I with
  | top => trivial
  | ival a b =>
    obtain ⟨h1, h2⟩ := hx
    simp only [sqrtWith]
    split_ifs with h
    · obtain ⟨hl0, hla, hh0, hbh⟩ := h
      have hl0' : (0 : ℝ) ≤ lo := by exact_mod_cast hl0
      have hh0' : (0 : ℝ) ≤ hi := by exact_mod_cast hh0
      have hla' : (lo : ℝ) ^ 2 ≤ a := by exact_mod_cast hla
      have hbh' : (b : ℝ) ≤ (hi : ℝ) ^ 2 := by exact_mod_cast hbh
      constructor
      · rw [show (lo : ℝ) = Real.sqrt ((lo : ℝ) ^ 2) from (Real.sqrt_sq hl0').symm]
        exact Real.sqrt_le_sqrt (hla'.trans h1)
      · rw [show (hi : ℝ) = Real.sqrt ((hi : ℝ) ^ 2) from (Real.sqrt_sq hh0').symm]
        exact Real.sqrt_le_sqrt (h2.trans hbh')
    · trivial

/-- Round down to `2^{-64}`. -/
def rd64 (q : ℚ) : ℚ := (⌊q * 2 ^ 64⌋ : ℚ) / 2 ^ 64

/-- Newton iteration for `√a` (any output is fine for soundness). -/
def newtonSqrt (a : ℚ) : ℕ → ℚ → ℚ
  | 0, s => s
  | k + 1, s => newtonSqrt a k (if s = 0 then 0 else rd64 ((s + a / s) / 2))

/-- Enclosure of `√x` on an interval. -/
def sqrtIV (I : IV) : IV :=
  match I with
  | top => top
  | ival a b =>
    let s := newtonSqrt a 40 ((a + 1) / 2)
    let t := newtonSqrt b 40 ((b + 1) / 2)
    sqrtWith (max 0 (s * (1 - 1 / 2 ^ 40))) (t * (1 + 1 / 2 ^ 40) + 1 / 2 ^ 60) I

lemma mem_sqrtIV {I : IV} {x : ℝ} (hx : I.mem x) : (sqrtIV I).mem (Real.sqrt x) := by
  cases I with
  | top => trivial
  | ival a b => exact mem_sqrtWith _ _ hx

end ZetaIrr.Interval
