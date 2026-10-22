/-
# Verified complex box arithmetic

A complex box `CB` is a pair of real intervals (`re`, `im`); `z ∈ B` means `z.re ∈ B.re` and
`z.im ∈ B.im`. Operations: `add`, `sub`, `neg`, `mul`, `inv`, multiplication by rational scalars,
rational points, `normSq`. All correctness theorems are unconditional (an operation that cannot
enclose returns a box with `top` components).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Interval.Basic
import Mathlib.Analysis.Complex.Norm

namespace ZetaIrr.Interval

open IV

/-- A complex box. -/
structure CB where
  re : IV
  im : IV
  deriving DecidableEq, Repr

namespace CB

def mem (B : CB) (z : ℂ) : Prop := B.re.mem z.re ∧ B.im.mem z.im

/-- The rational point `a + b i`. -/
def ofQ (a b : ℚ) : CB := ⟨ofRat a, ofRat b⟩

/-- The box `[a - e, a + e] × [b - e, b + e]`. -/
def ofQRad (a b e : ℚ) : CB := ⟨ival (a - e) (a + e), ival (b - e) (b + e)⟩

def add (B C : CB) : CB := ⟨B.re.add C.re, B.im.add C.im⟩
def neg (B : CB) : CB := ⟨B.re.neg, B.im.neg⟩
def sub (B C : CB) : CB := ⟨B.re.sub C.re, B.im.sub C.im⟩
def mul (B C : CB) : CB :=
  ⟨(B.re.mul C.re).sub (B.im.mul C.im), (B.re.mul C.im).add (B.im.mul C.re)⟩
/-- Multiplication by a rational scalar. -/
def smul (q : ℚ) (B : CB) : CB := ⟨B.re.smul q, B.im.smul q⟩
/-- `normSq z = re² + im²`. -/
def normSq (B : CB) : IV := B.re.sq.add B.im.sq
/-- `z⁻¹ = (re - i im) / normSq`. -/
def inv (B : CB) : CB :=
  let n := (normSq B).inv
  ⟨B.re.mul n, B.im.neg.mul n⟩
/-- Multiplication by `i`. -/
def mulI (B : CB) : CB := ⟨B.im.neg, B.re⟩
/-- Embedding of a real interval. -/
def ofIV (I : IV) : CB := ⟨I, ofRat 0⟩
/-- Round both components outward. -/
def round (p : ℕ) (B : CB) : CB := ⟨B.re.round p, B.im.round p⟩
/-- Hull of two boxes. -/
def join (B C : CB) : CB := ⟨B.re.join C.re, B.im.join C.im⟩

/-- Check `‖z‖ ≤ q` on the box (requires `0 ≤ q`). -/
def normLe (B : CB) (q : ℚ) : Bool := decide (0 ≤ q) && (normSq B).hiLe (q ^ 2)

/-- Check `q ≤ ‖z‖` on the box (requires `0 ≤ q`). -/
def normGe (B : CB) (q : ℚ) : Bool := decide (0 ≤ q) && (normSq B).loGe (q ^ 2)

lemma mem_ofQ (a b : ℚ) : (ofQ a b).mem (⟨a, b⟩ : ℂ) := ⟨mem_ofRat a, mem_ofRat b⟩

lemma mem_ofQRad {a b e : ℚ} {z : ℂ} (h : ‖z - ⟨a, b⟩‖ ≤ e) : (ofQRad a b e).mem z := by
  have h1 : |z.re - a| ≤ e := by
    have := Complex.abs_re_le_norm (z - ⟨a, b⟩); simp at this; linarith
  have h2 : |z.im - b| ≤ e := by
    have := Complex.abs_im_le_norm (z - ⟨a, b⟩); simp at this; linarith
  rw [abs_le] at h1 h2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma mem_add {B C : CB} {z w : ℂ} (hz : B.mem z) (hw : C.mem w) : (B.add C).mem (z + w) :=
  ⟨by simpa [add] using IV.mem_add hz.1 hw.1, by simpa [add] using IV.mem_add hz.2 hw.2⟩

lemma mem_neg {B : CB} {z : ℂ} (hz : B.mem z) : B.neg.mem (-z) :=
  ⟨by simpa [neg] using IV.mem_neg hz.1, by simpa [neg] using IV.mem_neg hz.2⟩

lemma mem_sub {B C : CB} {z w : ℂ} (hz : B.mem z) (hw : C.mem w) : (B.sub C).mem (z - w) :=
  ⟨by simpa [sub] using IV.mem_sub hz.1 hw.1, by simpa [sub] using IV.mem_sub hz.2 hw.2⟩

lemma mem_mul {B C : CB} {z w : ℂ} (hz : B.mem z) (hw : C.mem w) : (B.mul C).mem (z * w) :=
  ⟨by simpa [mul] using IV.mem_sub (IV.mem_mul hz.1 hw.1) (IV.mem_mul hz.2 hw.2),
   by simpa [mul] using IV.mem_add (IV.mem_mul hz.1 hw.2) (IV.mem_mul hz.2 hw.1)⟩

lemma mem_smul (q : ℚ) {B : CB} {z : ℂ} (hz : B.mem z) : (B.smul q).mem ((q : ℂ) * z) :=
  ⟨by simpa [smul] using IV.mem_smul q hz.1, by simpa [smul] using IV.mem_smul q hz.2⟩

lemma mem_normSq {B : CB} {z : ℂ} (hz : B.mem z) : (normSq B).mem (Complex.normSq z) := by
  rw [Complex.normSq_apply, ← pow_two, ← pow_two]
  exact IV.mem_add (IV.mem_sq hz.1) (IV.mem_sq hz.2)

lemma mem_inv {B : CB} {z : ℂ} (hz : B.mem z) : (inv B).mem z⁻¹ := by
  have hn := IV.mem_inv (mem_normSq hz)
  refine ⟨?_, ?_⟩
  · rw [Complex.inv_re, div_eq_mul_inv]; exact IV.mem_mul hz.1 hn
  · rw [Complex.inv_im, div_eq_mul_inv]; exact IV.mem_mul (IV.mem_neg hz.2) hn

lemma mem_mulI {B : CB} {z : ℂ} (hz : B.mem z) : (mulI B).mem (z * Complex.I) :=
  ⟨by simpa [mulI] using IV.mem_neg hz.2, by simpa [mulI] using hz.1⟩

lemma mem_ofIV {I : IV} {x : ℝ} (hx : I.mem x) : (ofIV I).mem (x : ℂ) :=
  ⟨by simpa [ofIV] using hx, by simpa [ofIV] using mem_ofRat 0⟩

lemma mem_round (p : ℕ) {B : CB} {z : ℂ} (hz : B.mem z) : (B.round p).mem z :=
  ⟨IV.mem_round p hz.1, IV.mem_round p hz.2⟩

lemma mem_join_left {B C : CB} {z : ℂ} (hz : B.mem z) : (B.join C).mem z :=
  ⟨IV.mem_join_left hz.1, IV.mem_join_left hz.2⟩

lemma mem_join_right {B C : CB} {z : ℂ} (hz : C.mem z) : (B.join C).mem z :=
  ⟨IV.mem_join_right hz.1, IV.mem_join_right hz.2⟩

lemma norm_le_of_normLe {B : CB} {z : ℂ} {q : ℚ} (hz : B.mem z) (h : B.normLe q = true) :
    ‖z‖ ≤ q := by
  simp only [normLe, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hq, h⟩ := h
  have h1 := IV.le_of_hiLe (mem_normSq hz) h
  rw [← Complex.sq_norm] at h1
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  push_cast at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg z) hq' two_ne_zero).1 h1

lemma le_norm_of_normGe {B : CB} {z : ℂ} {q : ℚ} (hz : B.mem z) (h : B.normGe q = true) :
    (q : ℝ) ≤ ‖z‖ := by
  simp only [normGe, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hq, h⟩ := h
  have h1 := IV.ge_of_loGe (mem_normSq hz) h
  rw [← Complex.sq_norm] at h1
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  push_cast at h1
  exact (pow_le_pow_iff_left₀ hq' (norm_nonneg z) two_ne_zero).1 h1

end CB

end ZetaIrr.Interval
