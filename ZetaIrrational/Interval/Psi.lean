/-
# The phase function `Ψ(x) = Σ c_i α_i log α_i` and its box enclosures

A factor `⟨c, s, κ⟩` stands for `c · F(α(x))` with `α(x) = s x + κ` and `F(y) = y log y`
(principal `Complex.log`), as in PROOF_BETA §6.2–6.3. For a factor list `l`:

* `psiL l z   = Σ c α log α`,
* `dpsiL l z  = Σ c s (log α + 1)`  (`= Ψ'`),
* `d2psiL l z = Σ c s² / α`          (`= Ψ''`),

and `hasDerivAt_psiL`, `hasDerivAt_dpsiL` prove these derivative relations wherever every
`α_i(z)` lies in the slit plane (e.g. `Im z ≠ 0` when all `s ≠ 0`).
`psiB`, `dpsiB`, `d2psiB` are the computable box versions, with unconditional soundness lemmas.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Interval.Elem
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace ZetaIrr.Interval

open Complex

/-- A factor `c · F(s x + κ)`. -/
structure Fac where
  c : ℤ
  s : ℤ
  κ : ℚ
  deriving DecidableEq, Repr

namespace Fac

/-- `α(z) = s z + κ`. -/
def α (a : Fac) (z : ℂ) : ℂ := (a.s : ℂ) * z + (a.κ : ℂ)

/-- Box version of `α`. -/
def αB (a : Fac) (B : CB) : CB := (B.smul (a.s : ℚ)).add (CB.ofQ a.κ 0)

lemma mem_αB (a : Fac) {B : CB} {z : ℂ} (hz : B.mem z) : (a.αB B).mem (a.α z) := by
  have h := CB.mem_add (CB.mem_smul (a.s : ℚ) hz) (CB.mem_ofQ a.κ 0)
  have he : ((a.s : ℚ) : ℂ) * z + (⟨(a.κ : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = a.α z := by
    apply Complex.ext <;> simp [α]
  rw [he] at h; exact h

lemma hasDerivAt_α (a : Fac) (z : ℂ) : HasDerivAt a.α (a.s : ℂ) z := by
  have := ((hasDerivAt_id z).const_mul (a.s : ℂ)).add_const (a.κ : ℂ)
  rw [mul_one] at this
  exact this

lemma α_mem_slitPlane (a : Fac) {z : ℂ} (hs : a.s ≠ 0) (hz : z.im ≠ 0) :
    a.α z ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right
  simp [α, hs, hz]

end Fac

/-! ## Analytic definitions -/

noncomputable def psiL : List Fac → ℂ → ℂ
  | [], _ => 0
  | a :: l, z => (a.c : ℂ) * (a.α z * log (a.α z)) + psiL l z

noncomputable def dpsiL : List Fac → ℂ → ℂ
  | [], _ => 0
  | a :: l, z => (a.c : ℂ) * ((a.s : ℂ) * (log (a.α z) + 1)) + dpsiL l z

noncomputable def d2psiL : List Fac → ℂ → ℂ
  | [], _ => 0
  | a :: l, z => (a.c : ℂ) * ((a.s : ℂ) * (a.s : ℂ) / a.α z) + d2psiL l z

/-- All `α_i(z)` in the slit plane. -/
def Good (l : List Fac) (z : ℂ) : Prop := ∀ a ∈ l, a.α z ∈ slitPlane

lemma good_of_im_ne_zero {l : List Fac} (hs : ∀ a ∈ l, a.s ≠ 0) {z : ℂ} (hz : z.im ≠ 0) :
    Good l z := fun a ha => a.α_mem_slitPlane (hs a ha) hz

lemma hasDerivAt_psiL (l : List Fac) {z : ℂ} (hz : Good l z) :
    HasDerivAt (psiL l) (dpsiL l z) z := by
  induction l with
  | nil => simpa [psiL, dpsiL] using hasDerivAt_const z (0 : ℂ)
  | cons a l ih =>
    have hgood : Good l z := fun b hb => hz b (List.mem_cons_of_mem a hb)
    have ha : a.α z ∈ slitPlane := hz a List.mem_cons_self
    have hne : a.α z ≠ 0 := slitPlane_ne_zero ha
    have h1 := a.hasDerivAt_α z
    have h2 := h1.clog ha
    have h3 := (h1.mul h2).const_mul (a.c : ℂ)
    have h4 := h3.add (ih hgood)
    have hfun : (fun w => (a.c : ℂ) * (a.α w * log (a.α w)) + psiL l w) = psiL (a :: l) := by
      funext w; rfl
    rw [← hfun]
    convert h4 using 1
    simp only [dpsiL]
    field_simp

lemma hasDerivAt_dpsiL (l : List Fac) {z : ℂ} (hz : Good l z) :
    HasDerivAt (dpsiL l) (d2psiL l z) z := by
  induction l with
  | nil => simpa [dpsiL, d2psiL] using hasDerivAt_const z (0 : ℂ)
  | cons a l ih =>
    have hgood : Good l z := fun b hb => hz b (List.mem_cons_of_mem a hb)
    have ha : a.α z ∈ slitPlane := hz a List.mem_cons_self
    have h1 := a.hasDerivAt_α z
    have h2 := ((h1.clog ha).add_const (1 : ℂ)).const_mul (a.s : ℂ) |>.const_mul (a.c : ℂ)
    have h4 := h2.add (ih hgood)
    have hfun : (fun w => (a.c : ℂ) * ((a.s : ℂ) * (log (a.α w) + 1)) + dpsiL l w)
        = dpsiL (a :: l) := by
      funext w; rfl
    rw [← hfun]
    convert h4 using 1
    simp only [d2psiL]
    ring

/-! ## Box versions -/

section Boxes

variable (p n : ℕ)

def psiB : List Fac → CB → CB
  | [], _ => CB.ofQ 0 0
  | a :: l, B => ((((a.αB B).mul (clogCB p n (a.αB B))).smul (a.c : ℚ))).add (psiB l B)

def dpsiB : List Fac → CB → CB
  | [], _ => CB.ofQ 0 0
  | a :: l, B => (((clogCB p n (a.αB B)).add (CB.ofQ 1 0)).smul ((a.c : ℚ) * a.s)).add (dpsiB l B)

def d2psiB : List Fac → CB → CB
  | [], _ => CB.ofQ 0 0
  | a :: l, B => ((CB.inv (a.αB B)).smul ((a.c : ℚ) * a.s * a.s)).add (d2psiB l B)

lemma mem_zero : (CB.ofQ 0 0).mem 0 := by
  have := CB.mem_ofQ 0 0
  have he : (⟨((0 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = 0 := by apply Complex.ext <;> simp
  rwa [he] at this

lemma mem_one : (CB.ofQ 1 0).mem 1 := by
  have := CB.mem_ofQ 1 0
  have he : (⟨((1 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = 1 := by apply Complex.ext <;> simp
  rwa [he] at this

lemma mem_psiB (l : List Fac) {B : CB} {z : ℂ} (hz : B.mem z) : (psiB p n l B).mem (psiL l z) := by
  induction l with
  | nil => exact mem_zero
  | cons a l ih =>
    have hα := a.mem_αB hz
    have h := CB.mem_add (CB.mem_smul (a.c : ℚ) (CB.mem_mul hα (mem_clogCB p n hα))) ih
    simp only [psiB, psiL]
    convert h using 2
    push_cast; ring

lemma mem_dpsiB (l : List Fac) {B : CB} {z : ℂ} (hz : B.mem z) :
    (dpsiB p n l B).mem (dpsiL l z) := by
  induction l with
  | nil => exact mem_zero
  | cons a l ih =>
    have hα := a.mem_αB hz
    have h := CB.mem_add
      (CB.mem_smul ((a.c : ℚ) * a.s) (CB.mem_add (mem_clogCB p n hα) mem_one)) ih
    simp only [dpsiB, dpsiL]
    convert h using 2
    push_cast; ring

end Boxes

lemma mem_d2psiB (l : List Fac) {B : CB} {z : ℂ} (hz : B.mem z) :
    (d2psiB l B).mem (d2psiL l z) := by
  induction l with
  | nil => exact mem_zero
  | cons a l ih =>
    have hα := a.mem_αB hz
    have h := CB.mem_add (CB.mem_smul ((a.c : ℚ) * a.s * a.s) (CB.mem_inv hα)) ih
    simp only [d2psiB, d2psiL]
    convert h using 2
    push_cast; ring

/-! ## Third derivative and its bound on a disc -/

noncomputable def d3psiL : List Fac → ℂ → ℂ
  | [], _ => 0
  | a :: l, z => (a.c : ℂ) * (-((a.s : ℂ) * (a.s : ℂ) * (a.s : ℂ)) / a.α z ^ 2) + d3psiL l z

lemma hasDerivAt_d2psiL (l : List Fac) {z : ℂ} (hz : Good l z) :
    HasDerivAt (d2psiL l) (d3psiL l z) z := by
  induction l with
  | nil => simpa [d2psiL, d3psiL] using hasDerivAt_const z (0 : ℂ)
  | cons a l ih =>
    have hgood : Good l z := fun b hb => hz b (List.mem_cons_of_mem a hb)
    have ha : a.α z ∈ slitPlane := hz a List.mem_cons_self
    have hne : a.α z ≠ 0 := slitPlane_ne_zero ha
    have h1 := ((a.hasDerivAt_α z).inv hne).const_mul ((a.c : ℂ) * ((a.s : ℂ) * (a.s : ℂ)))
    have h4 := h1.add (ih hgood)
    have hfun : (fun w => (a.c : ℂ) * ((a.s : ℂ) * (a.s : ℂ)) * (a.α w)⁻¹ + d2psiL l w)
        = d2psiL (a :: l) := by
      funext w; simp only [d2psiL]; ring
    rw [← hfun]
    convert h4 using 1
    simp only [d3psiL]
    ring

/-- `Σ |c| |s|³ / m²`. -/
def d3bnd : List (Fac × ℚ) → ℚ
  | [] => 0
  | (a, m) :: l => |(a.c : ℚ)| * |(a.s : ℚ)| ^ 3 / m ^ 2 + d3bnd l

/-- Check: every `|α_i|` is `≥ m_i + |s_i| r` on the box `P` (and `m_i > 0`). -/
def d3chk (P : CB) (r : ℚ) : List (Fac × ℚ) → Bool
  | [] => true
  | (a, m) :: l => decide (0 < m) && (a.αB P).normGe (m + |(a.s : ℚ)| * r) && d3chk P r l

lemma norm_intCast_eq (k : ℤ) : ‖(k : ℂ)‖ = |(k : ℝ)| := by
  rw [show ((k : ℂ)) = ((k : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]

lemma norm_α_sub (a : Fac) (z c : ℂ) : ‖a.α z - a.α c‖ = |(a.s : ℝ)| * ‖z - c‖ := by
  have : a.α z - a.α c = (a.s : ℂ) * (z - c) := by simp only [Fac.α]; ring
  rw [this, norm_mul, norm_intCast_eq]

/-- `‖Ψ'''(z)‖ ≤ Σ |c| |s|³ / m²` for `‖z - c‖ ≤ r`, if `c ∈ P` and `d3chk P r l`. -/
lemma norm_d3psiL_le (l : List (Fac × ℚ)) {P : CB} {c z : ℂ} {r : ℚ} (hc : P.mem c)
    (hz : ‖z - c‖ ≤ r) (h : d3chk P r l = true) :
    ‖d3psiL (l.map Prod.fst) z‖ ≤ d3bnd l := by
  induction l with
  | nil => simp [d3psiL, d3bnd]
  | cons am l ih =>
    obtain ⟨a, m⟩ := am
    simp only [d3chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hm, hn⟩, hl⟩ := h
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 := CB.le_norm_of_normGe (a.mem_αB hc) hn
    have h2 := norm_α_sub a z c
    have hαz : (m : ℝ) ≤ ‖a.α z‖ := by
      have h3 : ‖a.α c‖ - ‖a.α z - a.α c‖ ≤ ‖a.α z‖ := by
        have := norm_sub_norm_le (a.α c) (a.α c - a.α z)
        rw [sub_sub_cancel, norm_sub_rev] at this; linarith
      push_cast at h1
      have : |(a.s : ℝ)| * ‖z - c‖ ≤ |(a.s : ℝ)| * r :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      linarith
    have hpos : 0 < ‖a.α z‖ := hm'.trans_le hαz
    simp only [List.map_cons, d3psiL, d3bnd]
    push_cast
    refine (norm_add_le _ _).trans (add_le_add ?_ (ih hl))
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, norm_intCast_eq,
      norm_intCast_eq]
    have : |(a.s : ℝ)| * |(a.s : ℝ)| * |(a.s : ℝ)| / ‖a.α z‖ ^ 2
        ≤ |(a.s : ℝ)| ^ 3 / (m : ℝ) ^ 2 := by
      rw [show |(a.s : ℝ)| * |(a.s : ℝ)| * |(a.s : ℝ)| = |(a.s : ℝ)| ^ 3 by ring]
      gcongr
    calc |(a.c : ℝ)| * (|(a.s : ℝ)| * |(a.s : ℝ)| * |(a.s : ℝ)| / ‖a.α z‖ ^ 2)
        ≤ |(a.c : ℝ)| * (|(a.s : ℝ)| ^ 3 / (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |(a.c : ℝ)| * |(a.s : ℝ)| ^ 3 / (m : ℝ) ^ 2 := by ring

end ZetaIrr.Interval
