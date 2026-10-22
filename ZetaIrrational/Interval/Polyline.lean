/-
# Polylines, connectors and vertical rays (machinery for (S2) and (S3))

* `polyChk` / `poly_bound`: `Re f ≤ T` on every segment of a rational polyline (via `segOK`).
* `ballOK` / `ball_bound`: `Re f ≤ T` on a closed disc around a rational point (used for the short
  connector between the exact Taylor-disc endpoint `x₀ ± ρ d` and the first rational vertex).
* `rayPts` / `ray_pts`, `im_dpsiL_ge_tail`: lower bounds for `Im Ψ'(X + i y)` on a vertical ray
  (box evaluation on a list of `y`-intervals, and the analytic tail
  `Im Ψ' ≥ (π/2) Σ c - Σ |c| |s X + κ| / y` for factors with `s = ±1`).
* `ray_h_decreasing`: if `Im Ψ' ≥ ωπ + η` on the vertical ray, then `y ↦ h(X + i y) + η y` is
  antitone (so `h` decreases at rate `η`).
-/
import ZetaIrrational.Interval.Segment
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ZetaIrr.Interval

open Complex Metric IV Real

/-! ## Polylines -/

/-- `z` lies on the polyline `a, pts₀, pts₁, …`. -/
def onPoly : (ℚ × ℚ) → List (ℚ × ℚ) → ℂ → Prop
  | _, [], _ => False
  | a, b :: rest, z => z ∈ segment ℝ (toC a) (toC b) ∨ onPoly b rest z

def polyChk (ω p n : ℕ) (l : List Fac) (T : ℚ) : (ℚ × ℚ) → List (ℚ × ℚ) → Bool
  | _, [] => true
  | a, b :: rest => segOK p l T a b (fgAt ω p n l a) (fgAt ω p n l b) && polyChk ω p n l T b rest

theorem poly_bound (ω p n : ℕ) (l : List Fac) (T : ℚ) (a : ℚ × ℚ) (pts : List (ℚ × ℚ))
    (h : polyChk ω p n l T a pts = true) : ∀ z, onPoly a pts z → (fL ω l z).re ≤ T := by
  induction pts generalizing a with
  | nil => intro z hz; exact hz.elim
  | cons b rest ih =>
    simp only [polyChk, Bool.and_eq_true] at h
    intro z hz
    rcases hz with hz | hz
    · exact seg_bound ω p n l T a b h.1 z hz
    · exact ih b h.2 z hz

/-! ## Discs around rational points -/

/-- `max |lo| |hi|`. -/
def absHi : IV → ℚ
  | top => 0
  | ival a b => max |a| |b|

lemma abs_le_absHi {a b : ℚ} {x : ℝ} (hx : (ival a b).mem x) : |x| ≤ absHi (ival a b) := by
  obtain ⟨h1, h2⟩ := hx
  simp only [absHi, Rat.cast_max, Rat.cast_abs]
  rw [abs_le]
  constructor
  · have := neg_abs_le (a : ℝ); have := le_max_left |(a : ℝ)| |(b : ℝ)|; linarith
  · have := le_abs_self (b : ℝ); have := le_max_right |(a : ℝ)| |(b : ℝ)|; linarith

lemma norm_le_absHi {B : CB} {z : ℂ} (hz : B.mem z) {a b c d : ℚ} (h1 : B.re = ival a b)
    (h2 : B.im = ival c d) : ‖z‖ ≤ absHi (ival a b) + absHi (ival c d) := by
  have hr := hz.1; have hi := hz.2
  rw [h1] at hr; rw [h2] at hi
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ _ := add_le_add (abs_le_absHi hr) (abs_le_absHi hi)

/-- Check `Re f ≤ T` on `closedBall v D` (with `D ≥ 0`). -/
def ballOK (ω p n : ℕ) (l : List Fac) (T : ℚ) (v : ℚ × ℚ) (D : ℚ) : Bool :=
  let F := fgAt ω p n l v
  let B := CB.ofQRad v.1 v.2 D
  let C := d2psiBr p l B
  match F.1.re, F.2.re, F.2.im, C.re, C.im with
  | ival _ hv, ival g1 g2, ival g3 g4, ival c1 c2, ival c3 c4 =>
    decide (0 ≤ D ∧ hv + (absHi (ival g1 g2) + absHi (ival g3 g4)) * D
      + (absHi (ival c1 c2) + absHi (ival c3 c4)) * D ^ 2 ≤ T) && goodB l B
  | _, _, _, _, _ => false

theorem ball_bound (ω p n : ℕ) (l : List Fac) (T : ℚ) (v : ℚ × ℚ) (D : ℚ)
    (h : ballOK ω p n l T v D = true) : ∀ z ∈ closedBall (toC v) D, (fL ω l z).re ≤ T := by
  intro z hz
  have hF := mem_fgAt ω p n l v
  have hbox : ∀ w ∈ closedBall (toC v) D, (CB.ofQRad v.1 v.2 D).mem w := by
    intro w hw
    apply CB.mem_ofQRad
    rw [mem_closedBall, dist_eq_norm] at hw
    exact hw
  dsimp only [ballOK] at h
  split at h
  · rename_i _ hv g1 g2 g3 g4 c1 c2 c3 c4 e1 e2 e3 e4 e5
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hD, hT⟩, hgB⟩ := h
    set Gq : ℚ := absHi (ival g1 g2) + absHi (ival g3 g4) with hGq
    set Cq : ℚ := absHi (ival c1 c2) + absHi (ival c3 c4) with hCq
    have hsub : segment ℝ (toC v) z ⊆ closedBall (toC v) D :=
      (convex_closedBall _ _).segment_subset (mem_closedBall_self (by exact_mod_cast hD)) hz
    have hgood : ∀ w ∈ segment ℝ (toC v) z, Good l w :=
      fun w hw => good_of_goodB (hbox w (hsub hw)) hgB
    have hC : ∀ w ∈ segment ℝ (toC v) z, ‖d2psiL l w‖ ≤ (Cq : ℝ) := by
      intro w hw
      have := norm_le_absHi (mem_d2psiBr p l (hbox w (hsub hw))) e4 e5
      rw [hCq]; push_cast; exact this
    have hTay := taylor2_seg (F := fL ω l) (G := gL ω l) (G' := d2psiL l) (a := toC v) (z := z)
      (fun w hw => hasDerivAt_fL (hgood w hw)) (fun w hw => hasDerivAt_gL (hgood w hw)) hC
    have hG : ‖gL ω l (toC v)‖ ≤ (Gq : ℝ) := by
      have := norm_le_absHi hF.2 e2 e3
      rw [hGq]; push_cast; exact this
    have hfv : (fL ω l (toC v)).re ≤ hv := by
      have := hF.1.1; rw [e1] at this; exact_mod_cast this.2
    have hzv : ‖z - toC v‖ ≤ D := by rw [← dist_eq_norm]; exact hz
    have hre := (Complex.re_le_norm _).trans hTay
    simp only [sub_re] at hre
    have hlin : (gL ω l (toC v) * (z - toC v)).re ≤ (Gq : ℝ) * D := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul]
      exact mul_le_mul hG hzv (norm_nonneg _) ((norm_nonneg _).trans hG)
    have hC0 : (0 : ℝ) ≤ (Cq : ℝ) := (norm_nonneg _).trans (hC _ (left_mem_segment ℝ _ _))
    have hq : (Cq : ℝ) * ‖z - toC v‖ ^ 2 ≤ (Cq : ℝ) * (D : ℝ) ^ 2 := by gcongr
    have hT' : ((hv + Gq * D + Cq * D ^ 2 : ℚ) : ℝ) ≤ T := by exact_mod_cast hT
    have hT'' : (hv : ℝ) + (Gq : ℝ) * D + (Cq : ℝ) * (D : ℝ) ^ 2 ≤ T := by
      push_cast at hT' ⊢; linarith
    linarith
  · simp at h

/-! ## Sector bounds -/

/-! ## Upper half plane -/

/-! ## Vertical rays -/

/-- Box checks `Im Ψ' ≥ q` on `{X} × [y_i, y_{i+1}]` for consecutive breakpoints. -/
def rayPts (p n : ℕ) (l : List Fac) (X q : ℚ) : List ℚ → Bool
  | y1 :: y2 :: rest =>
    (dpsiB p n l ⟨ofRat X, ival y1 y2⟩).im.loGe q && rayPts p n l X q (y2 :: rest)
  | _ => true

theorem ray_pts (p n : ℕ) (l : List Fac) (X q : ℚ) (y1 y2 : ℚ) (rest : List ℚ)
    (h : rayPts p n l X q (y1 :: y2 :: rest) = true) :
    ∀ y : ℝ, (y1 : ℝ) ≤ y → y ≤ ((y2 :: rest).getLast (by simp) : ℚ) →
      (q : ℝ) ≤ (dpsiL l ⟨X, y⟩).im := by
  induction rest generalizing y1 y2 with
  | nil =>
    simp only [rayPts, Bool.and_eq_true] at h
    intro y h1 h2
    simp only [List.getLast_singleton] at h2
    have hm : (CB.mk (ofRat X) (ival y1 y2)).mem ⟨X, y⟩ := ⟨mem_ofRat X, h1, h2⟩
    exact ge_of_loGe (mem_dpsiB p n l hm).2 h.1
  | cons y3 rest ih =>
    change ((dpsiB p n l ⟨ofRat X, ival y1 y2⟩).im.loGe q
      && rayPts p n l X q (y2 :: y3 :: rest)) = true at h
    rw [Bool.and_eq_true] at h
    intro y h1 h2
    rcases le_total y y2 with hy | hy
    · have hm : (CB.mk (ofRat X) (ival y1 y2)).mem ⟨X, y⟩ := ⟨mem_ofRat X, h1, hy⟩
      exact ge_of_loGe (mem_dpsiB p n l hm).2 h.1
    · exact ih y2 y3 h.2 y hy (by simpa using h2)

/-- `Σ c`. -/
def csum : List Fac → ℚ
  | [] => 0
  | f :: l => (f.c : ℚ) + csum l

/-- `Σ |c| |s X + κ|`. -/
def tailB (X : ℚ) : List Fac → ℚ
  | [] => 0
  | f :: l => |(f.c : ℚ)| * |(f.s : ℚ) * X + f.κ| + tailB X l

lemma arg_term (f : Fac) (hs : f.s = 1 ∨ f.s = -1) {z : ℂ} (hz : 0 < z.im) :
    (f.c : ℝ) * f.s * arg (f.α z) = f.c * (π / 2)
      - f.c * f.s * Real.arctan ((f.α z).re / (f.α z).im) := by
  rcases hs with h | h
  · have hs' : (f.s : ℝ) = 1 := by exact_mod_cast h
    have him : 0 < (f.α z).im := by simp [Fac.α, h, hz]
    rw [arg_eq_of_im_pos him, hs']; ring
  · have hs' : (f.s : ℝ) = -1 := by exact_mod_cast h
    have him : (f.α z).im < 0 := by simp [Fac.α, h, hz]
    rw [arg_eq_of_im_neg him, hs']; ring

lemma im_dpsiL (l : List Fac) (z : ℂ) :
    (dpsiL l z).im = (l.map fun f => (f.c : ℝ) * f.s * arg (f.α z)).sum := by
  induction l with
  | nil => simp [dpsiL]
  | cons f l ih =>
    simp only [dpsiL, List.map_cons, List.sum_cons, add_im, ih]
    congr 1
    have h1 : ((f.c : ℂ) * ((f.s : ℂ) * (log (f.α z) + 1))) =
        (((f.c : ℝ) * f.s : ℝ) : ℂ) * (log (f.α z) + 1) := by push_cast; ring
    rw [h1, im_ofReal_mul, add_im, log_im, one_im, add_zero]

/-- **Analytic tail** for factor lists with `s = ±1`: on `Re z = X`, `Im z > 0`,
`Im Ψ'(z) ≥ (π/2) Σ c - Σ |c| |s X + κ| / Im z`. -/
theorem im_dpsiL_ge_tail (l : List Fac) (hs : ∀ f ∈ l, f.s = 1 ∨ f.s = -1) (X : ℚ) {z : ℂ}
    (hzX : z.re = X) (hz : 0 < z.im) :
    π / 2 * csum l - tailB X l / z.im ≤ (dpsiL l z).im := by
  rw [im_dpsiL]
  induction l with
  | nil => simp [csum, tailB]
  | cons f l ih =>
    have hf := hs f List.mem_cons_self
    have hl := ih (fun g hg => hs g (List.mem_cons_of_mem f hg))
    simp only [List.map_cons, List.sum_cons, csum, tailB]
    rw [arg_term f hf hz]
    have hims : |(f.α z).im| = z.im := by
      rcases hf with h | h <;> simp [Fac.α, h, abs_of_pos hz]
    have hre : (f.α z).re = (((f.s : ℚ) * X + f.κ : ℚ) : ℝ) := by
      simp [Fac.α, hzX]
    have hcs : |(f.c : ℝ) * f.s| = |(f.c : ℝ)| := by
      rcases hf with h | h <;> simp [h]
    have hat : |(f.c : ℝ) * f.s * Real.arctan ((f.α z).re / (f.α z).im)|
        ≤ |((f.c : ℚ) : ℝ)| * |(((f.s : ℚ) * X + f.κ : ℚ) : ℝ)| / z.im := by
      rw [abs_mul, hcs]
      have : |Real.arctan ((f.α z).re / (f.α z).im)|
          ≤ |(((f.s : ℚ) * X + f.κ : ℚ) : ℝ)| / z.im := by
        calc _ ≤ |(f.α z).re / (f.α z).im| := Real.abs_arctan_le_abs
          _ = _ := by rw [abs_div, hims, hre]
      have hc0 := abs_nonneg ((f.c : ℝ))
      calc |(f.c : ℝ)| * |Real.arctan ((f.α z).re / (f.α z).im)|
          ≤ |(f.c : ℝ)| * (|(((f.s : ℚ) * X + f.κ : ℚ) : ℝ)| / z.im) :=
            mul_le_mul_of_nonneg_left this hc0
        _ = _ := by push_cast; ring
    have := neg_abs_le ((f.c : ℝ) * f.s * Real.arctan ((f.α z).re / (f.α z).im))
    push_cast at hl hat this ⊢
    have e : (π / 2 * (↑f.c + csum l) - (|(f.c : ℝ)| * |(f.s : ℝ) * X + f.κ| + tailB X l) / z.im)
        = (f.c * (π / 2) - |(f.c : ℝ)| * |(f.s : ℝ) * X + f.κ| / z.im)
          + (π / 2 * csum l - tailB X l / z.im) := by ring
    rw [e]
    have := abs_le.1 hat
    linarith [this.1]

/-- If `Im Ψ' ≥ ωπ + η` on the vertical ray `X + i y`, `y ≥ y0`, then `h` decreases at rate `η`:
`h(X + i y₂) ≤ h(X + i y₁) - η (y₂ - y₁)` for `y0 ≤ y₁ ≤ y₂`. -/
theorem ray_h_decreasing (ω : ℕ) (l : List Fac) (X y0 η : ℝ)
    (hgood : ∀ y, y0 ≤ y → Good l ((X : ℂ) + y * I))
    (hη : ∀ y, y0 ≤ y → ω * π + η ≤ (dpsiL l ((X : ℂ) + y * I)).im)
    {y1 y2 : ℝ} (h1 : y0 ≤ y1) (h12 : y1 ≤ y2) :
    (fL ω l ((X : ℂ) + y2 * I)).re ≤ (fL ω l ((X : ℂ) + y1 * I)).re - η * (y2 - y1) := by
  set φ : ℝ → ℝ := fun y => (fL ω l ((X : ℂ) + y * I)).re with hφ
  have hd : ∀ y, y0 ≤ y → HasDerivAt φ (gL ω l ((X : ℂ) + y * I) * I).re y := by
    intro y hy
    have hz : HasDerivAt (fun w : ℂ => (X : ℂ) + w * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (X : ℂ)
    have hc := (hasDerivAt_fL (ω := ω) (hgood y hy)).comp (y : ℂ) hz
    exact hc.real_of_complex
  have hval : ∀ y, y0 ≤ y → (gL ω l ((X : ℂ) + y * I) * I).re ≤ -η := by
    intro y hy
    have := hη y hy
    simp only [mul_I_re, gL, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    simp
    linarith
  have hmv := (convex_Ici y0).image_sub_le_mul_sub_of_deriv_le (f := φ) (C := -η)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => by
      rw [interior_Ici] at hy
      exact (hd y (le_of_lt hy)).differentiableAt.differentiableWithinAt)
    (fun y hy => by
      rw [interior_Ici] at hy
      rw [(hd y (le_of_lt hy)).deriv]; exact hval y (le_of_lt hy))
    y1 h1 y2 (h1.trans h12) h12
  simp only [hφ] at hmv
  linarith

end ZetaIrr.Interval
