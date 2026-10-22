/-
# Certified bounds for `h = Re f` along polylines (far part (S2) machinery)

For a factor list `l` and a phase multiplier `ω : ℕ`, `fL ω l z = Ψ(z) - ωπi z` and
`gL ω l z = Ψ'(z) - ωπi` (the proof of the main theorem uses `ω = 3`).

**Segment bound.** For `z = a + t (b - a)`, `t ∈ [0, 1/2]`, the second-order Taylor bound
(`taylor2_seg`, from the mean value inequality applied twice) gives

    h(z) ≤ h(a) + t Re(g(a)(b - a)) + C |z - a|² ≤ h(a) + max(0, λ_a)/2 + C L²/4,

with `λ_a = Re(g(a)(b - a))`, `L = |b - a|`, `C ≥ sup |Ψ''|` on the segment; symmetrically from
`b` for `t ≥ 1/2`. `segOK` checks `X + C L²/4 ≤ T` (squared, to avoid square roots) with `X` the
larger of the two endpoint terms; the point values `f(a), g(a)` come from a shared box evaluation
`fgB` at the rational vertex, `C` from the rational box evaluation of `Ψ''` on the segment's
bounding box.

`polyChk` runs `segOK` along a list of rational vertices; `poly_bound` turns a successful check into
`∀ z` on the polyline, `Re f z ≤ T`. `ball_bound` handles a short connector near a non-rational
point.
-/
import ZetaIrrational.Interval.Psi
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex

namespace ZetaIrr.Interval

open Complex Metric IV Real

/-! ## Second-order Taylor bound on a segment -/

lemma taylor2_seg {F G G' : ℂ → ℂ} {a z : ℂ} {C : ℝ}
    (hF : ∀ w ∈ segment ℝ a z, HasDerivAt F (G w) w)
    (hG : ∀ w ∈ segment ℝ a z, HasDerivAt G (G' w) w)
    (hC : ∀ w ∈ segment ℝ a z, ‖G' w‖ ≤ C) :
    ‖F z - F a - G a * (z - a)‖ ≤ C * ‖z - a‖ ^ 2 := by
  have ha : a ∈ segment ℝ a z := left_mem_segment ℝ a z
  have hz : z ∈ segment ℝ a z := right_mem_segment ℝ a z
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a ha)
  have hconv := convex_segment (𝕜 := ℝ) a z
  -- `‖G w - G a‖ ≤ C ‖z - a‖` on the segment
  have hGb : ∀ w ∈ segment ℝ a z, ‖G w - G a‖ ≤ C * ‖z - a‖ := by
    intro w hw
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hG x hx).hasDerivWithinAt) hC ha hw
    exact this.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hw) hC0)
  set H : ℂ → ℂ := fun w => F w - F a - G a * (w - a) with hH
  have hHd : ∀ w ∈ segment ℝ a z, HasDerivWithinAt H (G w - G a) (segment ℝ a z) w := by
    intro w hw
    have h1 : HasDerivAt H (G w - G a * 1) w :=
      ((hF w hw).sub_const (F a)).sub (((hasDerivAt_id w).sub_const a).const_mul (G a))
    rw [mul_one] at h1
    exact h1.hasDerivWithinAt
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hHd hGb ha hz
  simp only [hH, sub_self, mul_zero, sub_zero] at this
  calc ‖F z - F a - G a * (z - a)‖ ≤ C * ‖z - a‖ * ‖z - a‖ := this
    _ = C * ‖z - a‖ ^ 2 := by ring

/-! ## Phase functions and point evaluation -/

noncomputable def fL (ω : ℕ) (l : List Fac) (z : ℂ) : ℂ := psiL l z - ω * π * I * z
noncomputable def gL (ω : ℕ) (l : List Fac) (z : ℂ) : ℂ := dpsiL l z - ω * π * I

lemma hasDerivAt_fL {ω : ℕ} {l : List Fac} {z : ℂ} (hz : Good l z) : HasDerivAt (fL ω l) (gL ω l z) z := by
  have := (hasDerivAt_psiL l hz).sub ((hasDerivAt_id z).const_mul ((ω : ℂ) * π * I))
  rw [mul_one] at this
  exact this

lemma hasDerivAt_gL {ω : ℕ} {l : List Fac} {z : ℂ} (hz : Good l z) :
    HasDerivAt (gL ω l) (d2psiL l z) z :=
  (hasDerivAt_dpsiL l hz).sub_const ((ω : ℂ) * π * I)

/-- Box for `ωπi`. -/
def phIB (ω : ℕ) : CB := ⟨ofRat 0, piI.smul ω⟩

lemma mem_phIB (ω : ℕ) : (phIB ω).mem ((ω : ℂ) * π * I) := by
  refine ⟨?_, ?_⟩
  · have h : ((ω : ℂ) * (π : ℂ) * I).re = ((0 : ℚ) : ℝ) := by simp
    rw [h]; exact mem_ofRat 0
  · have h : ((ω : ℂ) * (π : ℂ) * I).im = ((ω : ℚ) : ℝ) * π := by simp
    rw [h]; exact mem_smul (ω : ℚ) mem_piI

/-- Shared evaluation of `(Ψ, Ψ')` on a box: the logs are computed once. -/
def fgB (p n : ℕ) : List Fac → CB → CB × CB
  | [], _ => (CB.ofQ 0 0, CB.ofQ 0 0)
  | a :: l, B =>
    let A := a.αB B
    let L := clogCB p n A
    let r := fgB p n l B
    ((((A.mul L).smul (a.c : ℚ)).round p).add r.1,
      (((L.add (CB.ofQ 1 0)).smul ((a.c : ℚ) * a.s)).round p).add r.2)

lemma mem_fgB (p n : ℕ) (l : List Fac) {B : CB} {z : ℂ} (hz : B.mem z) :
    (fgB p n l B).1.mem (psiL l z) ∧ (fgB p n l B).2.mem (dpsiL l z) := by
  induction l with
  | nil => exact ⟨mem_zero, mem_zero⟩
  | cons a l ih =>
    have hα := a.mem_αB hz
    have hL := mem_clogCB p n hα
    constructor
    · have h := CB.mem_add (CB.mem_round p (CB.mem_smul (a.c : ℚ) (CB.mem_mul hα hL))) ih.1
      simp only [fgB, psiL]
      convert h using 2
      push_cast; ring
    · have h := CB.mem_add (CB.mem_round p (CB.mem_smul ((a.c : ℚ) * a.s) (CB.mem_add hL mem_one)))
        ih.2
      simp only [fgB, dpsiL]
      convert h using 2
      push_cast; ring

/-- `Ψ''` on a box, with outward rounding of every term. -/
def d2psiBr (p : ℕ) : List Fac → CB → CB
  | [], _ => CB.ofQ 0 0
  | a :: l, B => (((CB.inv (a.αB B)).smul ((a.c : ℚ) * a.s * a.s)).round p).add (d2psiBr p l B)

lemma mem_d2psiBr (p : ℕ) (l : List Fac) {B : CB} {z : ℂ} (hz : B.mem z) :
    (d2psiBr p l B).mem (d2psiL l z) := by
  induction l with
  | nil => exact mem_zero
  | cons a l ih =>
    have hα := a.mem_αB hz
    have h := CB.mem_add (CB.mem_round p (CB.mem_smul ((a.c : ℚ) * a.s * a.s) (CB.mem_inv hα))) ih
    simp only [d2psiBr, d2psiL]
    convert h using 2
    push_cast; ring

/-- The complex number of a rational pair. -/
def toC (v : ℚ × ℚ) : ℂ := ⟨(v.1 : ℝ), (v.2 : ℝ)⟩

/-- `(f, g)` boxes at a rational vertex. -/
def fgAt (ω p n : ℕ) (l : List Fac) (v : ℚ × ℚ) : CB × CB :=
  let P := CB.ofQ v.1 v.2
  let r := fgB p n l P
  (r.1.sub ((phIB ω).mul P), r.2.sub (phIB ω))

lemma mem_fgAt (ω p n : ℕ) (l : List Fac) (v : ℚ × ℚ) :
    (fgAt ω p n l v).1.mem (fL ω l (toC v)) ∧ (fgAt ω p n l v).2.mem (gL ω l (toC v)) := by
  have hP : (CB.ofQ v.1 v.2).mem (toC v) := CB.mem_ofQ v.1 v.2
  have h := mem_fgB p n l hP
  exact ⟨CB.mem_sub h.1 (CB.mem_mul (mem_phIB ω) hP), CB.mem_sub h.2 (mem_phIB ω)⟩

/-! ## Boxes around segments and the slit-plane condition -/

/-- Bounding box of the segment `[a, b]`. -/
def segBox (a b : ℚ × ℚ) : CB :=
  ⟨ival (min a.1 b.1) (max a.1 b.1), ival (min a.2 b.2) (max a.2 b.2)⟩

lemma combo_mem {s t x y : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    min x y ≤ s * x + t * y ∧ s * x + t * y ≤ max x y := by
  constructor
  · have h1 : s * min x y ≤ s * x := mul_le_mul_of_nonneg_left (min_le_left _ _) hs
    have h2 : t * min x y ≤ t * y := mul_le_mul_of_nonneg_left (min_le_right _ _) ht
    have h3 : s * min x y + t * min x y = min x y := by rw [← add_mul, hst, one_mul]
    linarith
  · have h1 : s * x ≤ s * max x y := mul_le_mul_of_nonneg_left (le_max_left _ _) hs
    have h2 : t * y ≤ t * max x y := mul_le_mul_of_nonneg_left (le_max_right _ _) ht
    have h3 : s * max x y + t * max x y = max x y := by rw [← add_mul, hst, one_mul]
    linarith

lemma mem_segBox {a b : ℚ × ℚ} {z : ℂ} (hz : z ∈ segment ℝ (toC a) (toC b)) :
    (segBox a b).mem z := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  have h1 := combo_mem (x := (a.1 : ℝ)) (y := (b.1 : ℝ)) hs ht hst
  have h2 := combo_mem (x := (a.2 : ℝ)) (y := (b.2 : ℝ)) hs ht hst
  have hre : (s • toC a + t • toC b).re = s * (a.1 : ℝ) + t * (b.1 : ℝ) := by simp [toC]
  have him : (s • toC a + t • toC b).im = s * (a.2 : ℝ) + t * (b.2 : ℝ) := by simp [toC]
  refine ⟨?_, ?_⟩
  · change ((min a.1 b.1 : ℚ) : ℝ) ≤ _ ∧ _ ≤ ((max a.1 b.1 : ℚ) : ℝ)
    rw [hre, Rat.cast_min, Rat.cast_max]; exact h1
  · change ((min a.2 b.2 : ℚ) : ℝ) ≤ _ ∧ _ ≤ ((max a.2 b.2 : ℚ) : ℝ)
    rw [him, Rat.cast_min, Rat.cast_max]; exact h2

/-- Box check that every `α_i` is in the slit plane. -/
def goodB : List Fac → CB → Bool
  | [], _ => true
  | a :: l, B => ((a.αB B).re.loGt 0 || (a.αB B).im.loGt 0 || (a.αB B).im.hiLt 0) && goodB l B

lemma good_of_goodB {l : List Fac} {B : CB} {z : ℂ} (hz : B.mem z) (h : goodB l B = true) :
    Good l z := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons a l ih =>
    simp only [goodB, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · have hα := b.mem_αB hz
      rw [mem_slitPlane_iff]
      rcases h1 with (h | h) | h
      · left; exact_mod_cast gt_of_loGt hα.1 h
      · right; exact (by exact_mod_cast gt_of_loGt hα.2 h : (0 : ℝ) < _).ne'
      · right; exact (by exact_mod_cast lt_of_hiLt hα.2 h : _ < (0 : ℝ)).ne
    · exact ih h2 b hb

/-! ## The segment check -/

/-- Check `Re f ≤ T` on the segment `[a, b]`, given the vertex boxes `FA = fgAt a`,
`FB = fgAt b`. -/
def segOK (p : ℕ) (l : List Fac) (T : ℚ) (a b : ℚ × ℚ) (FA FB : CB × CB) : Bool :=
  let e := CB.ofQ (b.1 - a.1) (b.2 - a.2)
  let L2 := (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2
  let B := segBox a b
  match FA.1.re, (FA.2.mul e).re, FB.1.re, (FB.2.mul e.neg).re, CB.normSq (d2psiBr p l B) with
  | ival _ ha, ival _ la, ival _ hb, ival _ lb, ival _ S =>
    let X := max (ha + max 0 la / 2) (hb + max 0 lb / 2)
    decide (X ≤ T ∧ S * L2 ^ 2 ≤ 16 * (T - X) ^ 2) && goodB l B
  | _, _, _, _, _ => false

lemma toC_sub (a b : ℚ × ℚ) : toC b - toC a = ⟨((b.1 - a.1 : ℚ) : ℝ), ((b.2 - a.2 : ℚ) : ℝ)⟩ := by
  apply Complex.ext <;> simp [toC]

lemma normSq_toC_sub (a b : ℚ × ℚ) :
    ‖toC b - toC a‖ ^ 2 = (((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, toC_sub]; push_cast; ring

/-- One-sided half-segment bound. -/
lemma half_bound {ω : ℕ} {l : List Fac} {a b z : ℂ} {t C ha la : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hzt : z = a + t * (b - a))
    (hgood : ∀ w ∈ segment ℝ a b, Good l w) (hC : ∀ w ∈ segment ℝ a b, ‖d2psiL l w‖ ≤ C)
    (hha : (fL ω l a).re ≤ ha) (hla : (gL ω l a * (b - a)).re ≤ la) :
    (fL ω l z).re ≤ ha + max 0 la / 2 + C * ‖b - a‖ ^ 2 / 4 := by
  have hsub : segment ℝ a z ⊆ segment ℝ a b := by
    apply (convex_segment a b).segment_subset (left_mem_segment ℝ a b)
    rw [hzt, segment_eq_image']
    exact ⟨t, ⟨ht0, by linarith⟩, by simp⟩
  have hT := taylor2_seg (F := fL ω l) (G := gL ω l) (G' := d2psiL l) (a := a) (z := z) (C := C)
    (fun w hw => hasDerivAt_fL (hgood w (hsub hw)))
    (fun w hw => hasDerivAt_gL (hgood w (hsub hw))) (fun w hw => hC w (hsub hw))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a (left_mem_segment ℝ a b))
  have hre := (Complex.re_le_norm _).trans hT
  have hza : z - a = (t : ℂ) * (b - a) := by rw [hzt]; ring
  rw [hza, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at hre
  have hlin : (gL ω l a * ((t : ℂ) * (b - a))).re = t * (gL ω l a * (b - a)).re := by
    rw [show gL ω l a * ((t : ℂ) * (b - a)) = (t : ℂ) * (gL ω l a * (b - a)) by ring, re_ofReal_mul]
  simp only [sub_re] at hre
  rw [hlin] at hre
  have h1 : t * (gL ω l a * (b - a)).re ≤ max 0 la / 2 := by
    rcases le_total 0 (gL ω l a * (b - a)).re with hp | hn
    · calc t * (gL ω l a * (b - a)).re ≤ (1 / 2) * (gL ω l a * (b - a)).re :=
            mul_le_mul_of_nonneg_right ht hp
        _ ≤ max 0 la / 2 := by linarith [le_max_right 0 la]
    · have : t * (gL ω l a * (b - a)).re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hn
      linarith [le_max_left 0 la]
  have h2 : C * (t * ‖b - a‖) ^ 2 ≤ C * ‖b - a‖ ^ 2 / 4 := by
    have : (t * ‖b - a‖) ^ 2 ≤ ‖b - a‖ ^ 2 / 4 := by
      rw [mul_pow]
      have : t ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [sq_nonneg ‖b - a‖]
    nlinarith
  linarith

theorem seg_bound (ω p n : ℕ) (l : List Fac) (T : ℚ) (a b : ℚ × ℚ)
    (h : segOK p l T a b (fgAt ω p n l a) (fgAt ω p n l b) = true) :
    ∀ z ∈ segment ℝ (toC a) (toC b), (fL ω l z).re ≤ T := by
  intro z hz
  have hA := mem_fgAt ω p n l a
  have hB := mem_fgAt ω p n l b
  have heM : (CB.ofQ (b.1 - a.1) (b.2 - a.2)).mem (toC b - toC a) := by
    rw [toC_sub]; exact CB.mem_ofQ _ _
  have hla := (CB.mem_mul hA.2 heM).1
  have hlb := (CB.mem_mul hB.2 (CB.mem_neg heM)).1
  have hseg : ∀ w ∈ segment ℝ (toC a) (toC b), (segBox a b).mem w := fun w hw => mem_segBox hw
  dsimp only [segOK] at h
  split at h
  · rename_i ha0 ha la0 la hb0 hb lb0 lb S0 S e1 e2 e3 e4 e5
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hX, hS2⟩, hgB⟩ := h
    have hFa : (fL ω l (toC a)).re ≤ ha := by
      have := hA.1.1; rw [e1] at this; exact_mod_cast this.2
    have hFb : (fL ω l (toC b)).re ≤ hb := by
      have := hB.1.1; rw [e3] at this; exact_mod_cast this.2
    have hLa : (gL ω l (toC a) * (toC b - toC a)).re ≤ la := by
      rw [e2] at hla; exact_mod_cast hla.2
    have hLb : (gL ω l (toC b) * (toC a - toC b)).re ≤ lb := by
      rw [e4, show -(toC b - toC a) = toC a - toC b by ring] at hlb; exact_mod_cast hlb.2
    have hgood : ∀ w ∈ segment ℝ (toC a) (toC b), Good l w :=
      fun w hw => good_of_goodB (hseg w hw) hgB
    have hC : ∀ w ∈ segment ℝ (toC a) (toC b), ‖d2psiL l w‖ ≤ √(S : ℝ) := by
      intro w hw
      have := CB.mem_normSq (mem_d2psiBr p l (hseg w hw))
      rw [e5] at this
      have h2 : ‖d2psiL l w‖ ^ 2 ≤ (S : ℝ) := by rw [Complex.sq_norm]; exact this.2
      have := Real.abs_le_sqrt h2
      rwa [abs_of_nonneg (norm_nonneg _)] at this
    have hgood' : ∀ w ∈ segment ℝ (toC b) (toC a), Good l w := by
      rw [segment_symm]; exact hgood
    have hC' : ∀ w ∈ segment ℝ (toC b) (toC a), ‖d2psiL l w‖ ≤ √(S : ℝ) := by
      rw [segment_symm]; exact hC
    -- the curvature term
    set X := max (ha + max 0 la / 2) (hb + max 0 lb / 2) with hXdef
    have hL : √(S : ℝ) * ‖toC b - toC a‖ ^ 2 / 4 ≤ (T : ℝ) - X := by
      rw [normSq_toC_sub]
      have hTX : (0 : ℝ) ≤ (T : ℝ) - X := by
        have : (X : ℝ) ≤ T := by exact_mod_cast hX
        linarith
      have hS2' : (S : ℝ) * (((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 : ℚ) : ℝ) ^ 2
          ≤ 16 * ((T : ℝ) - X) ^ 2 := by exact_mod_cast hS2
      have hL0 : (0 : ℝ) ≤ (((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 : ℚ) : ℝ) := by
        push_cast; positivity
      have hSn : (0 : ℝ) ≤ S := by
        have := CB.mem_normSq (mem_d2psiBr p l (hseg _ (left_mem_segment ℝ (toC a) (toC b))))
        rw [e5] at this
        exact (Complex.normSq_nonneg _).trans this.2
      have key : (√(S : ℝ) * (((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 : ℚ) : ℝ)) ^ 2
          ≤ (4 * ((T : ℝ) - X)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hSn]; nlinarith
      have h4 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 key
      linarith
    rw [segment_eq_image'] at hz
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
    rcases le_total t (1 / 2) with ht | ht
    · have := half_bound (ω := ω) (l := l) (C := √(S : ℝ)) (z := toC a + t • (toC b - toC a)) ht0 ht
        (by rw [Complex.real_smul]) hgood hC hFa hLa
      have hXa : (ha : ℝ) + max 0 (la : ℝ) / 2 ≤ X := by
        have : ha + max 0 la / 2 ≤ X := le_max_left _ _
        exact_mod_cast this
      linarith
    · have h1 : (0 : ℝ) ≤ 1 - t := by linarith
      have h2 : 1 - t ≤ 1 / 2 := by linarith
      have := half_bound (ω := ω) (l := l) (C := √(S : ℝ)) (a := toC b) (b := toC a)
        (z := toC a + t • (toC b - toC a)) h1 h2
        (by rw [Complex.real_smul]; push_cast; ring) hgood' hC' hFb hLb
      have hXb : (hb : ℝ) + max 0 (lb : ℝ) / 2 ≤ X := by
        have : hb + max 0 lb / 2 ≤ X := le_max_right _ _
        exact_mod_cast this
      rw [norm_sub_rev] at this
      linarith
  · simp at h

end ZetaIrr.Interval
