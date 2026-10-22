/-
# Instance-independent helpers for the analytic part of Lemma 6(ii)

Verbatim copies (namespace `ZetaIrr.Fam.Analytic`) of the instance-independent lemmas that live in
the concrete files of `I3/Analytic/` and `I3/Concrete/`:
* Γ run/block products via the reflection formula (`prod_Icc_sub_eq_Gamma`,
  `prod_Icc_add_half_eq_Gamma`);
* block-product reorganisation (`prod_list_blocks`, `sum_list_blocks`);
* `deriv_conj_symm`, `deriv_deriv_eq_zero_of_cube` (triple zeros give `R'' = 0`);
* logarithmic derivative of a finite product, `sin³(πw)/π³` and its derivatives;
* the `q`-form `Qform` of `H_n` and its bounds.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Analytic.Laplace
import ZetaIrrational.Analytic.Contour
import ZetaIrrational.Stirling.All
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

namespace ZetaIrr.Fam.Analytic

open Complex Real Finset Filter Topology Metric
open ZetaIrr.Analytic (norm_cexp_sub_one_le_mul_exp)

/-! ### Γ-products (from `Analytic/GammaFactor.lean`) -/

/-- `sin(x - nπ) = (-1)^n sin x`. -/
lemma csin_sub_nat_mul_pi (x : ℂ) (n : ℕ) : Complex.sin (x - n * π) = (-1) ^ n * Complex.sin x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : x - ((n + 1 : ℕ) : ℂ) * π = (x - n * π) - π := by push_cast; ring
    rw [this, Complex.sin_sub_pi, ih, pow_succ]; ring

/-- `Γ(w + k) = Γ(w) Π_{j<k} (w + j)` for `w ∉ {0, -1, -2, …}`. -/
lemma Gamma_add_nat_eq_mul_prod (w : ℂ) (hw : ∀ k : ℕ, w ≠ -k) (k : ℕ) :
    Complex.Gamma (w + k) = Complex.Gamma w * ∏ j ∈ range k, (w + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : w + k ≠ 0 := fun h => hw k (by linear_combination h)
    rw [prod_range_succ, show w + ((k + 1 : ℕ) : ℂ) = (w + k) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hne, ih]
    ring

/-- The run product via the reflection formula, indexed by `range`. -/
lemma prod_range_eq_Gamma (z : ℂ) (hz : ∀ k : ℤ, z ≠ k) (p q : ℕ) :
    ∏ j ∈ range (p + q + 1), (z - q + j)
      = (-1) ^ q * Complex.Gamma (z + p + 1) * Complex.Gamma (q + 1 - z)
          * Complex.sin (π * z) / π := by
  set w := z - q with hw
  have hwn : ∀ k : ℕ, w ≠ -k := by
    intro k h
    apply hz ((q : ℤ) - k)
    push_cast
    linear_combination h
  have hG := Gamma_add_nat_eq_mul_prod w hwn (p + q + 1)
  have hGw : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
  have e1 : w + ((p + q + 1 : ℕ) : ℂ) = z + p + 1 := by rw [hw]; push_cast; ring
  rw [e1] at hG
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have e2 : 1 - w = (q : ℂ) + 1 - z := by rw [hw]; ring
  rw [e2] at hrefl
  have hsinw : Complex.sin (π * w) = (-1) ^ q * Complex.sin (π * z) := by
    rw [hw, show (π : ℂ) * (z - q) = π * z - q * π by ring, csin_sub_nat_mul_pi]
  have hsin0 : Complex.sin (π * w) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrefl
    exact (mul_ne_zero hGw (Complex.Gamma_ne_zero (by
      intro k hk
      apply hz ((q : ℤ) + 1 + k)
      push_cast
      linear_combination -hk))) hrefl
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- Π = Γ(z+p+1)/Γ(w) and 1/Γ(w) = Γ(1-w) sin(πw)/π
  have hprod : ∏ j ∈ range (p + q + 1), (w + j) = Complex.Gamma (z + p + 1) / Complex.Gamma w := by
    rw [hG]; field_simp
  have hinv : (Complex.Gamma w)⁻¹ = Complex.Gamma ((q : ℂ) + 1 - z) * Complex.sin (π * w) / π := by
    field_simp
    have h' := (eq_div_iff hsin0).1 hrefl
    linear_combination -h'
  calc ∏ j ∈ range (p + q + 1), (z - q + j) = ∏ j ∈ range (p + q + 1), (w + j) := by rw [hw]
    _ = Complex.Gamma (z + p + 1) * (Complex.Gamma w)⁻¹ := by rw [hprod, div_eq_mul_inv]
    _ = _ := by rw [hinv, hsinw]; ring

/-- `Icc (-p) q = image of range (p+q+1) under j ↦ q - j` (as integers). -/
lemma Icc_eq_image_range (p q : ℕ) :
    Icc (-(p : ℤ)) q = (range (p + q + 1)).image (fun j : ℕ => (q : ℤ) - j) := by
  ext l
  simp only [mem_Icc, mem_image, mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨((q : ℤ) - l).toNat, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    omega

/-- **Run product.** For `z ∉ ℤ`: `Π_{l=-p}^{q} (z - l) = (-1)^q Γ(z+p+1) Γ(q+1-z) sin(πz)/π`. -/
lemma prod_Icc_sub_eq_Gamma (z : ℂ) (hz : ∀ k : ℤ, z ≠ k) (p q : ℕ) :
    ∏ l ∈ Icc (-(p : ℤ)) q, (z - l)
      = (-1) ^ q * Complex.Gamma (z + p + 1) * Complex.Gamma (q + 1 - z)
          * Complex.sin (π * z) / π := by
  rw [Icc_eq_image_range, prod_image (fun a _ b _ h => by simpa using h)]
  rw [← prod_range_eq_Gamma z hz p q]
  refine prod_congr rfl (fun j _ => ?_)
  push_cast; ring

/-- **Block product.** `Π_{k=A}^{B} (z + k + 1/2) = Γ(z + B + 3/2) / Γ(z + A + 1/2)` when
`z + A + 1/2 ∉ -ℕ` and `A ≤ B + 1`. -/
lemma prod_Icc_add_half_eq_Gamma (z : ℂ) (A B : ℕ) (hAB : A ≤ B + 1)
    (hz : ∀ k : ℕ, z + A + 1 / 2 ≠ -k) :
    ∏ k ∈ Icc A B, (z + k + 1 / 2)
      = Complex.Gamma (z + B + 3 / 2) / Complex.Gamma (z + A + 1 / 2) := by
  have hG := Gamma_add_nat_eq_mul_prod (z + A + 1 / 2) hz (B + 1 - A)
  have hGw : Complex.Gamma (z + A + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero hz
  have e : z + A + 1 / 2 + ((B + 1 - A : ℕ) : ℂ) = z + B + 3 / 2 := by
    rw [Nat.cast_sub hAB]; push_cast; ring
  rw [e] at hG
  rw [hG, mul_div_cancel_left₀ _ hGw, ← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  refine prod_congr rfl (fun j _ => ?_)
  push_cast; ring

lemma list_prod_map_ofReal {α : Type*} (l : List α) (g : α → ℝ) :
    ((l.map g).prod : ℂ) = (l.map (fun a => (g a : ℂ))).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma list_prod_map_inv {α : Type*} (l : List α) (g : α → ℂ) :
    (l.map (fun a => (g a)⁻¹)).prod = ((l.map g).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

/-! ### Block bookkeeping -/

/-- Reorganising a product of block products (general list version). -/
lemma prod_list_blocks {M : Type*} [CommMonoid M] (x : ℕ → M) (I : ℕ × ℕ → Finset ℕ)
    (U : Finset ℕ) (L : List (ℕ × ℕ)) (hsub : ∀ b ∈ L, I b ⊆ U) :
    (L.map (fun b => (∏ k ∈ I b, x k) ^ b.2)).prod
      = ∏ k ∈ U, x k ^ (L.map (fun b => if k ∈ I b then b.2 else 0)).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, Finset.prod_mul_distrib]
    rw [ih (fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    simp only [pow_ite, pow_zero]
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr (hsub b (List.mem_cons_self ..)),
      Finset.prod_pow]

/-- Additive version: counting with multiplicity. -/
lemma sum_list_blocks (I : ℕ × ℕ → Finset ℕ) (U : Finset ℕ) (L : List (ℕ × ℕ))
    (hsub : ∀ b ∈ L, I b ⊆ U) :
    ∑ k ∈ U, (L.map (fun b => if k ∈ I b then b.2 else 0)).sum
      = (L.map (fun b => b.2 * (I b).card)).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih (fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub b (List.mem_cons_self ..)),
      Finset.sum_const, smul_eq_mul, mul_comm]

lemma list_sum_ite_le (L : List (ℕ × ℕ)) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (L.map (fun b => if P b then b.2 else 0)).sum ≤ (L.map Prod.snd).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (if P b then b.2 else 0) ≤ b.2 := by split_ifs <;> omega
    omega

/-! ### Conjugation symmetry and triple zeros (from `Analytic/ConcreteIntegrand.lean`) -/

/-- The derivative of a conjugation-symmetric holomorphic function is conjugation-symmetric. -/
lemma deriv_conj_symm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hUc : ∀ z ∈ U, (starRingEnd ℂ) z ∈ U) (hg : DifferentiableOn ℂ g U)
    (hsym : ∀ z ∈ U, g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (g z)) :
    ∀ z ∈ U, deriv g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv g z) := by
  intro z hz
  have hzc := hUc z hz
  have hd : HasDerivAt g (deriv g z) z := (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hslope := hd.tendsto_slope
  -- conj maps a punctured neighbourhood of `conj z` to one of `z`
  have hconj : Tendsto (starRingEnd ℂ) (𝓝[≠] ((starRingEnd ℂ) z)) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Complex.continuous_conj.tendsto ((starRingEnd ℂ) z))
      rw [Complex.conj_conj] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
      intro h
      apply hw
      rw [← h, Complex.conj_conj]
  have hlim := (Complex.continuous_conj.tendsto _).comp (hslope.comp hconj)
  have hnew : HasDerivAt g ((starRingEnd ℂ) (deriv g z)) ((starRingEnd ℂ) z) := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine hlim.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hzc)] with w hw
    simp only [Function.comp, slope_def_field]
    rw [map_div₀, map_sub, map_sub, Complex.conj_conj, ← hsym _ (hUc w hw), Complex.conj_conj,
      ← hsym z hz]
  exact hnew.deriv

/-- If `g = (z - t)³ h` near `t` with `h` holomorphic near `t`, then `g''(t) = 0`. -/
lemma deriv_deriv_eq_zero_of_cube {g h : ℂ → ℂ} {t : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (ball t r)) (hg : ∀ z ∈ ball t r, g z = (z - t) ^ 3 * h z) :
    deriv (deriv g) t = 0 := by
  have hU : IsOpen (ball t r) := isOpen_ball
  have hh' : DifferentiableOn ℂ (deriv h) (ball t r) := hh.deriv hU
  set k : ℂ → ℂ := fun z => 3 * h z + (z - t) * deriv h z with hk
  have hdg : ∀ z ∈ ball t r, deriv g z = (z - t) ^ 2 * k z := by
    intro z hz
    have heq : g =ᶠ[𝓝 z] fun w => (w - t) ^ 3 * h w := by
      filter_upwards [hU.mem_nhds hz] with w hw using hg w hw
    rw [heq.deriv_eq]
    have hd1 : HasDerivAt (fun w : ℂ => (w - t) ^ 3) (3 * (z - t) ^ 2) z := by
      simpa using ((hasDerivAt_id z).sub_const t).fun_pow 3
    have hd := hd1.fun_mul (hh.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    rw [hd.deriv, hk]
    ring
  have heq2 : deriv g =ᶠ[𝓝 t] fun z => (z - t) ^ 2 * k z := by
    filter_upwards [hU.mem_nhds (mem_ball_self hr)] with z hz using hdg z hz
  rw [heq2.deriv_eq]
  have hkd : DifferentiableAt ℂ k t := by
    have h1 := hh.differentiableAt (hU.mem_nhds (mem_ball_self hr))
    have h2 := hh'.differentiableAt (hU.mem_nhds (mem_ball_self hr))
    rw [hk]
    fun_prop
  have hd2 : HasDerivAt (fun z : ℂ => (z - t) ^ 2) (2 * (t - t)) t := by
    simpa using ((hasDerivAt_id t).sub_const t).fun_pow 2
  rw [(hd2.fun_mul hkd.hasDerivAt).deriv]
  simp

/-! ### Logarithmic derivatives -/

lemma ne_neg_nat_of_im {w : ℂ} (hw : w.im ≠ 0) : ∀ k : ℕ, w ≠ -k := by
  intro k h; apply hw; rw [h]; simp

lemma mem_slitPlane_of_im {w : ℂ} (hw : w.im ≠ 0) : w ∈ slitPlane :=
  Or.inr hw

/-- `Γ' = Γ ψ` off the poles. -/
lemma hasDerivAt_Gamma_digamma {w : ℂ} (hw : ∀ k : ℕ, w ≠ -k) :
    HasDerivAt Complex.Gamma (Complex.Gamma w * Complex.digamma w) w := by
  have hd := (Complex.differentiableAt_Gamma w hw).hasDerivAt
  have hG := Complex.Gamma_ne_zero hw
  have : deriv Complex.Gamma w = Complex.Gamma w * Complex.digamma w := by
    rw [Complex.digamma_def, logDeriv_apply]; field_simp
  rwa [this] at hd

/-- Logarithmic derivative of a finite product. -/
lemma hasDerivAt_prod_logDeriv {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (κ : ι → ℂ) {z : ℂ} (h : ∀ i ∈ S, HasDerivAt (f i) (f i z * κ i) z) :
    HasDerivAt (fun w => ∏ i ∈ S, f i w) ((∏ i ∈ S, f i z) * ∑ i ∈ S, κ i) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const z (1 : ℂ)
  | insert a S ha ih =>
    have h1 := h a (mem_insert_self a S)
    have h2 := ih (fun i hi => h i (mem_insert_of_mem hi))
    have := h1.mul h2
    simp only [prod_insert ha, sum_insert ha]
    convert this using 1
    ring

/-- `S(w) = sin³(πw)/π³` and its derivatives. -/
lemma hasDerivAt_sin_pi (w : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.sin (π * w)) (π * Complex.cos (π * w)) w := by
  have := ((hasDerivAt_id w).const_mul (π : ℂ)).csin
  simp only [id, mul_one] at this
  convert this using 1; ring

lemma hasDerivAt_cos_pi (w : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.cos (π * w)) (-(π * Complex.sin (π * w))) w := by
  have := ((hasDerivAt_id w).const_mul (π : ℂ)).ccos
  simp only [id, mul_one] at this
  convert this using 1; ring

/-- `S = sin³(πw)/π³`. -/
noncomputable def S0 (w : ℂ) : ℂ := Complex.sin (π * w) ^ 3 / π ^ 3
/-- `S' = 3 sin² cos / π²`. -/
noncomputable def S1 (w : ℂ) : ℂ := 3 * Complex.sin (π * w) ^ 2 * Complex.cos (π * w) / π ^ 2
/-- `S'' = (3/π)(2 sin cos² - sin³)`. -/
noncomputable def S2 (w : ℂ) : ℂ :=
  3 * (2 * Complex.sin (π * w) * Complex.cos (π * w) ^ 2 - Complex.sin (π * w) ^ 3) / π

lemma hπC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

lemma hasDerivAt_S0 (w : ℂ) : HasDerivAt S0 (S1 w) w := by
  have := ((hasDerivAt_sin_pi w).fun_pow 3).div_const ((π : ℂ) ^ 3)
  unfold S0 S1
  convert this using 1
  have := hπC
  field_simp
  ring

lemma hasDerivAt_S1 (w : ℂ) : HasDerivAt S1 (S2 w) w := by
  have := ((((hasDerivAt_sin_pi w).fun_pow 2).const_mul (3 : ℂ)).fun_mul
    (hasDerivAt_cos_pi w)).div_const ((π : ℂ) ^ 2)
  unfold S1 S2
  convert this using 1
  have := hπC
  simp only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
  field_simp
  ring

/-! ### The `q`-form and amplitude helpers (from `Analytic/FnPath.lean`) -/

lemma pi_lt_four : π < 4 := by linarith [Real.pi_lt_d2]

lemma norm_exp_le_three {e : ℂ} (he : ‖e‖ ≤ 1) : ‖Complex.exp e‖ ≤ 3 := by
  calc ‖Complex.exp e‖ ≤ Real.exp ‖e‖ := Complex.norm_exp_le_exp_norm e
    _ ≤ Real.exp 1 := Real.exp_le_exp.2 he
    _ ≤ 3 := by linarith [Real.exp_one_lt_d9]

/-- The `q`-form of `H_n`, as a function of `μ, μ', q`. -/
noncomputable def Qform (μ μ1 q : ℂ) : ℂ :=
  ((-1 + 2 * q - q ^ 2) * (μ ^ 2 + μ1) + 6 * π * I * μ * (1 - q ^ 2)
    + 3 * π ^ 2 * (3 + 2 * q + 3 * q ^ 2)) / 4

lemma norm_Qform_le {μ μ1 q : ℂ} {B : ℝ} (hB : 1 ≤ B) (hμ : ‖μ‖ ≤ 2 * B) (hμ1 : ‖μ1‖ ≤ 1)
    (hq : ‖q‖ ≤ 1) : ‖Qform μ μ1 q‖ ≤ 100 * B ^ 2 := by
  have hπ := pi_lt_four
  have hπ0 := Real.pi_pos
  unfold Qform
  rw [norm_div, show ‖(4 : ℂ)‖ = 4 by simp]
  have hq0 := norm_nonneg q
  have h1 : ‖(-1 + 2 * q - q ^ 2)‖ ≤ 4 := by
    have e1 : ‖(-1 : ℂ) + 2 * q - q ^ 2‖ ≤ 1 + 2 * ‖q‖ + ‖q‖ ^ 2 := by
      calc _ ≤ ‖(-1 : ℂ) + 2 * q‖ + ‖q ^ 2‖ := norm_sub_le _ _
        _ ≤ (‖(-1 : ℂ)‖ + ‖(2 : ℂ) * q‖) + ‖q ^ 2‖ := by gcongr; exact norm_add_le _ _
        _ = 1 + 2 * ‖q‖ + ‖q‖ ^ 2 := by simp [norm_mul, norm_pow]
    nlinarith
  have h2 : ‖μ ^ 2 + μ1‖ ≤ 4 * B ^ 2 + 1 := by
    calc ‖μ ^ 2 + μ1‖ ≤ ‖μ‖ ^ 2 + ‖μ1‖ := by rw [← norm_pow]; exact norm_add_le _ _
      _ ≤ (2 * B) ^ 2 + 1 := by gcongr
      _ = 4 * B ^ 2 + 1 := by ring
  have h3 : ‖6 * (π : ℂ) * I * μ * (1 - q ^ 2)‖ ≤ 6 * π * (2 * B) * 2 := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hπ0, show ‖(6 : ℂ)‖ = 6 by simp]
    have : ‖(1 : ℂ) - q ^ 2‖ ≤ 2 := by
      calc ‖(1 : ℂ) - q ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖q ^ 2‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [norm_one, norm_pow]; gcongr; exact pow_le_one₀ (norm_nonneg _) hq
        _ = 2 := by norm_num
    calc 6 * π * 1 * ‖μ‖ * ‖1 - q ^ 2‖ ≤ 6 * π * 1 * (2 * B) * 2 := by gcongr
      _ = 6 * π * (2 * B) * 2 := by ring
  have h4 : ‖3 * (π : ℂ) ^ 2 * (3 + 2 * q + 3 * q ^ 2)‖ ≤ 3 * π ^ 2 * 8 := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ0,
      show ‖(3 : ℂ)‖ = 3 by simp]
    have : ‖(3 : ℂ) + 2 * q + 3 * q ^ 2‖ ≤ 8 := by
      have e1 : ‖(3 : ℂ) + 2 * q + 3 * q ^ 2‖ ≤ 3 + 2 * ‖q‖ + 3 * ‖q‖ ^ 2 := by
        calc _ ≤ ‖(3 : ℂ)‖ + ‖(2 : ℂ) * q‖ + ‖(3 : ℂ) * q ^ 2‖ := norm_add₃_le
          _ = 3 + 2 * ‖q‖ + 3 * ‖q‖ ^ 2 := by simp [norm_mul, norm_pow]
      nlinarith
    gcongr
  calc ‖(-1 + 2 * q - q ^ 2) * (μ ^ 2 + μ1) + 6 * (π : ℂ) * I * μ * (1 - q ^ 2)
        + 3 * (π : ℂ) ^ 2 * (3 + 2 * q + 3 * q ^ 2)‖ / 4
      ≤ (4 * (4 * B ^ 2 + 1) + 6 * π * (2 * B) * 2 + 3 * π ^ 2 * 8) / 4 := by
        gcongr
        refine (norm_add₃_le).trans (add_le_add_three ?_ h3 h4)
        rw [norm_mul]; exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ ≤ 100 * B ^ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

lemma Qform_sub (μ μ1 q P : ℂ) :
    Qform μ μ1 q - (-(P - 3 * π * I) ^ 2 / 4) =
      -(μ - P) * (μ + P - 6 * π * I) / 4 - μ1 / 4 +
        q * ((2 - q) * (μ ^ 2 + μ1) - 6 * π * I * μ * q + 3 * π ^ 2 * (2 + 3 * q)) / 4 := by
  unfold Qform
  linear_combination ((9 : ℂ) / 4 * π ^ 2) * Complex.I_sq

lemma hπ2 : (0 : ℝ) < π ^ 2 := by positivity

lemma norm_pi_sq : ‖((π : ℂ) ^ 2)‖ = π ^ 2 := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

lemma norm_log_le_of_ge {w : ℂ} {a : ℝ} (ha : 0 < a) (hw : a ≤ ‖w‖) :
    ‖Complex.log w‖ ≤ ‖w‖ + |Real.log a| + π := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le ha hw
  have h1 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 : |Complex.arg w| ≤ π := Complex.abs_arg_le_pi w
  have h3 : |Real.log ‖w‖| ≤ ‖w‖ + |Real.log a| := by
    rcases le_or_gt 1 ‖w‖ with h | h
    · rw [abs_of_nonneg (Real.log_nonneg h)]
      have := Real.log_le_sub_one_of_pos hw0
      linarith [abs_nonneg (Real.log a)]
    · rw [abs_of_neg (Real.log_neg hw0 h)]
      have : Real.log a ≤ Real.log ‖w‖ := Real.log_le_log ha hw
      have := neg_abs_le (Real.log a)
      linarith
  linarith

lemma norm_exp_two_pi_I_mul (n : ℝ) (x : ℂ) :
    ‖Complex.exp (2 * π * I * ((n : ℂ) * x))‖ = Real.exp (-(2 * π * n * x.im)) := by
  rw [Complex.norm_exp]; congr 1; simp; ring

end ZetaIrr.Fam.Analytic
