/-
# Instance-independent helpers for the ζ analytic part (PROOF_ZETA §6.1–6.2)

* Γ-products with integer shifts: `prod_Icc_one_sub_eq_Gamma`
  (`Π_{l=1}^{q} (z - l) = (-1)^q Γ(z) Γ(q+1-z) sin(πz)/π`, `z ∉ ℤ`) and `prod_Icc_add_eq_Gamma`
  (`Π_{k=A}^{B} (z + k) = Γ(z+B+1)/Γ(z+A)`);
* `iterate_deriv_eq_zero_of_pow`: a zero of order `p` kills the derivatives of order `< p`;
* `iterate_deriv_conj_symm`: iterated derivatives of a conjugation-symmetric function;
* Cauchy-estimate decay: `norm_iterate_deriv_le_of_decay` (`‖f‖ ≤ C/‖w‖²` far out gives
  `‖f⁽ʲ⁾‖ ≤ 8ʲ C/‖w‖²` further out) and `exists_bound_of_decay` (the form
  `‖g z‖ ≤ C (1 + ‖z‖²)⁻¹` on a closed half plane).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Fam.Analytic.Helpers
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false

namespace ZetaIrr.Fam.Analytic

open Complex Real Finset Filter Topology Metric

/-! ### Γ-products -/

/-- `Π_{l=1}^{q} (z - l) = (-1)^q Γ(q+1-z) / Γ(1-z)` for `z ∉ ℤ`. -/
lemma prod_Icc_one_sub_eq_div (z : ℂ) (hz : ∀ k : ℤ, z ≠ k) (q : ℕ) :
    ∏ l ∈ Icc 1 q, (z - (l : ℂ)) = (-1) ^ q * Complex.Gamma (q + 1 - z) / Complex.Gamma (1 - z) := by
  have hne : ∀ j : ℕ, (j : ℂ) + 1 - z ≠ 0 := by
    intro j h; apply hz ((j : ℤ) + 1); push_cast; linear_combination -h
  have hG1 : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero (fun k h => by
    apply hz ((k : ℤ) + 1); push_cast; linear_combination -h)
  induction q with
  | zero => simp [hG1]
  | succ q ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have hrec : Complex.Gamma (((q + 1 : ℕ) : ℂ) + 1 - z)
        = ((q : ℂ) + 1 - z) * Complex.Gamma ((q : ℂ) + 1 - z) := by
      rw [show (((q + 1 : ℕ) : ℂ) + 1 - z) = ((q : ℂ) + 1 - z) + 1 by push_cast; ring]
      exact Complex.Gamma_add_one _ (hne q)
    rw [hrec, pow_succ]
    field_simp
    push_cast
    ring

/-- **Run product.** For `z ∉ ℤ`: `Π_{l=1}^{q} (z - l) = (-1)^q Γ(z) Γ(q+1-z) sin(πz)/π`. -/
lemma prod_Icc_one_sub_eq_Gamma (z : ℂ) (hz : ∀ k : ℤ, z ≠ k) (q : ℕ) :
    ∏ l ∈ Icc 1 q, (z - (l : ℂ))
      = (-1) ^ q * Complex.Gamma z * Complex.Gamma (q + 1 - z) * Complex.sin (π * z) / π := by
  rw [prod_Icc_one_sub_eq_div z hz q]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hsin : Complex.sin (π * z) ≠ 0 := by
    intro h0
    rw [Complex.sin_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    apply hz k
    have hπ : (π : ℂ) ≠ 0 := hπC
    have : (π : ℂ) * z = π * k := by rw [hk]; ring
    exact mul_left_cancel₀ hπ this
  have hG1 : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero (fun k h => by
    apply hz ((k : ℤ) + 1); push_cast; linear_combination -h)
  have hπ : (π : ℂ) ≠ 0 := hπC
  rw [eq_div_iff hsin] at hrefl
  rw [div_eq_div_iff hG1 hπ]
  linear_combination (-((-1) ^ q * Complex.Gamma (q + 1 - z))) * hrefl

/-- **Block product.** `Π_{k=A}^{B} (z + k) = Γ(z + B + 1) / Γ(z + A)` when `z + A ∉ -ℕ` and
`A ≤ B + 1`. -/
lemma prod_Icc_add_eq_Gamma (z : ℂ) (A B : ℕ) (hAB : A ≤ B + 1) (hz : ∀ k : ℕ, z + A ≠ -k) :
    ∏ k ∈ Icc A B, (z + k) = Complex.Gamma (z + B + 1) / Complex.Gamma (z + A) := by
  have hG := Gamma_add_nat_eq_mul_prod (z + A) hz (B + 1 - A)
  have hGw : Complex.Gamma (z + A) ≠ 0 := Complex.Gamma_ne_zero hz
  have e : z + A + ((B + 1 - A : ℕ) : ℂ) = z + B + 1 := by
    rw [Nat.cast_sub hAB]; push_cast; ring
  rw [e] at hG
  rw [hG, mul_div_cancel_left₀ _ hGw, ← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  refine prod_congr rfl (fun j _ => ?_)
  push_cast; ring

/-! ### Zeros of order `p` -/

/-- If `g = (z - t)^p h` on a ball with `h` holomorphic there, then for `j ≤ p`,
`g⁽ʲ⁾ = (z - t)^(p-j) h_j` on the ball with `h_j` holomorphic there. -/
lemma iterate_deriv_pow_mul {g h : ℂ → ℂ} {t : ℂ} {r : ℝ} {p : ℕ}
    (hh : DifferentiableOn ℂ h (ball t r)) (hg : ∀ z ∈ ball t r, g z = (z - t) ^ p * h z) :
    ∀ j ≤ p, ∃ hj : ℂ → ℂ, DifferentiableOn ℂ hj (ball t r) ∧
      ∀ z ∈ ball t r, deriv^[j] g z = (z - t) ^ (p - j) * hj z := by
  have hU : IsOpen (ball t r) := isOpen_ball
  intro j
  induction j with
  | zero => intro _; exact ⟨h, hh, fun z hz => by simpa using hg z hz⟩
  | succ j ih =>
    intro hj
    obtain ⟨k, hk, hkg⟩ := ih (by omega)
    refine ⟨fun z => ((p - j : ℕ) : ℂ) * k z + (z - t) * deriv k z, ?_, ?_⟩
    · have hk' : DifferentiableOn ℂ (deriv k) (ball t r) := hk.deriv hU
      intro z hz
      have h1 := (hk.differentiableAt (hU.mem_nhds hz))
      have h2 := (hk'.differentiableAt (hU.mem_nhds hz))
      exact (((differentiableAt_const _).mul h1).add
        ((differentiableAt_id.sub_const t).mul h2)).differentiableWithinAt
    · intro z hz
      rw [Function.iterate_succ_apply']
      have heq : deriv^[j] g =ᶠ[𝓝 z] fun w => (w - t) ^ (p - j) * k w := by
        filter_upwards [hU.mem_nhds hz] with w hw using hkg w hw
      rw [heq.deriv_eq]
      have hd1 : HasDerivAt (fun w : ℂ => (w - t) ^ (p - j))
          (((p - j : ℕ) : ℂ) * (z - t) ^ (p - j - 1)) z := by
        simpa using ((hasDerivAt_id z).sub_const t).fun_pow (p - j)
      have hd := hd1.fun_mul (hk.differentiableAt (hU.mem_nhds hz)).hasDerivAt
      rw [hd.deriv]
      have e : p - j = (p - (j + 1)) + 1 := by omega
      rw [e, pow_succ, Nat.add_sub_cancel]
      push_cast
      ring

/-- A zero of order `p ≥ j + 1` kills the `j`-th derivative. -/
lemma iterate_deriv_eq_zero_of_pow {g h : ℂ → ℂ} {t : ℂ} {r : ℝ} (hr : 0 < r) {p j : ℕ}
    (hjp : j < p) (hh : DifferentiableOn ℂ h (ball t r))
    (hg : ∀ z ∈ ball t r, g z = (z - t) ^ p * h z) : deriv^[j] g t = 0 := by
  obtain ⟨k, _, hk⟩ := iterate_deriv_pow_mul hh hg j hjp.le
  rw [hk t (mem_ball_self hr), sub_self, zero_pow (by omega), zero_mul]

/-! ### Conjugation symmetry -/

lemma iterate_deriv_conj_symm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hUc : ∀ z ∈ U, (starRingEnd ℂ) z ∈ U) (hg : DifferentiableOn ℂ g U)
    (hsym : ∀ z ∈ U, g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (g z)) :
    ∀ j, ∀ z ∈ U, deriv^[j] g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv^[j] g z) := by
  intro j
  induction j with
  | zero => simpa using hsym
  | succ j ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have hd : DifferentiableOn ℂ (deriv^[j] g) U := by
      clear ih
      induction j with
      | zero => simpa using hg
      | succ j ihj => rw [Function.iterate_succ_apply']; exact ihj.deriv hU
    exact deriv_conj_symm hU hUc hd ih z hz

lemma differentiableOn_iterate_deriv {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : ∀ j, DifferentiableOn ℂ (deriv^[j] g) U := by
  intro j
  induction j with
  | zero => simpa using hg
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.deriv hU

/-! ### Decay of derivatives (Cauchy estimates) -/

/-- One Cauchy estimate on circles of radius `1/2`. -/
lemma norm_deriv_le_of_decay {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U) {A C : ℝ}
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hsub : ∀ w : ℂ, A ≤ ‖w‖ → w ∈ U)
    (hb : ∀ w : ℂ, A ≤ ‖w‖ → ‖f w‖ ≤ C / ‖w‖ ^ 2) {z : ℂ} (hz : A + 1 ≤ ‖z‖) :
    ‖deriv f z‖ ≤ 8 * C / ‖z‖ ^ 2 := by
  have hz0 : 0 < ‖z‖ := by linarith
  have hfar : ∀ u : ℂ, ‖u - z‖ ≤ 1 / 2 → ‖z‖ - 1 / 2 ≤ ‖u‖ := by
    intro u hu
    have := norm_sub_norm_le z u
    rw [norm_sub_rev] at hu
    linarith
  have hd : DiffContOnCl ℂ f (ball z (1 / 2)) := by
    refine hf.diffContOnCl_ball (fun u hu => hsub u ?_)
    rw [mem_closedBall, dist_eq_norm] at hu
    linarith [hfar u hu]
  have hbound : ∀ u ∈ sphere z (1 / 2), ‖f u‖ ≤ 4 * C / ‖z‖ ^ 2 := by
    intro u hu
    rw [mem_sphere, dist_eq_norm] at hu
    have h1 := hfar u hu.le
    have h2 : ‖z‖ / 2 ≤ ‖u‖ := by linarith
    refine (hb u (by linarith)).trans ?_
    have hu0 : 0 < ‖u‖ := by linarith
    rw [div_le_div_iff₀ (pow_pos hu0 2) (pow_pos hz0 2)]
    have : (‖z‖ / 2) ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    nlinarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hd hbound
  refine h.trans (le_of_eq ?_)
  ring

/-- Iterated Cauchy estimates: `‖f⁽ʲ⁾ z‖ ≤ 8ʲ C / ‖z‖²` for `‖z‖ ≥ A + j`. -/
lemma norm_iterate_deriv_le_of_decay {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {A C : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hsub : ∀ w : ℂ, A ≤ ‖w‖ → w ∈ U) (hb : ∀ w : ℂ, A ≤ ‖w‖ → ‖f w‖ ≤ C / ‖w‖ ^ 2) :
    ∀ j : ℕ, ∀ z : ℂ, A + j ≤ ‖z‖ → ‖deriv^[j] f z‖ ≤ 8 ^ j * C / ‖z‖ ^ 2 := by
  intro j
  induction j with
  | zero => intro z hz; simpa using hb z (by simpa using hz)
  | succ j ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have hd := differentiableOn_iterate_deriv hU hf j
    have := norm_deriv_le_of_decay (f := deriv^[j] f) (U := U) hd (A := A + j)
      (C := 8 ^ j * C) (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith) (by positivity)
      (fun w hw => hsub w (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)) ih
      (by push_cast at hz; linarith)
    refine this.trans (le_of_eq ?_)
    ring

/-- A function continuous on `{Re z ≥ c}` with `‖g z‖ ≤ C'/‖z‖²` for `‖z‖ ≥ R` satisfies
`‖g z‖ ≤ C (1 + ‖z‖²)⁻¹` there. -/
lemma exists_bound_of_decay {g : ℂ → ℂ} {c R C' : ℝ} (hR : 1 ≤ R) (hC' : 0 ≤ C')
    (hcont : ContinuousOn g {z : ℂ | c ≤ z.re})
    (hb : ∀ z : ℂ, R ≤ ‖z‖ → ‖g z‖ ≤ C' / ‖z‖ ^ 2) :
    ∃ C : ℝ, ∀ z : ℂ, c ≤ z.re → ‖g z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹ := by
  have hK : IsCompact ({z : ℂ | c ≤ z.re} ∩ closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const Complex.continuous_re)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono Set.inter_subset_left)
  refine ⟨max M 0 * (1 + R ^ 2) + 2 * C', fun z hzre => ?_⟩
  have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hinv0 : 0 ≤ (1 + ‖z‖ ^ 2)⁻¹ := inv_nonneg.2 hpos.le
  by_cases hz : ‖z‖ ≤ R
  · have h1 : ‖g z‖ ≤ M := hM z ⟨hzre, by rw [mem_closedBall, dist_zero_right]; exact hz⟩
    have h2 : 1 ≤ (1 + R ^ 2) * (1 + ‖z‖ ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
      have : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      linarith
    calc ‖g z‖ ≤ max M 0 := h1.trans (le_max_left _ _)
      _ ≤ max M 0 * ((1 + R ^ 2) * (1 + ‖z‖ ^ 2)⁻¹) :=
          le_mul_of_one_le_right (le_max_right _ _) h2
      _ ≤ max M 0 * (1 + R ^ 2) * (1 + ‖z‖ ^ 2)⁻¹ + 2 * C' * (1 + ‖z‖ ^ 2)⁻¹ := by
          have : 0 ≤ 2 * C' * (1 + ‖z‖ ^ 2)⁻¹ := by positivity
          linarith [mul_assoc (max M 0) (1 + R ^ 2) (1 + ‖z‖ ^ 2)⁻¹]
      _ = _ := by ring
  · push Not at hz
    have hz1 : 1 ≤ ‖z‖ := by linarith
    have h1 := hb z hz.le
    have h2 : C' / ‖z‖ ^ 2 ≤ 2 * C' * (1 + ‖z‖ ^ 2)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 + ‖z‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by nlinarith
      calc C' = 2 * C' * (1 + ‖z‖ ^ 2)⁻¹ * ((1 + ‖z‖ ^ 2) / 2) := by field_simp
        _ ≤ 2 * C' * (1 + ‖z‖ ^ 2)⁻¹ * ‖z‖ ^ 2 := by gcongr; linarith
    calc ‖g z‖ ≤ 2 * C' * (1 + ‖z‖ ^ 2)⁻¹ := h1.trans h2
      _ ≤ (max M 0 * (1 + R ^ 2) + 2 * C') * (1 + ‖z‖ ^ 2)⁻¹ := by
          have : 0 ≤ max M 0 * (1 + R ^ 2) := by positivity
          nlinarith

end ZetaIrr.Fam.Analytic
