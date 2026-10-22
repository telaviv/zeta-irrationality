/-
# Lemma 6 for Z7: `SaddleData → (size bound) ∧ ∃ᶠ m, L_m ≠ 0`

The chain (PROOF_ZETA §6.6, with the integrand `G_n = R_n k₄` of `ContourZ7.lean`):
1. `L_eq_J`: `L_n = -(1/π) Im J_n`, `J_n = i ∫_0^∞ G_n(c_n + iy) dy`, `c_n = ⌊n x_c⌋ + 1/2`
   (`L_eq_half_line`).
2. `J_split`: deformation onto the polyline `c_n, n v_1, …, n v_Ktop` plus the top ray
   (`contour_eq_polyline_Gfn`).
3. `disc_term`: the disc segment equals `e^{λ_n + log n + nΩ} (n d) D_n`.
4. `D_bound`: `|D_n - A(x₀) √(2π/(nK))| ≤ εD_n/√n`, `εD → 0` (`laplace_bound`,
   `taylor_phase_bound`, `Gfn_disc_approx`).
5. `E_bound`: the rest is `≤ εf_n e^{λ_n + log n + n Re Ω} √n`, `εf → 0` (`norm_Gfn_le`,
   (S2), (S3)).
6. `nonvan_of_saddleData`: `frequently_ne_zero_of_saddle'` with `sin(240 Im Ω) ≠ 0` (H4).
7. `size_of_saddleData`: `|L_n| ≤ |J_n|/π ≤ e^{λ_n + log n + n Re Ω} √n · C`, Stirling's upper bound
   `log n! ≤ n log n - n + (log n)/2 + 1`, and `Re Ω ≤ Vcert` (`ReΩ_le`) give Lemma 6(i):
   `log |L_n| ≤ -G log n! + n (Vcert + εL_n)`, `εL → 0`.

The progression is `n = 240(m+1)` (`q = 240`), the zero run ends at `rn = 220(m+1)` (so
`x_c < r = 11/12`). Mirrors lean_beta's `I3/Analytic/NonvanI3.lean`; the amplitude is
`A(x) = (2x+1) e^{ψ₀(x)}` and there is no boundary term.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Analytic.Pointwise
import ZetaIrrational.Z7.Analytic.Deform
import ZetaIrrational.Analytic.SaddleAssembly

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real Finset Filter Topology Set MeasureTheory
open ZetaIrr.Analytic ZetaIrr.Fam.Analytic


namespace SaddleData

variable (S : SaddleData)

/-- `n = 240(m+1)` as a real number. -/
noncomputable def nn (m : ℕ) : ℝ := (Z7.nOf m : ℝ)

lemma nn_pos (m : ℕ) : 0 < nn m := by unfold nn Z7.nOf; positivity

lemma nn_eq (m : ℕ) : nn m = 240 * ((m : ℝ) + 1) := by unfold nn Z7.nOf; push_cast; ring

lemma tendsto_nn : Tendsto nn atTop atTop := by
  have : nn = fun m : ℕ => 240 * ((m : ℝ) + 1) := funext nn_eq
  rw [this]
  exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num)

/-- `Ω = f(x₀)`. -/
noncomputable def Ω : ℂ := phaseZ S.x₀

/-- The start `c_n = ⌊n x_c⌋ + 1/2`. -/
noncomputable def cm (m : ℕ) : ℝ := ⌊nn m * (S.v 0).re⌋ + 1 / 2

/-- Polyline vertices in `z`: `w 0 = c_n`, `w k = n v_k`. -/
noncomputable def w (m : ℕ) (k : ℕ) : ℂ := if k = 0 then (S.cm m : ℂ) else (nn m : ℂ) * S.v k

/-- `J_n = i ∫_0^∞ F_n(c_n + iy) dy`. -/
noncomputable def J (m : ℕ) : ℂ := I * ∫ y in Ioi (0 : ℝ), Gfn m (S.cm m + y * I)

lemma v0_re_pos : 0 < (S.v 0).re := lt_of_lt_of_le S.δ₀_pos S.δ₀_le

lemma cm_bounds (m : ℕ) :
    nn m * (S.v 0).re - 1 / 2 < S.cm m ∧ S.cm m ≤ nn m * (S.v 0).re + 1 / 2 := by
  unfold cm
  constructor
  · have := Int.lt_floor_add_one (nn m * (S.v 0).re); linarith
  · have := Int.floor_le (nn m * (S.v 0).re); linarith

lemma cm_ne_int (m : ℕ) (k : ℤ) : S.cm m ≠ k := by
  unfold cm
  intro h
  have h2 : ((2 * ⌊nn m * (S.v 0).re⌋ + 1 : ℤ) : ℝ) = ((2 * k : ℤ) : ℝ) := by
    push_cast; linarith
  have h3 := Int.cast_injective h2
  omega

lemma cm_pos (m : ℕ) : 0 < S.cm m := by
  unfold cm
  have hprod : 0 ≤ nn m * (S.v 0).re := mul_nonneg (nn_pos m).le S.v0_re_pos.le
  have : (0 : ℝ) ≤ ⌊nn m * (S.v 0).re⌋ := by exact_mod_cast Int.floor_nonneg.2 hprod
  linarith

/-- Step 1. -/
theorem L_eq_J (m : ℕ) : Z7.L m = -(1 / π) * (S.J m).im := by
  have hb := S.cm_bounds m
  have hup : nn m * (S.v 0).re < 220 * ((m : ℝ) + 1) := by
    rw [nn_eq]; nlinarith [S.v0_lt]
  rw [L_eq_half_line m (c := S.cm m) (S.cm_pos m) (by linarith) (S.cm_ne_int m)]
  unfold J
  rw [Complex.mul_im, Complex.I_re, Complex.I_im]
  simp

lemma v1_im_pos : 0 < (S.v 1).im := by
  have hK : 0 < S.Ktop := by have := S.Kd_lt; have := S.Kd_pos; omega
  have := S.path_im 0 hK 1 ⟨one_pos, le_rfl⟩
  simpa using this

lemma vtop_im_pos : 0 < (S.v S.Ktop).im := by
  have hK : 0 < S.Ktop := by have := S.Kd_lt; have := S.Kd_pos; omega
  obtain ⟨j, hj⟩ : ∃ j, S.Ktop = j + 1 := ⟨S.Ktop - 1, by omega⟩
  have := S.path_im j (by omega) 1 ⟨one_pos, le_rfl⟩
  rw [hj]
  simpa using this

/-- Step 2. -/
theorem J_split (m : ℕ) :
    S.J m = (∑ k ∈ range S.Ktop, segInt (Gfn m) (S.w m k) (S.w m (k + 1)))
      + I * ∫ y in Ioi (0 : ℝ), Gfn m (S.w m S.Ktop + y * I) := by
  have hK : 0 < S.Ktop := by have := S.Kd_lt; have := S.Kd_pos; omega
  unfold J
  refine contour_eq_polyline_Gfn m (S.cm_pos m) (S.cm_ne_int m) (S.w m) S.Ktop
    (by simp [w]) ?_ ?_ ?_
  · intro k hk t ht
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have e0 : S.w m 0 = (S.cm m : ℂ) := by simp [w]
      have e1 : S.w m (0 + 1) = (nn m : ℂ) * S.v 1 := by simp [w]
      rw [e0, e1]
      have h1 := S.v1_im_pos
      have : ((S.cm m : ℂ) + t * ((nn m : ℂ) * S.v 1 - S.cm m)).im = t * (nn m * (S.v 1).im) := by
        simp
      rw [this]
      exact mul_pos ht.1 (mul_pos (nn_pos m) h1)
    · have e0 : S.w m k = (nn m : ℂ) * S.v k := by simp [w, hk0.ne']
      have e1 : S.w m (k + 1) = (nn m : ℂ) * S.v (k + 1) := by simp [w]
      rw [e0, e1]
      have := S.path_im k hk t ht
      have e : (nn m : ℂ) * S.v k + t * ((nn m : ℂ) * S.v (k + 1) - (nn m : ℂ) * S.v k)
          = (nn m : ℂ) * (S.v k + t * (S.v (k + 1) - S.v k)) := by ring
      rw [e, Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos (nn_pos m) this
  · have e0 : S.w m S.Ktop = (nn m : ℂ) * S.v S.Ktop := by simp [w, hK.ne']
    rw [e0, Complex.mul_im]; simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (nn_pos m) S.vtop_im_pos
  · have e0 : S.w m S.Ktop = (nn m : ℂ) * S.v S.Ktop := by simp [w, hK.ne']
    rw [e0, Complex.mul_re]; simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (nn_pos m) S.top_re_pos

/-- `λ'_n = λ_n + log n`. -/
noncomputable def lam' (m : ℕ) : ℝ := lamN (nn m) + Real.log (nn m)

/-- `D_n = ∫_{-ρ}^{ρ} F_n(n(x₀ + sd)) e^{-λ_n - nΩ}/n ds`. -/
noncomputable def D (m : ℕ) : ℂ :=
  ∫ s in (-S.ρ)..S.ρ, Gfn m ((nn m : ℂ) * (S.x₀ + s * S.d)) *
    (Complex.exp (-(lamN (nn m) + (nn m : ℂ) * S.Ω)) / (nn m : ℂ))

/-- Step 3. -/
theorem disc_term (m : ℕ) :
    segInt (Gfn m) (S.w m S.Kd) (S.w m (S.Kd + 1)) =
      Complex.exp ((lam' m : ℂ) + (nn m : ℂ) * S.Ω) * ((nn m : ℂ) * S.d) * S.D m := by
  have hKd : S.Kd ≠ 0 := by have := S.Kd_pos; omega
  have hn0 : (nn m : ℂ) ≠ 0 := by exact_mod_cast (nn_pos m).ne'
  have hρ0 : (S.ρ : ℝ) ≠ 0 := S.ρ_pos.ne'
  have e0 : S.w m S.Kd = (nn m : ℂ) * S.v S.Kd := by simp [w, hKd]
  have e1 : S.w m (S.Kd + 1) = (nn m : ℂ) * S.v (S.Kd + 1) := by simp [w]
  rw [e0, e1, S.v_disc_lo, S.v_disc_hi]
  unfold segInt
  set g : ℝ → ℂ := fun s => Gfn m ((nn m : ℂ) * (S.x₀ + s * S.d)) with hg
  have hpt : ∀ t : ℝ, (nn m : ℂ) * (S.x₀ - S.ρ * S.d) + t * ((nn m : ℂ) * (S.x₀ + S.ρ * S.d)
      - (nn m : ℂ) * (S.x₀ - S.ρ * S.d)) = (nn m : ℂ) * (S.x₀ + ((2 * S.ρ * t - S.ρ : ℝ) : ℂ) * S.d) := by
    intro t; push_cast; ring
  simp_rw [hpt]
  have hdiff : (nn m : ℂ) * (S.x₀ + S.ρ * S.d) - (nn m : ℂ) * (S.x₀ - S.ρ * S.d)
      = 2 * S.ρ * ((nn m : ℂ) * S.d) := by ring
  rw [hdiff, intervalIntegral.integral_mul_const]
  have hsub : ∫ t in (0 : ℝ)..1, Gfn m ((nn m : ℂ) * (S.x₀ + ((2 * S.ρ * t - S.ρ : ℝ) : ℂ) * S.d))
      = (2 * S.ρ)⁻¹ • ∫ s in (-S.ρ)..S.ρ, g s := by
    have := intervalIntegral.integral_comp_mul_sub (f := g) (a := 0) (b := 1)
      (show (2 * S.ρ : ℝ) ≠ 0 by have := S.ρ_pos; positivity) S.ρ
    simp only [mul_zero, zero_sub, mul_one] at this
    rw [show 2 * S.ρ - S.ρ = S.ρ by ring] at this
    exact this
  rw [hsub]
  unfold D lam'
  rw [intervalIntegral.integral_mul_const]
  have hexp : Complex.exp (((lamN (nn m) + Real.log (nn m) : ℝ) : ℂ) + (nn m : ℂ) * S.Ω)
      = (nn m : ℂ) * Complex.exp (lamN (nn m) + (nn m : ℂ) * S.Ω) := by
    rw [show (((lamN (nn m) + Real.log (nn m) : ℝ) : ℂ) + (nn m : ℂ) * S.Ω)
        = (Real.log (nn m) : ℂ) + ((lamN (nn m) : ℂ) + (nn m : ℂ) * S.Ω) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (nn_pos m)]
  rw [hexp, Complex.exp_neg, Complex.real_smul]
  generalize (∫ s in (-S.ρ)..S.ρ, g s) = Ig
  have he : Complex.exp ((lamN (nn m) : ℂ) + (nn m : ℂ) * S.Ω) ≠ 0 := Complex.exp_ne_zero _
  have hρC : ((2 * S.ρ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show (2 * S.ρ : ℝ) ≠ 0 by positivity)
  have hρ' : (S.ρ : ℂ) ≠ 0 := by exact_mod_cast S.ρ_pos.ne'
  push_cast at hρC ⊢
  field_simp

/-! ### Step 4: the disc part -/

/-- The disc point `x(s) = x₀ + s d`. -/
noncomputable def xs (s : ℝ) : ℂ := S.x₀ + s * S.d

lemma xs_mem_ball {s : ℝ} (hs : s ∈ Icc (-S.ρ) S.ρ) : S.xs s ∈ Metric.closedBall S.x₀ S.ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  unfold xs
  rw [add_sub_cancel_left, norm_mul, S.d_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.2 hs

lemma im_of_mem_ball {z : ℂ} (hz : z ∈ Metric.closedBall S.x₀ S.ρ) : S.x₀.im - S.ρ ≤ z.im := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_im_le_norm (z - S.x₀)
  have : (z - S.x₀).im = z.im - S.x₀.im := by simp
  rw [this] at h
  have := (abs_le.1 (h.trans hz)).1
  linarith

lemma ball_im_pos {z : ℂ} (hz : z ∈ Metric.closedBall S.x₀ S.ρ) : 0 < z.im := by
  have := S.im_of_mem_ball hz; have := S.S1'_disc; linarith

lemma ball_subset_upper : Metric.closedBall S.x₀ S.ρ ⊆ {z : ℂ | 0 < z.im} :=
  fun z hz => S.ball_im_pos hz

lemma xs_re_nonneg {s : ℝ} (hs : s ∈ Icc (-S.ρ) S.ρ) : 0 ≤ (S.xs s).re := by
  have h0 := S.re_nonneg S.Kd (by have := S.Kd_lt; omega)
  have h1 := S.re_nonneg (S.Kd + 1) (by have := S.Kd_lt; omega)
  rw [S.v_disc_lo] at h0
  rw [S.v_disc_hi] at h1
  have hρ := S.ρ_pos
  have e : S.xs s = ((S.ρ - s) / (2 * S.ρ) : ℝ) * (S.x₀ - S.ρ * S.d)
      + ((S.ρ + s) / (2 * S.ρ) : ℝ) * (S.x₀ + S.ρ * S.d) := by
    unfold xs
    have : (S.ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have ha : 0 ≤ (S.ρ - s) / (2 * S.ρ) := div_nonneg (by linarith [hs.2]) (by positivity)
  have hb : 0 ≤ (S.ρ + s) / (2 * S.ρ) := div_nonneg (by linarith [hs.1]) (by positivity)
  exact add_nonneg (mul_nonneg ha h0) (mul_nonneg hb h1)

lemma xs_norm_le {s : ℝ} (hs : s ∈ Icc (-S.ρ) S.ρ) : ‖S.xs s‖ ≤ ‖S.x₀‖ + S.ρ := by
  have := S.xs_mem_ball hs
  rw [Metric.mem_closedBall, dist_eq_norm] at this
  have h2 := norm_sub_norm_le (S.xs s) S.x₀
  linarith

lemma x₀_re_nonneg : 0 ≤ S.x₀.re := by
  have := S.xs_re_nonneg (s := 0) ⟨by linarith [S.ρ_pos], S.ρ_pos.le⟩
  simpa [xs] using this

/-- The phase deviation `φ(s) = f(x(s)) - Ω`. -/
noncomputable def φ (s : ℝ) : ℂ := phaseZ (S.xs s) - S.Ω

lemma taylor (s : ℝ) (hs : s ∈ Icc (-S.ρ) S.ρ) :
    ‖S.φ s + S.K * s ^ 2 / 2‖ ≤ S.M * |s| ^ 3 / 6 := by
  have hpt : ∀ s ∈ Icc (-S.ρ) S.ρ, (S.x₀ + s * S.d).im ≠ 0 := fun s hs =>
    ne_of_gt (S.ball_im_pos (S.xs_mem_ball hs))
  have := taylor_phase_bound (F := phaseZ) (F1 := fun x => Psi1Z x - 3 * π * I) (F2 := Psi2Z)
    (F3 := Psi3Z) (x₀ := S.x₀) (d := S.d) (K := S.K) (M := S.M) (ρ := S.ρ) S.d_norm
    (by rw [S.S0]; ring) S.S1_dir
    (fun s hs => hasDerivAt_phaseZ (hpt s hs))
    (fun s hs => (hasDerivAt_Psi1Z (hpt s hs)).sub_const _)
    (fun s hs => hasDerivAt_Psi2Z (hpt s hs))
    (fun s hs => S.S1_M _ (S.xs_mem_ball hs)) s hs
  unfold φ Ω xs
  exact this

lemma M_nonneg : 0 ≤ S.M :=
  (norm_nonneg _).trans (S.S1_M S.x₀ (Metric.mem_closedBall_self S.ρ_pos.le))

lemma re_φ_nonpos {s : ℝ} (hs : s ∈ Icc (-S.ρ) S.ρ) : (S.φ s).re ≤ 0 := by
  have h := S.taylor s hs
  have hre : (S.φ s).re + S.K * s ^ 2 / 2 ≤ S.M * |s| ^ 3 / 6 := by
    have := Complex.re_le_norm (S.φ s + S.K * s ^ 2 / 2)
    have e : (S.φ s + S.K * s ^ 2 / 2).re = (S.φ s).re + S.K * s ^ 2 / 2 := by
      rw [show (S.K : ℂ) * (s : ℂ) ^ 2 / 2 = ((S.K * s ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.add_re, Complex.ofReal_re]
    rw [e] at this; linarith
  have habs : |s| ≤ S.ρ := abs_le.2 hs
  have hM := S.M_nonneg
  have h1 : S.M * |s| ≤ 3 * S.K / 2 := (mul_le_mul_of_nonneg_left habs hM).trans S.S1_ρ
  have h2 : S.M * |s| ^ 3 = (S.M * |s|) * s ^ 2 := by rw [← sq_abs s]; ring
  have h3 : S.M * |s| ^ 3 ≤ 3 * S.K / 2 * s ^ 2 := by
    rw [h2]; exact mul_le_mul_of_nonneg_right h1 (sq_nonneg s)
  nlinarith [S.K_pos, sq_nonneg s]

lemma norm_exp_nφ_le {n : ℝ} (hn : 0 ≤ n) {s : ℝ} (hs : s ∈ Icc (-S.ρ) S.ρ) :
    ‖Complex.exp ((n : ℂ) * S.φ s)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.2
  have : ((n : ℂ) * S.φ s).re = n * (S.φ s).re := by simp
  rw [this]
  exact mul_nonpos_of_nonneg_of_nonpos hn (S.re_φ_nonpos hs)

/-- The disc amplitude bound `A₀` and Lipschitz constant `A₁` (compactness). -/
lemma exists_amp_consts : ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
    (∀ s ∈ Icc (-S.ρ) S.ρ, ‖Alim (S.xs s)‖ ≤ A₀) ∧
    (∀ s ∈ Icc (-S.ρ) S.ρ, ‖Alim (S.xs s) - Alim (S.xs 0)‖ ≤ A₁ * |s|) := by
  have hK : IsCompact (Metric.closedBall S.x₀ S.ρ) := isCompact_closedBall _ _
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hcont : ContinuousOn Alim (Metric.closedBall S.x₀ S.ρ) :=
    (differentiableOn_Alim.mono S.ball_subset_upper).continuousOn
  have hdcont : ContinuousOn (deriv Alim) (Metric.closedBall S.x₀ S.ρ) :=
    ((differentiableOn_Alim.deriv hH).mono S.ball_subset_upper).continuousOn
  obtain ⟨A₀, hA₀⟩ := hK.exists_bound_of_continuousOn hcont
  obtain ⟨A₁, hA₁⟩ := hK.exists_bound_of_continuousOn hdcont
  have hx₀ : S.x₀ ∈ Metric.closedBall S.x₀ S.ρ := Metric.mem_closedBall_self S.ρ_pos.le
  refine ⟨A₀, A₁, (norm_nonneg _).trans (hA₀ _ hx₀), (norm_nonneg _).trans (hA₁ _ hx₀),
    fun s hs => hA₀ _ (S.xs_mem_ball hs), fun s hs => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => differentiableAt_Alim (ne_of_gt (S.ball_im_pos hz))) hA₁
    (convex_closedBall S.x₀ S.ρ) (S.xs_mem_ball (s := 0) ⟨by linarith [S.ρ_pos], S.ρ_pos.le⟩)
    (S.xs_mem_ball hs)
  refine h.trans (le_of_eq ?_)
  unfold xs
  rw [show S.x₀ + (s : ℂ) * S.d - (S.x₀ + ((0 : ℝ) : ℂ) * S.d) = s * S.d by push_cast; ring,
    norm_mul, S.d_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-! ### Limits used for the error terms -/

lemma tendsto_sqrt_mul_div (C : ℝ) :
    Tendsto (fun x : ℝ => √x * (C / x)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => C * (√x)⁻¹) atTop (𝓝 (C * 0)) :=
    (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul C
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have hsq : √x * √x = x := Real.mul_self_sqrt hx.le
  calc C * (√x)⁻¹ = √x * C / (√x * √x) := by field_simp
    _ = √x * (C / x) := by rw [hsq]; ring

lemma tendsto_sqrt_mul_exp {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => √x * Real.exp (-(c * x))) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) c hc
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow, neg_mul]

lemma eventually_largeN : ∀ᶠ m in atTop, LargeN S.a S.η (nn m) := by
  have h := tendsto_nn
  unfold LargeN
  filter_upwards [h.eventually (eventually_ge_atTop (4 / S.a)),
    h.eventually (eventually_ge_atTop 1), h.eventually (eventually_ge_atTop (cE S.a S.η))]
    with m h1 h2 h3
  exact ⟨h1, h2, h3⟩

lemma tendsto_deltaN {y₁ : ℝ} (hy : 0 < y₁) :
    Tendsto (fun m => deltaN S.a S.η (nn m) y₁) atTop (𝓝 0) := by
  unfold deltaN
  have h1 : Tendsto (fun m => (cE S.a S.η + 1) / nn m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_nn
  have h2 : Tendsto (fun m => Real.exp (-(2 * π * nn m * y₁))) atTop (𝓝 0) := by
    have : Tendsto (fun m => 2 * π * y₁ * nn m) atTop atTop :=
      tendsto_nn.const_mul_atTop (by have := Real.pi_pos; positivity)
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp this
    refine h.congr (fun m => ?_)
    simp only [Function.comp]; congr 1; ring
  simpa using h1.add h2

/-- **Step 4.** -/
theorem D_bound : ∃ εD : ℕ → ℝ, Tendsto εD atTop (𝓝 0) ∧ ∀ᶠ m in atTop,
    ‖S.D m - Alim S.x₀ * ((√(2 * π / (nn m * S.K)) : ℝ) : ℂ)‖ ≤ εD m / √(nn m) := by
  obtain ⟨A₀, A₁, hA₀, hA₁, ha0, ha1⟩ := S.exists_amp_consts
  set B := Bgrowth S.a (‖S.x₀‖ + S.ρ) with hB
  set y₁ := S.x₀.im - S.ρ with hy₁
  have hy₁pos : 0 < y₁ := by have := S.S1'_disc; rw [hy₁]; linarith
  set C1 := 16 * √(2 * π) / 3 * A₀ * S.M / S.K ^ 2 + 2 * √(2 * π) * A₁ / S.K with hC1
  set C2 := 2 * S.ρ * (100 * B ^ 2) with hC2
  set Cs := cE S.a S.η + 1 with hCs
  set c₁ := S.K * S.ρ ^ 2 / 4 with hc₁
  have hc₁pos : 0 < c₁ := by have := S.K_pos; have := S.ρ_pos; positivity
  set c₂ := 2 * π * y₁ with hc₂
  have hc₂pos : 0 < c₂ := by have := Real.pi_pos; positivity
  let εD : ℕ → ℝ := fun m => √(nn m) * (C1 / nn m + A₀ * √(4 * π / S.K) * Real.exp (-(c₁ * nn m))
    + C2 * (Cs / nn m + Real.exp (-(c₂ * nn m))))
  refine ⟨εD, ?_, ?_⟩
  · -- the limit
    have e : εD = fun m => √(nn m) * (C1 / nn m) + A₀ * √(4 * π / S.K) *
        (√(nn m) * Real.exp (-(c₁ * nn m))) + C2 * (√(nn m) * (Cs / nn m)
        + √(nn m) * Real.exp (-(c₂ * nn m))) := by
      funext m; simp only [εD]; ring
    rw [e]
    have t1 := (tendsto_sqrt_mul_div C1).comp tendsto_nn
    have t2 := ((tendsto_sqrt_mul_exp hc₁pos).comp tendsto_nn).const_mul (A₀ * √(4 * π / S.K))
    have t3 := (((tendsto_sqrt_mul_div Cs).comp tendsto_nn).add
      ((tendsto_sqrt_mul_exp hc₂pos).comp tendsto_nn)).const_mul C2
    simpa using (t1.add t2).add t3
  · -- the bound
    have hδ := (S.tendsto_deltaN hy₁pos).eventually (eventually_le_nhds zero_lt_one)
    filter_upwards [S.eventually_largeN, hδ] with m hL hδm
    set n := nn m with hn_def
    have hn1 : 1 ≤ n := hL.2.1
    have hnpos : 0 < n := by linarith
    have hsn : 0 < √n := Real.sqrt_pos.2 hnpos
    -- the two integrands
    set gt : ℝ → ℂ := fun s => Gfn m ((n : ℂ) * (S.x₀ + s * S.d)) *
      (Complex.exp (-(lamN n + (n : ℂ) * S.Ω)) / (n : ℂ)) with hgt
    set h : ℝ → ℂ := fun s => Complex.exp ((n : ℂ) * S.φ s) * Alim (S.xs s) with hh
    have hD : S.D m = ∫ s in (-S.ρ)..S.ρ, gt s := rfl
    have hpt : ∀ s ∈ Icc (-S.ρ) S.ρ, 0 < (S.xs s).im := fun s hs =>
      S.ball_im_pos (S.xs_mem_ball hs)
    have hρle : -S.ρ ≤ S.ρ := by linarith [S.ρ_pos]
    -- continuity / integrability
    have hcx : Continuous S.xs := by unfold xs; fun_prop
    have hgt_int : IntervalIntegrable gt volume (-S.ρ) S.ρ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hρle]
      intro s hs
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul ?_ continuousAt_const
      have him : 0 < ((n : ℂ) * (S.x₀ + s * S.d)).im := by
        have := hpt s hs
        unfold xs at this
        rw [Complex.mul_im]; simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        exact mul_pos hnpos this
      exact ContinuousAt.comp (g := Gfn m) (f := fun s : ℝ => (n : ℂ) * (S.x₀ + s * S.d))
        (Gfn_differentiableAt_of_im m him).continuousAt (by fun_prop)
    have hφc : ContinuousOn S.φ (Icc (-S.ρ) S.ρ) := by
      intro s hs
      refine ContinuousAt.continuousWithinAt ?_
      unfold φ
      exact (ContinuousAt.comp (g := phaseZ) (f := S.xs)
        (hasDerivAt_phaseZ (ne_of_gt (hpt s hs))).continuousAt hcx.continuousAt).sub
        continuousAt_const
    have hac : ContinuousOn (fun s => Alim (S.xs s)) (Icc (-S.ρ) S.ρ) := by
      intro s hs
      exact (ContinuousAt.comp (g := Alim) (f := S.xs)
        (differentiableAt_Alim (ne_of_gt (hpt s hs))).continuousAt
        hcx.continuousAt).continuousWithinAt
    have hh_int : IntervalIntegrable h volume (-S.ρ) S.ρ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hρle]
      exact ((continuousOn_const.mul hφc).cexp).mul hac
    -- Laplace
    have hlap := laplace_bound (n := n) (K := S.K) (M := S.M) (ρ := S.ρ) (A₀ := A₀) (A₁ := A₁)
      hnpos S.K_pos S.M_nonneg S.ρ_pos S.S1_ρ hφc hac (fun s hs => S.taylor s hs) ha0
      (fun s hs => by simpa using ha1 s hs)
    have hx0 : S.xs 0 = S.x₀ := by simp [xs]
    rw [hx0] at hlap
    -- the approximation
    have happrox : ∀ s ∈ Set.uIoc (-S.ρ) S.ρ, ‖gt s - h s‖ ≤ 100 * B ^ 2 * deltaN S.a S.η n y₁ := by
      intro s hs
      rw [uIoc_of_le hρle] at hs
      have hsI : s ∈ Icc (-S.ρ) S.ρ := Ioc_subset_Icc_self hs
      have hap := Gfn_disc_approx m S.a_pos S.η_pos S.η_le (x := S.xs s) (hpt s hsI)
        (S.S4_disc s hsI) (R := ‖S.x₀‖ + S.ρ) (y₁ := y₁)
        (S.xs_norm_le hsI) (S.im_of_mem_ball (S.xs_mem_ball hsI)) S.Ω hL hδm
      have hexp := S.norm_exp_nφ_le hnpos.le hsI
      simp only [hgt, hh]
      unfold xs at hap ⊢
      unfold φ at hexp ⊢
      unfold xs at hexp
      rw [← mul_div_assoc]
      refine hap.trans ?_
      have : 0 ≤ 100 * B ^ 2 * deltaN S.a S.η n y₁ := by
        have : 0 ≤ deltaN S.a S.η n y₁ := by
          unfold deltaN
          have := cE_pos S.a_pos S.η_pos S.η_le
          positivity
        positivity
      exact (mul_le_mul_of_nonneg_right hexp this).trans_eq (one_mul _)
    have hdiff : ‖(∫ s in (-S.ρ)..S.ρ, gt s) - ∫ s in (-S.ρ)..S.ρ, h s‖
        ≤ C2 * deltaN S.a S.η n y₁ := by
      rw [← intervalIntegral.integral_sub hgt_int hh_int]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const happrox).trans (le_of_eq ?_)
      rw [hC2, show S.ρ - -S.ρ = 2 * S.ρ by ring, abs_of_pos (by linarith [S.ρ_pos])]
      ring
    -- combine
    have hsqrt : √(4 * π / (n * S.K)) ≤ √(4 * π / S.K) := by
      apply Real.sqrt_le_sqrt
      have := S.K_pos; have := Real.pi_pos
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have hexp1 : Real.exp (-(n * S.K * S.ρ ^ 2 / 4)) = Real.exp (-(c₁ * n)) := by
      rw [hc₁]; congr 1; ring
    have hdelta : deltaN S.a S.η n y₁ = Cs / n + Real.exp (-(c₂ * n)) := by
      unfold deltaN; rw [hCs, hc₂]; congr 2; ring
    have hεD : εD m / √n = C1 / n + A₀ * √(4 * π / S.K) * Real.exp (-(c₁ * n))
        + C2 * (Cs / n + Real.exp (-(c₂ * n))) := by
      simp only [εD]; rw [← hn_def]; field_simp
    rw [hεD, hD]
    calc ‖(∫ s in (-S.ρ)..S.ρ, gt s) - Alim S.x₀ * ((√(2 * π / (n * S.K)) : ℝ) : ℂ)‖
        ≤ ‖(∫ s in (-S.ρ)..S.ρ, gt s) - ∫ s in (-S.ρ)..S.ρ, h s‖
          + ‖(∫ s in (-S.ρ)..S.ρ, h s) - Alim S.x₀ * ((√(2 * π / (n * S.K)) : ℝ) : ℂ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C2 * deltaN S.a S.η n y₁ + (C1 / n + A₀ * Real.exp (-(n * S.K * S.ρ ^ 2 / 4))
          * √(4 * π / (n * S.K))) := add_le_add hdiff hlap
      _ ≤ _ := by
          rw [hexp1, hdelta]
          have : A₀ * Real.exp (-(c₁ * n)) * √(4 * π / (n * S.K))
              ≤ A₀ * √(4 * π / S.K) * Real.exp (-(c₁ * n)) := by
            rw [mul_right_comm]; gcongr
          linarith

/-! ### Step 5: the far part -/

/-- A segment of the far part: pointwise (U) along the segment. -/
lemma seg_bound (m : ℕ) (hL : LargeN S.a S.η (nn m)) (A B : ℂ) (R : ℝ)
    (hpt : ∀ t ∈ Ioc (0 : ℝ) 1, ∃ x : ℂ, A + t * (B - A) = (nn m : ℂ) * x ∧ 0 < x.im ∧
      SectorAt S.a S.η x ∧ ‖x‖ ≤ R ∧ (phaseZ x).re ≤ S.Ω.re - S.ηfar) :
    ‖segInt (Gfn m) A B‖ ≤ Real.exp (lamN (nn m) + nn m * (S.Ω.re - S.ηfar)) * nn m *
      (72 * Bgrowth S.a R ^ 2) * ‖B - A‖ := by
  unfold segInt
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t : ℝ => Gfn m (A + t * (B - A)) * (B - A))
    (C := Real.exp (lamN (nn m) + nn m * (S.Ω.re - S.ηfar)) * nn m *
      (72 * Bgrowth S.a R ^ 2) * ‖B - A‖) (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      obtain ⟨x, hx, hxim, hxs, hxR, hxph⟩ := hpt t ht
      rw [norm_mul, hx]
      have hF : ‖Gfn m ((nn m : ℂ) * x)‖ ≤ Real.exp (lamN (nn m) + nn m * (phaseZ x).re) * nn m *
          (72 * Bgrowth S.a R ^ 2) := norm_Gfn_le m S.a_pos S.η_pos S.η_le hxim hxs
        hxR hL
      refine mul_le_mul_of_nonneg_right (hF.trans ?_) (norm_nonneg _)
      have hn := (nn_pos m).le
      have : Real.exp (lamN (nn m) + nn m * (phaseZ x).re)
          ≤ Real.exp (lamN (nn m) + nn m * (S.Ω.re - S.ηfar)) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hxph hn
        linarith
      gcongr)
  simpa using h

lemma Bgrowth_shift (a : ℝ) {r u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) :
    Bgrowth a (r + u) ≤ Bgrowth a r * Real.exp (28 * u) := by
  unfold Bgrowth ellA
  have he : 1 + 28 * u ≤ Real.exp (28 * u) := by have := Real.add_one_le_exp (28 * u); linarith
  have hexp : Real.exp (28 * (r + u + 2 + |Real.log a| + π))
      = Real.exp (28 * (r + 2 + |Real.log a| + π)) * Real.exp (28 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  have hpos : 0 < Real.exp (28 * (r + 2 + |Real.log a| + π)) := Real.exp_pos _
  nlinarith

/-- The far part `E_n`. -/
noncomputable def E (m : ℕ) : ℂ :=
  (∑ k ∈ (range S.Ktop).erase S.Kd, segInt (Gfn m) (S.w m k) (S.w m (k + 1)))
    + I * ∫ y in Ioi (0 : ℝ), Gfn m (S.w m S.Ktop + y * I)

/-- A radius dominating every vertex. -/
noncomputable def Rall : ℝ := (∑ k ∈ range (S.Ktop + 1), ‖S.v k‖) + S.δ₀

lemma norm_v_le {k : ℕ} (hk : k ≤ S.Ktop) : ‖S.v k‖ ≤ ∑ j ∈ range (S.Ktop + 1), ‖S.v j‖ :=
  single_le_sum (f := fun j => ‖S.v j‖) (fun j _ => norm_nonneg _)
    (mem_range.2 (Nat.lt_succ_of_le hk))

lemma sum_two_le {j k : ℕ} (hj : j ≤ S.Ktop) (hk : k ≤ S.Ktop) (hjk : j ≠ k) :
    ‖S.v j‖ + ‖S.v k‖ ≤ ∑ i ∈ range (S.Ktop + 1), ‖S.v i‖ := by
  have := sum_le_sum_of_subset_of_nonneg (f := fun i => ‖S.v i‖)
    (show ({j, k} : Finset ℕ) ⊆ range (S.Ktop + 1) by
      intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> omega)
    (fun i _ _ => norm_nonneg _)
  rw [sum_pair hjk] at this
  exact this

lemma Rall_nonneg : 0 ≤ S.Rall := by
  unfold Rall; have := S.δ₀_pos.le; positivity

/-- Points of a polyline segment have norm at most the sum of the endpoint norms. -/
lemma norm_seg_le (p q : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖p + t * (q - p)‖ ≤ ‖p‖ + ‖q‖ := by
  have e : p + t * (q - p) = ((1 - t : ℝ) : ℂ) * p + (t : ℂ) * q := by push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
  nlinarith [norm_nonneg p, norm_nonneg q, ht.1, ht.2]

/-- **Step 5.** -/
theorem E_bound : ∃ εf : ℕ → ℝ, Tendsto εf atTop (𝓝 0) ∧ ∀ᶠ m in atTop,
    ‖S.E m‖ ≤ εf m * Real.exp (lam' m + nn m * S.Ω.re) * √(nn m) := by
  set R := S.Rall with hR
  set Cst := 72 * Bgrowth S.a R ^ 2 with hCst
  set Bg := Bgrowth S.a ‖S.v S.Ktop‖ with hBg
  set Ctop := 72 * Bg ^ 2 * Real.exp (57 * S.Y₀) with hCtop
  set Cfar := (S.Ktop : ℝ) * (Cst * (2 * R + 1)) + Ctop with hCfar
  refine ⟨fun m => Cfar * (√(nn m) * Real.exp (-(S.ηfar * nn m))), ?_, ?_⟩
  · have := ((tendsto_sqrt_mul_exp S.ηfar_pos).comp tendsto_nn).const_mul Cfar
    simpa using this
  have hK : 0 < S.Ktop := by have := S.Kd_lt; have := S.Kd_pos; omega
  have hδ : ∀ᶠ m in atTop, 1 / (2 * S.δ₀) ≤ nn m :=
    tendsto_nn.eventually (eventually_ge_atTop _)
  have hrate : ∀ᶠ m in atTop, 57 / S.rate ≤ nn m :=
    tendsto_nn.eventually (eventually_ge_atTop _)
  filter_upwards [S.eventually_largeN, hδ, hrate] with m hL hδm hrm
  set n := nn m with hn_def
  have hnpos : 0 < n := nn_pos m
  have hn1 : 1 ≤ n := hL.2.1
  set Λ := Real.exp (lamN n + n * (S.Ω.re - S.ηfar)) with hΛ
  have hΛpos : 0 < Λ := Real.exp_pos _
  have hRnn := S.Rall_nonneg
  have hCst0 : 0 ≤ Cst := by positivity
  have hsum0 : ∑ i ∈ range (S.Ktop + 1), ‖S.v i‖ ≤ R := by
    rw [hR]; unfold Rall; linarith [S.δ₀_pos]
  -- each far segment
  have hseg : ∀ k ∈ (range S.Ktop).erase S.Kd,
      ‖segInt (Gfn m) (S.w m k) (S.w m (k + 1))‖ ≤ Λ * n * Cst * (n * (2 * R + 1)) := by
    intro k hk
    obtain ⟨hkd, hk⟩ := mem_erase.1 hk
    have hk' := mem_range.1 hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · -- the first segment
      have e0 : S.w m 0 = (S.cm m : ℂ) := by unfold w; rw [if_pos rfl]
      have e1 : S.w m (0 + 1) = (n : ℂ) * S.v 1 := by unfold w; rw [if_neg (by norm_num)]
      rw [e0, e1]
      set e : ℝ := S.cm m / n - (S.v 0).re with he
      have hcm := S.cm_bounds m
      have he_bd : |e| ≤ S.δ₀ := by
        have h1 : |S.cm m - n * (S.v 0).re| ≤ 1 / 2 :=
          abs_le.2 ⟨by linarith [hcm.1], by linarith [hcm.2]⟩
        have he' : e = (S.cm m - n * (S.v 0).re) / n := by rw [he]; field_simp
        rw [he', abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
        have : 1 / 2 ≤ S.δ₀ * n := by
          rw [div_le_iff₀ (by linarith [S.δ₀_pos])] at hδm
          linarith
        linarith
      have hseg1 := seg_bound S m hL (S.cm m : ℂ) ((n : ℂ) * S.v 1) R (fun t ht => by
        refine ⟨(S.v 0 + e) + t * (S.v 1 - (S.v 0 + e)), ?_, ?_, ?_, ?_, ?_⟩
        · have hcmC : (S.cm m : ℂ) = (n : ℂ) * (S.v 0 + e) := by
            apply Complex.ext
            · simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.add_re,
                zero_mul, sub_zero]
              rw [he]; field_simp; ring
            · simp [S.v0_im]
          rw [hcmC]; ring
        · have : ((S.v 0 + e) + t * (S.v 1 - (S.v 0 + e))).im = t * (S.v 1).im := by
            simp [S.v0_im]
          rw [this]; exact mul_pos ht.1 S.v1_im_pos
        · exact (S.S2_first e (abs_le.1 he_bd) t ht).2
        · refine (norm_seg_le _ _ ⟨ht.1.le, ht.2⟩).trans ?_
          have h01 := S.sum_two_le (j := 0) (k := 1) (by omega) (by omega) (by omega)
          have : ‖S.v 0 + (e : ℂ)‖ ≤ ‖S.v 0‖ + S.δ₀ := by
            refine (norm_add_le _ _).trans ?_
            rw [Complex.norm_real, Real.norm_eq_abs]; linarith
          rw [hR]; unfold Rall; linarith
        · exact (S.S2_first e (abs_le.1 he_bd) t ht).1)
      refine hseg1.trans ?_
      gcongr
      calc ‖(n : ℂ) * S.v 1 - S.cm m‖ ≤ ‖(n : ℂ) * S.v 1‖ + ‖(S.cm m : ℂ)‖ := norm_sub_le _ _
        _ ≤ n * ‖S.v 1‖ + (n * ‖S.v 0‖ + 1) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.cm_pos m)]
            have : (S.v 0).re ≤ ‖S.v 0‖ := Complex.re_le_norm _
            nlinarith [hcm.2]
        _ ≤ n * (2 * R + 1) := by
            have h01 := S.sum_two_le (j := 0) (k := 1) (by omega) (by omega) (by omega)
            nlinarith [norm_nonneg (S.v 0), norm_nonneg (S.v 1)]
    · -- the other far segments
      have hk1 : k ≠ 0 := Nat.pos_iff_ne_zero.1 hk0
      have e0 : S.w m k = (n : ℂ) * S.v k := by unfold w; rw [if_neg hk1]
      have e1 : S.w m (k + 1) = (n : ℂ) * S.v (k + 1) := by
        unfold w; rw [if_neg (Nat.succ_ne_zero k)]
      rw [e0, e1]
      have hsegk := seg_bound S m hL ((n : ℂ) * S.v k) ((n : ℂ) * S.v (k + 1)) R (fun t ht => by
        refine ⟨S.v k + t * (S.v (k + 1) - S.v k), by ring, S.path_im k hk' t ht,
          (S.S2 k hk' hk0 hkd t ⟨ht.1.le, ht.2⟩).2, ?_,
          (S.S2 k hk' hk0 hkd t ⟨ht.1.le, ht.2⟩).1⟩
        refine (norm_seg_le _ _ ⟨ht.1.le, ht.2⟩).trans ?_
        have := S.sum_two_le (j := k) (k := k + 1) (by omega) (by omega) (by omega)
        linarith)
      refine hsegk.trans ?_
      gcongr
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
      gcongr
      have := S.sum_two_le (j := k) (k := k + 1) (by omega) (by omega) (by omega)
      calc ‖S.v (k + 1) - S.v k‖ ≤ ‖S.v (k + 1)‖ + ‖S.v k‖ := norm_sub_le _ _
        _ ≤ 2 * R + 1 := by linarith
  -- the top ray
  have hwK : S.w m S.Ktop = (n : ℂ) * S.v S.Ktop := by unfold w; rw [if_neg hK.ne']
  have htop : ‖I * ∫ y in Ioi (0 : ℝ), Gfn m (S.w m S.Ktop + y * I)‖ ≤ Λ * n * Ctop * n := by
    rw [norm_mul, Complex.norm_I, one_mul, hwK]
    have hbound : ∀ y ∈ Ioi (0 : ℝ), ‖Gfn m ((n : ℂ) * S.v S.Ktop + y * I)‖
        ≤ Λ * n * Ctop * Real.exp ((-1 / n) * y) := by
      intro y hy
      have hy0 : 0 < y := hy
      set u : ℝ := y / n with hu
      have hu0 : 0 ≤ u := by positivity
      set x : ℂ := S.v S.Ktop + u * I with hx
      have hz : (n : ℂ) * S.v S.Ktop + y * I = (n : ℂ) * x := by
        have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
        rw [hx, hu]; push_cast; field_simp
      have hxim : 0 < x.im := by rw [hx]; simp; linarith [S.vtop_im_pos]
      have hxn : ‖x‖ ≤ ‖S.v S.Ktop‖ + u := by
        rw [hx]; refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0, Complex.norm_I,
          mul_one]
      obtain ⟨hph, hsec⟩ := S.S3 u hu0
      have hF := norm_Gfn_le m S.a_pos S.η_pos S.η_le hxim hsec hxn hL
      rw [hz]
      refine hF.trans ?_
      have hBs := Bgrowth_shift S.a (norm_nonneg (S.v S.Ktop)) hu0
      have hB2 : Bgrowth S.a (‖S.v S.Ktop‖ + u) ^ 2 ≤ Bg ^ 2 * Real.exp (56 * u) := by
        have h1 := one_le_Bgrowth S.a (r := ‖S.v S.Ktop‖ + u) (by positivity)
        calc Bgrowth S.a (‖S.v S.Ktop‖ + u) ^ 2 ≤ (Bg * Real.exp (28 * u)) ^ 2 :=
              pow_le_pow_left₀ (by linarith) hBs 2
          _ = Bg ^ 2 * Real.exp (56 * u) := by
              rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
      -- exponent algebra
      have hexpo : n * (phaseZ x).re + 56 * u
          ≤ n * (S.Ω.re - S.ηfar) + 57 * S.Y₀ + (-1 / n) * y := by
        have h1 : n * (phaseZ x).re ≤ n * (S.Ω.re - S.ηfar - S.rate * max 0 (u - S.Y₀)) :=
          mul_le_mul_of_nonneg_left hph hnpos.le
        have hnr : 57 ≤ n * S.rate := by
          rw [div_le_iff₀ S.rate_pos] at hrm; linarith
        have h2 : 57 * (u - S.Y₀) ≤ n * S.rate * max 0 (u - S.Y₀) := by
          rcases le_or_gt (u - S.Y₀) 0 with h | h
          · have : 0 ≤ n * S.rate * max 0 (u - S.Y₀) := by
              have := S.rate_pos; positivity
            linarith
          · rw [max_eq_right h.le]; nlinarith
        have hyu : (-1 / n) * y = -u := by rw [hu]; field_simp
        rw [hyu]
        nlinarith
      calc Real.exp (lamN n + n * (phaseZ x).re) * n *
            (72 * Bgrowth S.a (‖S.v S.Ktop‖ + u) ^ 2)
          ≤ Real.exp (lamN n + n * (phaseZ x).re) * n * (72 * (Bg ^ 2 * Real.exp (56 * u))) := by
            gcongr
        _ = 72 * Bg ^ 2 * n * Real.exp ((lamN n + n * (phaseZ x).re) + 56 * u) := by
            rw [Real.exp_add (lamN n + n * (phaseZ x).re)]; ring
        _ ≤ 72 * Bg ^ 2 * n * Real.exp ((lamN n + n * (S.Ω.re - S.ηfar))
              + 57 * S.Y₀ + (-1 / n) * y) := by
            apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hexpo]))
            positivity
        _ = Λ * n * Ctop * Real.exp ((-1 / n) * y) := by
            rw [Real.exp_add, Real.exp_add, hΛ, hCtop]; ring
    have hneg : (-1 / n) < 0 := by
      rw [neg_div]; exact neg_neg_of_pos (by positivity)
    have hint := (integrableOn_exp_mul_Ioi hneg 0).const_mul (Λ * n * Ctop)
    refine (norm_integral_le_of_norm_le hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbound))).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_exp_mul_Ioi hneg 0]
    field_simp
    simp
  -- assemble
  have hsum : ‖∑ k ∈ (range S.Ktop).erase S.Kd, segInt (Gfn m) (S.w m k) (S.w m (k + 1))‖
      ≤ S.Ktop * (Λ * n * Cst * (n * (2 * R + 1))) := by
    refine (norm_sum_le _ _).trans ((sum_le_sum hseg).trans ?_)
    rw [sum_const, nsmul_eq_mul]
    have hcard : (((range S.Ktop).erase S.Kd).card : ℝ) ≤ S.Ktop := by
      have := card_erase_le (s := range S.Ktop) (a := S.Kd)
      rw [card_range] at this; exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  unfold E
  refine (norm_add_le _ _).trans ((add_le_add hsum htop).trans (le_of_eq ?_))
  -- algebra: `Λ n² Cfar = εf e^{λ' + n Re Ω} √n`
  have hsq : √n * √n = n := Real.mul_self_sqrt hnpos.le
  have hexp : Real.exp (lam' m + n * S.Ω.re) = n * Real.exp (lamN n + n * S.Ω.re) := by
    unfold lam'
    rw [← hn_def, show lamN n + Real.log n + n * S.Ω.re = Real.log n + (lamN n + n * S.Ω.re)
      by ring, Real.exp_add, Real.exp_log hnpos]
  have hΛ' : Λ = Real.exp (lamN n + n * S.Ω.re) * Real.exp (-(S.ηfar * n)) := by
    rw [hΛ, ← Real.exp_add]; congr 1; ring
  rw [hexp, hΛ', hCfar]
  calc (S.Ktop : ℝ) * (Real.exp (lamN n + n * S.Ω.re) * Real.exp (-(S.ηfar * n)) * n * Cst *
        (n * (2 * R + 1))) + Real.exp (lamN n + n * S.Ω.re) * Real.exp (-(S.ηfar * n)) * n * Ctop * n
      = ((S.Ktop : ℝ) * (Cst * (2 * R + 1)) + Ctop) * Real.exp (-(S.ηfar * n)) * Real.exp
          (lamN n + n * S.Ω.re) * (n * n) := by ring
    _ = _ := by
        beta_reduce
        linear_combination (-(((S.Ktop : ℝ) * (Cst * (2 * R + 1)) + Ctop) *
          Real.exp (-(S.ηfar * n)) * Real.exp (lamN n + n * S.Ω.re) * n)) * hsq

/-! ### Step 6: assembly -/

lemma Alim_x₀_ne_zero : Alim S.x₀ ≠ 0 := by
  unfold Alim
  have h1 : 2 * S.x₀ + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [S.x₀_re_nonneg]
  exact mul_ne_zero h1 (Complex.exp_ne_zero _)

theorem J_decomp (m : ℕ) :
    S.J m = Complex.exp ((lam' m : ℂ) + (nn m : ℂ) * S.Ω) * ((nn m : ℂ) * S.d) * S.D m
      + S.E m := by
  have hKd : S.Kd ∈ range S.Ktop := mem_range.2 (by have := S.Kd_lt; omega)
  rw [S.J_split m, ← add_sum_erase _ _ hKd, S.disc_term m]
  unfold E
  ring

end SaddleData

/-- **Lemma 6(ii) for Z7.** The certified saddle data imply that `L_n ≠ 0` for infinitely many
`n ∈ 240ℕ`. -/
theorem nonvan_of_saddleData (S : SaddleData) : ∃ᶠ m in atTop, Z7.L m ≠ 0 := by
  obtain ⟨εD, hεD, hD⟩ := S.D_bound
  obtain ⟨εf, hεf, hE⟩ := S.E_bound
  have hfreq := frequently_ne_zero_of_saddle' (fun m => -(1 / π) * (S.J m).im)
    SaddleData.nn SaddleData.lam' εf S.J S.D S.E S.Ω S.d (Alim S.x₀) S.K 240 (-(1 / π)) εD
    S.K_pos (by intro h; have := S.d_norm; rw [h, norm_zero] at this; norm_num at this)
    S.Alim_x₀_ne_zero (neg_ne_zero.2 (one_div_pos.2 Real.pi_pos).ne') S.H4
    (fun m => by rw [SaddleData.nn_eq, SaddleData.nn_eq]; push_cast; ring)
    SaddleData.tendsto_nn (fun m => rfl) (Eventually.of_forall S.J_decomp) hD hεD hE hεf
  exact hfreq.mono (fun m hm => by rw [S.L_eq_J m]; exact hm)

/-- Stirling's upper bound `log n! ≤ n log n - n + (log n)/2 + 1` for `n ≥ 1`. -/
lemma log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le k)
    simpa [Function.comp] using this
  have hpos := Stirling.stirlingSeq'_pos k
  have hlog := Real.log_le_log hpos h1
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at hlog
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Real.log_mul (by norm_num) hk.ne', Real.log_div hk.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at hlog
  nlinarith

/-- **Lemma 6(i) for Z7.** The certified saddle data give
`log |L_n| ≤ -G log n! + n (Vcert + εL_n)` with `εL → 0`. -/
theorem size_of_saddleData (S : SaddleData) : ∃ εL : ℕ → ℝ, Tendsto εL atTop (𝓝 0) ∧
    ∀ᶠ m in atTop, Z7.L m ≠ 0 → Real.log |Z7.L m| ≤
      -(Z7.G : ℝ) * Real.log ((Z7.nOf m).factorial : ℝ) + (Z7.nOf m : ℝ) * ((Vcert : ℝ) + εL m) := by
  obtain ⟨εD, hεD, hD⟩ := S.D_bound
  obtain ⟨εf, hεf, hE⟩ := S.E_bound
  set A0 : ℝ := ‖Alim S.x₀‖ * √(2 * π / S.K) + 2 with hA0
  have hA0pos : 0 < A0 := by rw [hA0]; positivity
  set C1 : ℝ := (547 / 120 + 1) + 5 * Real.log (2 * π) + |Real.log A0| with hC1
  set εL : ℕ → ℝ := fun m => C1 / SaddleData.nn m +
    (547 / 120 + 1) * (Real.log (SaddleData.nn m) / SaddleData.nn m) with hεL
  refine ⟨εL, ?_, ?_⟩
  · have h1 : Tendsto (fun m => C1 / SaddleData.nn m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop SaddleData.tendsto_nn
    have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using this
    have h3 := (h2.comp SaddleData.tendsto_nn).const_mul (547 / 120 + 1)
    simpa [hεL] using h1.add h3
  have hsmall : ∀ᶠ m in atTop, εD m ≤ 1 ∧ εf m ≤ 1 :=
    (hεD.eventually (eventually_le_nhds one_pos)).and (hεf.eventually (eventually_le_nhds one_pos))
  filter_upwards [hD, hE, hsmall] with m hDm hEm hsm hL
  set n := SaddleData.nn m with hn_def
  have hnpos : 0 < n := SaddleData.nn_pos m
  have hn1 : 1 ≤ n := by rw [hn_def, SaddleData.nn_eq]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hsn : 0 < √n := Real.sqrt_pos.2 hnpos
  have hsq : √n * √n = n := Real.mul_self_sqrt hnpos.le
  -- `‖J‖ ≤ e^{λ' + n Re Ω} √n A0`
  have hJ : ‖S.J m‖ ≤ Real.exp (SaddleData.lam' m + n * S.Ω.re) * √n * A0 := by
    rw [S.J_decomp m]
    have hexp : ‖Complex.exp ((SaddleData.lam' m : ℂ) + (n : ℂ) * S.Ω)‖
        = Real.exp (SaddleData.lam' m + n * S.Ω.re) := by
      rw [Complex.norm_exp]; congr 1; simp
    have hnd : ‖(n : ℂ) * S.d‖ = n := by
      rw [norm_mul, S.d_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
    have hDn : ‖S.D m‖ ≤ ‖Alim S.x₀‖ * (√(2 * π / S.K) / √n) + εD m / √n := by
      have h := norm_sub_norm_le (S.D m) (Alim S.x₀ * ((√(2 * π / (n * S.K)) : ℝ) : ℂ))
      have e1 : ‖Alim S.x₀ * ((√(2 * π / (n * S.K)) : ℝ) : ℂ)‖
          = ‖Alim S.x₀‖ * (√(2 * π / S.K) / √n) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        congr 1
        rw [show 2 * π / (n * S.K) = (2 * π / S.K) / n by field_simp, Real.sqrt_div' _ hnpos.le]
      rw [e1] at h
      linarith
    have hnD : n * ‖S.D m‖ ≤ √n * (‖Alim S.x₀‖ * √(2 * π / S.K) + εD m) := by
      calc n * ‖S.D m‖ ≤ n * (‖Alim S.x₀‖ * (√(2 * π / S.K) / √n) + εD m / √n) :=
            mul_le_mul_of_nonneg_left hDn hnpos.le
        _ = (n / √n) * (‖Alim S.x₀‖ * √(2 * π / S.K) + εD m) := by
            field_simp
        _ = √n * (‖Alim S.x₀‖ * √(2 * π / S.K) + εD m) := by
            have hn' : n / √n = √n := by rw [div_eq_iff hsn.ne']; exact hsq.symm
            rw [hn']
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hexp, hnd]
    have hεD0 : 0 ≤ εD m := by
      have := (norm_nonneg _).trans hDm
      exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hsn))
    have hX := Real.exp_pos (SaddleData.lam' m + n * S.Ω.re)
    calc Real.exp (SaddleData.lam' m + n * S.Ω.re) * n * ‖S.D m‖ + ‖S.E m‖
        ≤ Real.exp (SaddleData.lam' m + n * S.Ω.re) * (√n * (‖Alim S.x₀‖ * √(2 * π / S.K) + εD m))
          + εf m * Real.exp (SaddleData.lam' m + n * S.Ω.re) * √n := by
          rw [mul_assoc]; gcongr
      _ = Real.exp (SaddleData.lam' m + n * S.Ω.re) * √n *
            (‖Alim S.x₀‖ * √(2 * π / S.K) + εD m + εf m) := by ring
      _ ≤ Real.exp (SaddleData.lam' m + n * S.Ω.re) * √n * A0 := by
          rw [hA0]
          exact mul_le_mul_of_nonneg_left (by linarith [hsm.1, hsm.2]) (by positivity)
  -- `|L| ≤ ‖J‖`
  have hLJ : |Z7.L m| ≤ ‖S.J m‖ := by
    rw [S.L_eq_J m, abs_mul, abs_neg, abs_of_pos (one_div_pos.2 Real.pi_pos)]
    have h1 : |(S.J m).im| ≤ ‖S.J m‖ := Complex.abs_im_le_norm _
    have h2 : 1 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
    nlinarith [abs_nonneg (S.J m).im]
  have hLpos : 0 < |Z7.L m| := abs_pos.2 hL
  have hlog := Real.log_le_log hLpos (hLJ.trans hJ)
  rw [Real.log_mul (by positivity) hA0pos.ne', Real.log_mul (by positivity) hsn.ne',
    Real.log_exp, Real.log_sqrt hnpos.le] at hlog
  -- assemble
  have hfact := log_factorial_le (Z7.nOf m) (by unfold Z7.nOf; omega)
  have hnn : ((Z7.nOf m : ℕ) : ℝ) = n := rfl
  rw [hnn] at hfact
  have hG : (Z7.G : ℝ) = 547 / 120 := by norm_num [Z7.G]
  have hV : (Vcert : ℝ) = -101167 / 10000 := by norm_num [Vcert]
  have hΩ : S.Ω.re ≤ -101167 / 10000 := S.ReΩ_le
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlam : SaddleData.lam' m = -(547 / 120) * n * Real.log n + (547 / 120) * n
      - 18 * Real.log n + 5 * Real.log (2 * π) + Real.log n := by
    unfold SaddleData.lam' lamN; rw [← hn_def]
  rw [hlam] at hlog
  rw [hG, hV, hnn]
  have hεLm : n * εL m = C1 + (547 / 120 + 1) * Real.log n := by
    simp only [hεL]; rw [← hn_def]; field_simp
  have habs := le_abs_self (Real.log A0)
  have hfin : n * (-101167 / 10000 + εL m)
      = n * (-101167 / 10000) + (C1 + (547 / 120 + 1) * Real.log n) := by
    rw [mul_add, hεLm]
  rw [hfin, hC1]
  nlinarith [mul_le_mul_of_nonneg_left hΩ hnpos.le]

end ZetaIrr.Z7.Analytic
