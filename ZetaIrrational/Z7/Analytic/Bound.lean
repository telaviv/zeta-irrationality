/-
# Decay of the concrete Z7 rational function and its derivatives

* `norm_RC_le`: `‖RC m w‖ ≤ C₁ / ‖w‖²` for `‖w‖ ≥ R₁ = 2(460(m+1) + 1)`, by comparing every
  linear factor with `‖w‖` (numerator degree `1 + 2200(m+1)`, denominator degree
  `Σ B_k = 3294(m+1) + 18`, so `deg R ≤ -2`);
* `RCd_bound`: for every `j` and every `c > -1` there is `C` with
  `‖R_n⁽ʲ⁾(z)‖ ≤ C (1 + ‖z‖²)⁻¹` on `Re z ≥ c` (Cauchy estimates `norm_iterate_deriv_le_of_decay`
  and compactness `exists_bound_of_decay`).
-/
import ZetaIrrational.Z7.Analytic.Integrand

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Finset Filter Topology Metric
open ZetaIrr.Fam.Analytic

/-- The radius beyond which the crude factor comparison applies. -/
def R₁ (m : ℕ) : ℝ := 2 * (460 * ((m : ℝ) + 1) + 1)

lemma one_le_R₁ (m : ℕ) : 1 ≤ R₁ m := by
  unfold R₁; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith

lemma nOf_real (m : ℕ) : (Z7.nOf m : ℝ) = 240 * ((m : ℝ) + 1) := by
  unfold Z7.nOf; push_cast; ring

lemma norm_NC_le (m : ℕ) {w : ℂ} (hw : R₁ m ≤ ‖w‖) :
    ‖NC m w‖ ≤ 3 * ‖w‖ * (2 * ‖w‖) ^ (2200 * (m + 1)) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn := nOf_real m
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  unfold NC
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  have h1 : ‖2 * w + (Z7.nOf m : ℂ)‖ ≤ 3 * ‖w‖ := by
    calc ‖2 * w + (Z7.nOf m : ℂ)‖ ≤ ‖2 * w‖ + ‖(Z7.nOf m : ℂ)‖ := norm_add_le _ _
      _ = 2 * ‖w‖ + Z7.nOf m := by rw [norm_mul, Complex.norm_natCast]; norm_num
      _ ≤ 3 * ‖w‖ := by rw [hn]; unfold R₁ at hw; linarith
  have h2 : ∏ l ∈ Icc 1 (220 * (m + 1)), ‖(w - (l : ℂ)) ^ 5‖
      ≤ (2 * ‖w‖) ^ (5 * (220 * (m + 1))) := by
    calc ∏ l ∈ Icc 1 (220 * (m + 1)), ‖(w - (l : ℂ)) ^ 5‖
        ≤ ∏ _l ∈ Icc 1 (220 * (m + 1)), (2 * ‖w‖) ^ 5 := by
          refine prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun l hl => ?_)
          rw [norm_pow]
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 5
          have hl' : (l : ℝ) ≤ 220 * ((m : ℝ) + 1) := by
            have := (mem_Icc.1 hl).2
            have : (l : ℝ) ≤ ((220 * (m + 1) : ℕ) : ℝ) := by exact_mod_cast this
            push_cast at this; linarith
          calc ‖w - (l : ℂ)‖ ≤ ‖w‖ + ‖(l : ℂ)‖ := norm_sub_le _ _
            _ = ‖w‖ + l := by rw [Complex.norm_natCast]
            _ ≤ 2 * ‖w‖ := by unfold R₁ at hw; linarith
      _ = (2 * ‖w‖) ^ (5 * (220 * (m + 1))) := by
          rw [prod_const, ← pow_mul, Nat.card_Icc, Nat.add_sub_cancel]
  have h3 : ∏ l ∈ Icc (Z7.nOf m + 1) (460 * (m + 1)), ‖(w + (l : ℂ)) ^ 5‖
      ≤ (2 * ‖w‖) ^ (5 * (220 * (m + 1))) := by
    calc ∏ l ∈ Icc (Z7.nOf m + 1) (460 * (m + 1)), ‖(w + (l : ℂ)) ^ 5‖
        ≤ ∏ _l ∈ Icc (Z7.nOf m + 1) (460 * (m + 1)), (2 * ‖w‖) ^ 5 := by
          refine prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun l hl => ?_)
          rw [norm_pow]
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 5
          have hl' : (l : ℝ) ≤ 460 * ((m : ℝ) + 1) := by
            have := (mem_Icc.1 hl).2
            have : (l : ℝ) ≤ ((460 * (m + 1) : ℕ) : ℝ) := by exact_mod_cast this
            push_cast at this; linarith
          calc ‖w + (l : ℂ)‖ ≤ ‖w‖ + ‖(l : ℂ)‖ := norm_add_le _ _
            _ = ‖w‖ + l := by rw [Complex.norm_natCast]
            _ ≤ 2 * ‖w‖ := by unfold R₁ at hw; linarith
      _ = (2 * ‖w‖) ^ (5 * (220 * (m + 1))) := by
          have hc : (Icc (Z7.nOf m + 1) (460 * (m + 1))).card = 220 * (m + 1) := by
            rw [Nat.card_Icc]; unfold Z7.nOf; omega
          rw [prod_const, ← pow_mul, hc]
  have hp : (0 : ℝ) ≤ (2 * ‖w‖) ^ (5 * (220 * (m + 1))) := pow_nonneg (by positivity) _
  calc ‖2 * w + (Z7.nOf m : ℂ)‖ * (∏ l ∈ Icc 1 (220 * (m + 1)), ‖(w - (l : ℂ)) ^ 5‖) *
        (∏ l ∈ Icc (Z7.nOf m + 1) (460 * (m + 1)), ‖(w + (l : ℂ)) ^ 5‖)
      ≤ 3 * ‖w‖ * (2 * ‖w‖) ^ (5 * (220 * (m + 1))) * (2 * ‖w‖) ^ (5 * (220 * (m + 1))) :=
        mul_le_mul (mul_le_mul h1 h2 (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)) h3
          (prod_nonneg fun _ _ => norm_nonneg _) (mul_nonneg (by positivity) hp)
    _ = 3 * ‖w‖ * (2 * ‖w‖) ^ (2200 * (m + 1)) := by
        rw [mul_assoc, ← pow_add, show 5 * (220 * (m + 1)) + 5 * (220 * (m + 1)) = 2200 * (m + 1) by
          ring]

lemma norm_DC_ge (m : ℕ) {w : ℂ} (hw : R₁ m ≤ ‖w‖) :
    (‖w‖ / 2) ^ (∑ k ∈ range (Z7.nOf m + 1), BkC m k) ≤ ‖DC m w‖ := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold DC
  rw [norm_prod, ← prod_pow_eq_pow_sum]
  refine prod_le_prod₀ (fun _ _ => by positivity) (fun k hk => ?_)
  rw [norm_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have hk' : (k : ℝ) ≤ 240 * ((m : ℝ) + 1) := by
    have := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have : (k : ℝ) ≤ (Z7.nOf m : ℝ) := by exact_mod_cast this
    rw [nOf_real] at this; linarith
  have h1 : ‖w‖ - (k : ℝ) ≤ ‖w + (k : ℂ)‖ := by
    have := norm_sub_norm_le w (-(k : ℂ))
    rw [norm_neg, Complex.norm_natCast, sub_neg_eq_add] at this
    exact this
  unfold R₁ at hw
  linarith

/-- `‖RC m w‖ ≤ C₁ / ‖w‖²` for `‖w‖ ≥ R₁`. -/
lemma norm_RC_le (m : ℕ) {w : ℂ} (hw : R₁ m ≤ ‖w‖) :
    ‖RC m w‖ ≤ 3 * 2 ^ (2200 * (m + 1)) * 2 ^ (∑ k ∈ range (Z7.nOf m + 1), BkC m k)
      / ‖w‖ ^ 2 := by
  have hw1 : 1 ≤ ‖w‖ := (one_le_R₁ m).trans hw
  have hw0 : 0 < ‖w‖ := by linarith
  set A := 2200 * (m + 1) with hA
  set S := ∑ k ∈ range (Z7.nOf m + 1), BkC m k with hS
  have hAS : A + 3 ≤ S := by rw [hA, hS, sum_BkC]; omega
  have hN := norm_NC_le m hw
  have hD := norm_DC_ge m hw
  have hDpos : 0 < (‖w‖ / 2) ^ S := by positivity
  rw [RC_eq, norm_div]
  rw [div_le_div_iff₀ (hDpos.trans_le hD) (by positivity)]
  calc ‖NC m w‖ * ‖w‖ ^ 2 ≤ 3 * ‖w‖ * (2 * ‖w‖) ^ A * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hN (by positivity)
    _ = 3 * 2 ^ A * 2 ^ S * (‖w‖ / 2) ^ S * ‖w‖ ^ (A + 3) / ‖w‖ ^ S := by
        rw [div_pow]
        field_simp
        ring
    _ ≤ 3 * 2 ^ A * 2 ^ S * (‖w‖ / 2) ^ S := by
        rw [div_le_iff₀ (by positivity)]
        have : ‖w‖ ^ (A + 3) ≤ ‖w‖ ^ S := pow_le_pow_right₀ hw1 hAS
        have hc : 0 ≤ 3 * 2 ^ A * 2 ^ S * (‖w‖ / 2) ^ S := by positivity
        exact mul_le_mul_of_nonneg_left this hc
    _ ≤ 3 * 2 ^ A * 2 ^ S * ‖DC m w‖ := by gcongr

lemma not_mem_poles_of_norm (m : ℕ) {u : ℂ} (hu : R₁ m ≤ ‖u‖) : u ∈ (poles m)ᶜ := by
  rintro ⟨k, _, hk, rfl⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [norm_neg, Complex.norm_natCast] at hu
  have : (k : ℝ) ≤ 240 * ((m : ℝ) + 1) := by
    have : (k : ℝ) ≤ (Z7.nOf m : ℝ) := by exact_mod_cast hk
    rw [nOf_real] at this; linarith
  unfold R₁ at hu
  linarith

/-- **Decay.** For every `j` and `c > -1` there is `C` with `‖R_n⁽ʲ⁾(z)‖ ≤ C (1 + ‖z‖²)⁻¹` on
`Re z ≥ c`. -/
theorem RCd_bound (m j : ℕ) {c : ℝ} (hc : -1 < c) :
    ∃ C : ℝ, ∀ z : ℂ, c ≤ z.re → ‖RCd m j z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹ := by
  set C₁ : ℝ := 3 * 2 ^ (2200 * (m + 1)) * 2 ^ (∑ k ∈ range (Z7.nOf m + 1), BkC m k) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hdec := norm_iterate_deriv_le_of_decay (isOpen_compl_poles m) (RC_differentiableOn m)
    (A := R₁ m) (C := C₁) (one_le_R₁ m) hC₁0 (fun w hw => not_mem_poles_of_norm m hw)
    (fun w hw => norm_RC_le m hw) j
  refine exists_bound_of_decay (R := R₁ m + j)
    (by have := one_le_R₁ m; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    (by positivity) ?_ hdec
  intro z hz
  exact (RCd_differentiableAt m j (mem_compl_poles_of_re (by
    simp only [Set.mem_ofPred_eq] at hz; linarith))).continuousAt.continuousWithinAt

end ZetaIrr.Z7.Analytic
