/-
# From the saddle-point decomposition to nonvanishing (PROOF_BETA100 §6.6, (6.6.1) and (ii))

`frequently_ne_zero_of_saddle` packages the last deduction of Lemma 6(ii). Suppose that along a
progression `n_m` (step `q`, `n_m → ∞`) the contour integral `J_m` splits as

    J_m = e^{λ_m + n_m Ω} · n_m d · D_m + E_m,

where `D_m` is the Laplace integral over the disc segment, with

    |D_m - a₀ √(2π/(n_m K))| ≤ B / n_m          (from `laplace_bound`)
    |E_m| ≤ ε_m e^{λ_m + n_m Re Ω} √n_m,  ε_m → 0   (far part, from (U), (S2), (S3)),

`a₀ ≠ 0`, `d ≠ 0`, `K > 0`, `λ_m` real. If `L_m = κ Im J_m` with `κ ≠ 0` (here `κ = -1/π`) and
`sin(q Im Ω) ≠ 0` (H4), then `L_m ≠ 0` for infinitely many `m`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Analytic.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace ZetaIrr.Analytic

open Filter Topology Real

theorem frequently_ne_zero_of_saddle (L n lam εf : ℕ → ℝ) (J D E : ℕ → ℂ) (Ω d a₀ : ℂ)
    (K q κ B : ℝ) (hK : 0 < K) (hd : d ≠ 0) (ha : a₀ ≠ 0) (hκ : κ ≠ 0)
    (hq : Real.sin (q * Ω.im) ≠ 0) (hn : ∀ m, n (m + 1) = n m + q)
    (hnlim : Tendsto n atTop atTop)
    (hL : ∀ m, L m = κ * (J m).im)
    (hJ : ∀ᶠ m in atTop,
      J m = Complex.exp ((lam m : ℂ) + n m * Ω) * ((n m : ℂ) * d) * D m + E m)
    (hD : ∀ᶠ m in atTop, ‖D m - a₀ * ((√(2 * π / (n m * K)) : ℝ) : ℂ)‖ ≤ B / n m)
    (hE : ∀ᶠ m in atTop, ‖E m‖ ≤ εf m * Real.exp (lam m + n m * Ω.re) * √(n m))
    (hεf : Tendsto εf atTop (𝓝 0)) :
    ∃ᶠ m in atTop, L m ≠ 0 := by
  set C₀ : ℂ := d * a₀ * ((√(2 * π / K) : ℝ) : ℂ) with hC₀
  have hC : C₀ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hd ha) ?_
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  -- normalised error
  let δ : ℕ → ℂ := fun m =>
    ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * J m - C₀ * Complex.exp (n m * Ω)
  let ε : ℕ → ℝ := fun m => (δ m).im / Real.exp (n m * Ω.re)
  have hnpos : ∀ᶠ m in atTop, 0 < n m := hnlim.eventually (eventually_gt_atTop 0)
  refine frequently_ne_zero_of_im_asymptotic L (fun m => κ * Real.exp (lam m) * √(n m)) ε n C₀
    Ω q hC hq hn ?_ ?_ ?_
  · filter_upwards [hnpos] with m hm
    exact mul_ne_zero (mul_ne_zero hκ (Real.exp_pos _).ne') (Real.sqrt_pos.2 hm).ne'
  · -- `|ε m| ≤ |d| B / √n + εf m → 0`
    have hbound : ∀ᶠ m in atTop, ‖ε m‖ ≤ ‖d‖ * B / √(n m) + εf m := by
      filter_upwards [hnpos, hJ, hD, hE] with m hm hJm hDm hEm
      have hs : 0 < √(n m) := Real.sqrt_pos.2 hm
      have hsq : √(n m) * √(n m) = n m := Real.mul_self_sqrt hm.le
      have he : 0 < Real.exp (n m * Ω.re) := Real.exp_pos _
      have hroot : √(n m) * √(2 * π / (n m * K)) = √(2 * π / K) := by
        rw [← Real.sqrt_mul hm.le]; congr 1; field_simp
      -- the algebraic form of `δ m`
      have hδ : δ m = Complex.exp (n m * Ω) * d * ((√(n m) : ℝ) : ℂ) *
            (D m - a₀ * ((√(2 * π / (n m * K)) : ℝ) : ℂ))
          + ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * E m := by
        have hs' : ((√(n m) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
        have hreal : Real.exp (-lam m) / √(n m) * Real.exp (lam m) * n m = √(n m) := by
          calc Real.exp (-lam m) / √(n m) * Real.exp (lam m) * n m
              = (Real.exp (-lam m) * Real.exp (lam m)) * (n m / √(n m)) := by ring
            _ = n m / √(n m) := by rw [← Real.exp_add]; simp
            _ = √(n m) := by rw [div_eq_iff hs.ne', hsq]
        have key : ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * Complex.exp ((lam m : ℂ) + n m * Ω)
            * (n m : ℂ) = Complex.exp (n m * Ω) * ((√(n m) : ℝ) : ℂ) := by
          rw [Complex.exp_add, ← Complex.ofReal_exp]
          have : ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * ((Real.exp (lam m) : ℝ) : ℂ)
              * (n m : ℂ) = ((√(n m) : ℝ) : ℂ) := by exact_mod_cast hreal
          rw [← this]; ring
        have hroot' : ((√(n m) : ℝ) : ℂ) * ((√(2 * π / (n m * K)) : ℝ) : ℂ)
            = ((√(2 * π / K) : ℝ) : ℂ) := by exact_mod_cast hroot
        simp only [δ, hJm]
        have e1 : ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * (Complex.exp ((lam m : ℂ) + n m * Ω)
            * ((n m : ℂ) * d) * D m + E m)
            = (((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * Complex.exp ((lam m : ℂ) + n m * Ω)
              * (n m : ℂ)) * d * D m + ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * E m := by ring
        rw [e1, key, hC₀, ← hroot']
        ring
      have hnδ : ‖δ m‖ ≤ Real.exp (n m * Ω.re) * (‖d‖ * B / √(n m) + εf m) := by
        rw [hδ]
        refine (norm_add_le _ _).trans ?_
        have h1 : ‖Complex.exp (n m * Ω) * d * ((√(n m) : ℝ) : ℂ) *
            (D m - a₀ * ((√(2 * π / (n m * K)) : ℝ) : ℂ))‖
            ≤ Real.exp (n m * Ω.re) * (‖d‖ * B / √(n m)) := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hs]
          have hre : ((n m : ℂ) * Ω).re = n m * Ω.re := by simp
          rw [hre]
          calc Real.exp (n m * Ω.re) * ‖d‖ * √(n m) *
                ‖D m - a₀ * ((√(2 * π / (n m * K)) : ℝ) : ℂ)‖
              ≤ Real.exp (n m * Ω.re) * ‖d‖ * √(n m) * (B / n m) := by gcongr
            _ = Real.exp (n m * Ω.re) * (‖d‖ * B / √(n m)) := by
                have h' : √(n m) / n m = 1 / √(n m) := by
                  rw [div_eq_div_iff hm.ne' hs.ne', one_mul, hsq]
                calc Real.exp (n m * Ω.re) * ‖d‖ * √(n m) * (B / n m)
                    = Real.exp (n m * Ω.re) * ‖d‖ * B * (√(n m) / n m) := by ring
                  _ = _ := by rw [h']; ring
        have h2 : ‖((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * E m‖
            ≤ Real.exp (n m * Ω.re) * εf m := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (div_pos (Real.exp_pos _) hs)]
          calc Real.exp (-lam m) / √(n m) * ‖E m‖
              ≤ Real.exp (-lam m) / √(n m) * (εf m * Real.exp (lam m + n m * Ω.re) * √(n m)) := by
                gcongr
            _ = Real.exp (n m * Ω.re) * εf m := by
                rw [Real.exp_add]
                field_simp
                rw [mul_comm (Real.exp (-lam m)), mul_assoc, ← Real.exp_add]
                simp
        calc _ ≤ Real.exp (n m * Ω.re) * (‖d‖ * B / √(n m)) + Real.exp (n m * Ω.re) * εf m :=
              add_le_add h1 h2
          _ = _ := by ring
      have hεm : ‖ε m‖ = |(δ m).im| / Real.exp (n m * Ω.re) := by
        simp only [ε, Real.norm_eq_abs, abs_div, abs_of_pos he]
      rw [hεm, div_le_iff₀ he]
      calc |(δ m).im| ≤ ‖δ m‖ := Complex.abs_im_le_norm _
        _ ≤ _ := hnδ
        _ = _ := by ring
    refine squeeze_zero_norm' hbound ?_
    have h1 : Tendsto (fun m => ‖d‖ * B / √(n m)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hnlim)
    simpa using h1.add hεf
  · filter_upwards [hnpos] with m hm
    have hs : 0 < √(n m) := Real.sqrt_pos.2 hm
    rw [hL]
    simp only [ε, δ]
    have he : Real.exp (n m * Ω.re) ≠ 0 := (Real.exp_pos _).ne'
    have him : ((((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * J m - C₀ * Complex.exp (n m * Ω)).im)
        = Real.exp (-lam m) / √(n m) * (J m).im - (C₀ * Complex.exp (n m * Ω)).im := by
      rw [Complex.sub_im, Complex.im_ofReal_mul]
    rw [him, div_mul_cancel₀ _ he]
    have hone : Real.exp (lam m) * √(n m) * (Real.exp (-lam m) / √(n m)) = 1 := by
      field_simp; rw [← Real.exp_add]; simp
    set A := (C₀ * Complex.exp (n m * Ω)).im
    rw [show A + (Real.exp (-lam m) / √(n m) * (J m).im - A)
        = Real.exp (-lam m) / √(n m) * (J m).im by ring]
    rw [show κ * Real.exp (lam m) * √(n m) * (Real.exp (-lam m) / √(n m) * (J m).im)
        = κ * (Real.exp (lam m) * √(n m) * (Real.exp (-lam m) / √(n m))) * (J m).im by ring,
      hone, mul_one]

/-- Variant with `|D_m - a₀√(2π/(nK))| ≤ εD_m/√n_m`, `εD → 0`. -/
theorem frequently_ne_zero_of_saddle' (L n lam εf : ℕ → ℝ) (J D E : ℕ → ℂ) (Ω d a₀ : ℂ)
    (K q κ : ℝ) (εD : ℕ → ℝ) (hK : 0 < K) (hd : d ≠ 0) (ha : a₀ ≠ 0) (hκ : κ ≠ 0)
    (hq : Real.sin (q * Ω.im) ≠ 0) (hn : ∀ m, n (m + 1) = n m + q)
    (hnlim : Tendsto n atTop atTop)
    (hL : ∀ m, L m = κ * (J m).im)
    (hJ : ∀ᶠ m in atTop,
      J m = Complex.exp ((lam m : ℂ) + n m * Ω) * ((n m : ℂ) * d) * D m + E m)
    (hD : ∀ᶠ m in atTop, ‖D m - a₀ * ((√(2 * π / (n m * K)) : ℝ) : ℂ)‖ ≤ εD m / √(n m))
    (hεD : Tendsto εD atTop (𝓝 0))
    (hE : ∀ᶠ m in atTop, ‖E m‖ ≤ εf m * Real.exp (lam m + n m * Ω.re) * √(n m))
    (hεf : Tendsto εf atTop (𝓝 0)) :
    ∃ᶠ m in atTop, L m ≠ 0 := by
  set C₀ : ℂ := d * a₀ * ((√(2 * π / K) : ℝ) : ℂ) with hC₀
  have hC : C₀ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hd ha) ?_
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  -- normalised error
  let δ : ℕ → ℂ := fun m =>
    ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * J m - C₀ * Complex.exp (n m * Ω)
  let ε : ℕ → ℝ := fun m => (δ m).im / Real.exp (n m * Ω.re)
  have hnpos : ∀ᶠ m in atTop, 0 < n m := hnlim.eventually (eventually_gt_atTop 0)
  refine frequently_ne_zero_of_im_asymptotic L (fun m => κ * Real.exp (lam m) * √(n m)) ε n C₀
    Ω q hC hq hn ?_ ?_ ?_
  · filter_upwards [hnpos] with m hm
    exact mul_ne_zero (mul_ne_zero hκ (Real.exp_pos _).ne') (Real.sqrt_pos.2 hm).ne'
  · -- `|ε m| ≤ |d| B / √n + εf m → 0`
    have hbound : ∀ᶠ m in atTop, ‖ε m‖ ≤ ‖d‖ * εD m + εf m := by
      filter_upwards [hnpos, hJ, hD, hE] with m hm hJm hDm hEm
      have hs : 0 < √(n m) := Real.sqrt_pos.2 hm
      have hsq : √(n m) * √(n m) = n m := Real.mul_self_sqrt hm.le
      have he : 0 < Real.exp (n m * Ω.re) := Real.exp_pos _
      have hroot : √(n m) * √(2 * π / (n m * K)) = √(2 * π / K) := by
        rw [← Real.sqrt_mul hm.le]; congr 1; field_simp
      -- the algebraic form of `δ m`
      have hδ : δ m = Complex.exp (n m * Ω) * d * ((√(n m) : ℝ) : ℂ) *
            (D m - a₀ * ((√(2 * π / (n m * K)) : ℝ) : ℂ))
          + ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * E m := by
        have hs' : ((√(n m) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
        have hreal : Real.exp (-lam m) / √(n m) * Real.exp (lam m) * n m = √(n m) := by
          calc Real.exp (-lam m) / √(n m) * Real.exp (lam m) * n m
              = (Real.exp (-lam m) * Real.exp (lam m)) * (n m / √(n m)) := by ring
            _ = n m / √(n m) := by rw [← Real.exp_add]; simp
            _ = √(n m) := by rw [div_eq_iff hs.ne', hsq]
        have key : ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * Complex.exp ((lam m : ℂ) + n m * Ω)
            * (n m : ℂ) = Complex.exp (n m * Ω) * ((√(n m) : ℝ) : ℂ) := by
          rw [Complex.exp_add, ← Complex.ofReal_exp]
          have : ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * ((Real.exp (lam m) : ℝ) : ℂ)
              * (n m : ℂ) = ((√(n m) : ℝ) : ℂ) := by exact_mod_cast hreal
          rw [← this]; ring
        have hroot' : ((√(n m) : ℝ) : ℂ) * ((√(2 * π / (n m * K)) : ℝ) : ℂ)
            = ((√(2 * π / K) : ℝ) : ℂ) := by exact_mod_cast hroot
        simp only [δ, hJm]
        have e1 : ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * (Complex.exp ((lam m : ℂ) + n m * Ω)
            * ((n m : ℂ) * d) * D m + E m)
            = (((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * Complex.exp ((lam m : ℂ) + n m * Ω)
              * (n m : ℂ)) * d * D m + ((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * E m := by ring
        rw [e1, key, hC₀, ← hroot']
        ring
      have hnδ : ‖δ m‖ ≤ Real.exp (n m * Ω.re) * (‖d‖ * εD m + εf m) := by
        rw [hδ]
        refine (norm_add_le _ _).trans ?_
        have h1 : ‖Complex.exp (n m * Ω) * d * ((√(n m) : ℝ) : ℂ) *
            (D m - a₀ * ((√(2 * π / (n m * K)) : ℝ) : ℂ))‖
            ≤ Real.exp (n m * Ω.re) * (‖d‖ * εD m) := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hs]
          have hre : ((n m : ℂ) * Ω).re = n m * Ω.re := by simp
          rw [hre]
          calc Real.exp (n m * Ω.re) * ‖d‖ * √(n m) *
                ‖D m - a₀ * ((√(2 * π / (n m * K)) : ℝ) : ℂ)‖
              ≤ Real.exp (n m * Ω.re) * ‖d‖ * √(n m) * (εD m / √(n m)) := by gcongr
            _ = Real.exp (n m * Ω.re) * (‖d‖ * εD m) := by field_simp
        have h2 : ‖((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * E m‖
            ≤ Real.exp (n m * Ω.re) * εf m := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (div_pos (Real.exp_pos _) hs)]
          calc Real.exp (-lam m) / √(n m) * ‖E m‖
              ≤ Real.exp (-lam m) / √(n m) * (εf m * Real.exp (lam m + n m * Ω.re) * √(n m)) := by
                gcongr
            _ = Real.exp (n m * Ω.re) * εf m := by
                rw [Real.exp_add]
                field_simp
                rw [mul_comm (Real.exp (-lam m)), mul_assoc, ← Real.exp_add]
                simp
        calc _ ≤ Real.exp (n m * Ω.re) * (‖d‖ * εD m) + Real.exp (n m * Ω.re) * εf m :=
              add_le_add h1 h2
          _ = _ := by ring
      have hεm : ‖ε m‖ = |(δ m).im| / Real.exp (n m * Ω.re) := by
        simp only [ε, Real.norm_eq_abs, abs_div, abs_of_pos he]
      rw [hεm, div_le_iff₀ he]
      calc |(δ m).im| ≤ ‖δ m‖ := Complex.abs_im_le_norm _
        _ ≤ _ := hnδ
        _ = _ := by ring
    refine squeeze_zero_norm' hbound ?_
    have h1 : Tendsto (fun m => ‖d‖ * εD m) atTop (𝓝 0) := by
      simpa using hεD.const_mul ‖d‖
    simpa using h1.add hεf
  · filter_upwards [hnpos] with m hm
    have hs : 0 < √(n m) := Real.sqrt_pos.2 hm
    rw [hL]
    simp only [ε, δ]
    have he : Real.exp (n m * Ω.re) ≠ 0 := (Real.exp_pos _).ne'
    have him : ((((Real.exp (-lam m) / √(n m) : ℝ) : ℂ) * J m - C₀ * Complex.exp (n m * Ω)).im)
        = Real.exp (-lam m) / √(n m) * (J m).im - (C₀ * Complex.exp (n m * Ω)).im := by
      rw [Complex.sub_im, Complex.im_ofReal_mul]
    rw [him, div_mul_cancel₀ _ he]
    have hone : Real.exp (lam m) * √(n m) * (Real.exp (-lam m) / √(n m)) = 1 := by
      field_simp; rw [← Real.exp_add]; simp
    set A := (C₀ * Complex.exp (n m * Ω)).im
    rw [show A + (Real.exp (-lam m) / √(n m) * (J m).im - A)
        = Real.exp (-lam m) / √(n m) * (J m).im by ring]
    rw [show κ * Real.exp (lam m) * √(n m) * (Real.exp (-lam m) / √(n m) * (J m).im)
        = κ * (Real.exp (lam m) * √(n m) * (Real.exp (-lam m) / √(n m))) * (J m).im by ring,
      hone, mul_one]

end ZetaIrr.Analytic
