/-
# The steepest-descent direction `d` at the Z7 saddle, and the Taylor-segment endpoints

Used for the Taylor disc condition (S1).

With `w = Ψ''(x₀)`, `K = |w|`, `u = -conj(w)/K` (a unit number) and `v = 1 + u`, put

    dir = v / |v|.

Then `|dir| = 1` and `Ψ''(x₀) · dir² = -K` (`dir_norm`, `dir_sq`). `dB` is a certified box for
`dir`, and `ePlus = x₀ + ρ dir`, `eMinus = x₀ - ρ dir` (the Taylor segment endpoints, `ρ = 1/20`)
are within `Dc = 10⁻⁹` of the rational points `upStart`, `dnStart` (`PolyDataZ7.lean`) where the
certified polylines begin.
-/
import ZetaIrrational.Z7.Interval.SaddleZ7
import ZetaIrrational.Z7.Interval.PolyDataZ7
import ZetaIrrational.Interval.Sqrt

namespace ZetaIrr.Z7.Interval

open Complex Metric ZetaIrr.Interval ZetaIrr.Interval.IV Real ComplexConjugate

/-- `w = Ψ''(x₀)`. -/
noncomputable def w0 : ℂ := d2psiL facZ7 x₀
/-- `K = |Ψ''(x₀)|`. -/
noncomputable def Kx : ℝ := ‖w0‖
noncomputable def u0 : ℂ := -conj w0 / (Kx : ℂ)
noncomputable def v0 : ℂ := 1 + u0
/-- **The direction** `dir = v / |v|`. -/
noncomputable def dir : ℂ := v0 / (‖v0‖ : ℂ)

lemma Kx_ge : (28 : ℝ) ≤ Kx := Z7_K_ge

lemma Kx_pos : 0 < Kx := by linarith [Kx_ge]

/-- Box for `conj`. -/
def conjB (B : CB) : CB := ⟨B.re, B.im.neg⟩

lemma mem_conjB {B : CB} {z : ℂ} (hz : B.mem z) : (conjB B).mem (conj z) :=
  ⟨by simpa [conjB] using hz.1, by simpa [conjB] using IV.mem_neg hz.2⟩

def KxB : IV := sqrtIV (CB.normSq d2B)
def uB : CB := (conjB d2B).neg.mul (CB.inv (CB.ofIV KxB))
def vB : CB := (CB.ofQ 1 0).add uB
def nB : IV := sqrtIV (CB.normSq vB)
def dB : CB := vB.mul (CB.inv (CB.ofIV nB))

lemma mem_KxB : KxB.mem Kx := by
  have := mem_sqrtIV (CB.mem_normSq Z7_d2_mem)
  rwa [← Complex.norm_def] at this

lemma mem_uB : uB.mem u0 := by
  have h := CB.mem_mul (CB.mem_neg (mem_conjB Z7_d2_mem)) (CB.mem_inv (CB.mem_ofIV mem_KxB))
  have e : u0 = -conj w0 * ((Kx : ℝ) : ℂ)⁻¹ := by rw [u0, div_eq_mul_inv]
  rw [e]; exact h

lemma mem_vB : vB.mem v0 := CB.mem_add mem_one mem_uB

lemma mem_nB : nB.mem ‖v0‖ := by
  have := mem_sqrtIV (CB.mem_normSq mem_vB)
  rwa [← Complex.norm_def] at this

lemma mem_dB : dB.mem dir := by
  have h := CB.mem_mul mem_vB (CB.mem_inv (CB.mem_ofIV mem_nB))
  have e : dir = v0 * ((‖v0‖ : ℝ) : ℂ)⁻¹ := by rw [dir, div_eq_mul_inv]
  rw [e]; exact h

lemma chk_v : vB.re.loGt (2 / 5) = true := by decide +kernel

lemma v0_ne : v0 ≠ 0 := by
  intro h
  have := gt_of_loGt mem_vB.1 chk_v
  rw [h] at this; norm_num at this

theorem dir_norm : ‖dir‖ = 1 := by
  have hn : ‖v0‖ ≠ 0 := norm_ne_zero_iff.2 v0_ne
  rw [dir, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self hn]

theorem dir_sq : w0 * dir ^ 2 = -(Kx : ℂ) := by
  have hK : (Kx : ℂ) ≠ 0 := by exact_mod_cast Kx_pos.ne'
  have hv := v0_ne
  have hcv : conj v0 ≠ 0 := by simpa using hv
  have hWW : w0 * conj w0 = (Kx : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; simp [Kx]
  have hv2 : ((‖v0‖ : ℝ) : ℂ) ^ 2 = v0 * conj v0 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hconj : conj v0 = 1 - w0 / (Kx : ℂ) := by
    simp [v0, u0, map_div₀, Complex.conj_ofReal, sub_eq_add_neg, neg_div]
  have hvd : v0 = 1 - conj w0 / (Kx : ℂ) := by simp [v0, u0, sub_eq_add_neg, neg_div]
  have h1 : w0 * conj w0 / (Kx : ℂ) = Kx := by rw [hWW]; field_simp
  have key : w0 * v0 = -(Kx : ℂ) * conj v0 := by
    calc w0 * v0 = w0 - w0 * conj w0 / (Kx : ℂ) := by rw [hvd]; ring
      _ = w0 - Kx := by rw [h1]
      _ = -(Kx : ℂ) * conj v0 := by rw [hconj]; field_simp; ring
  rw [dir, div_pow, hv2]
  have e2 : v0 ^ 2 / (v0 * conj v0) = v0 / conj v0 := by field_simp
  rw [e2, ← mul_div_assoc, key, mul_div_assoc, div_self hcv, mul_one]

/-! ## Endpoints of the Taylor segment -/

/-- `x₀ + ρ dir`. -/
noncomputable def ePlus : ℂ := x₀ + (ρ : ℂ) * dir
/-- `x₀ - ρ dir`. -/
noncomputable def eMinus : ℂ := x₀ - (ρ : ℂ) * dir

def ePlusB : CB := B0box.add (dB.smul ρ)
def eMinusB : CB := B0box.sub (dB.smul ρ)

lemma mem_ePlusB : ePlusB.mem ePlus :=
  CB.mem_add (mem_B0box saddle_mem) (by simpa using CB.mem_smul ρ mem_dB)

lemma mem_eMinusB : eMinusB.mem eMinus :=
  CB.mem_sub (mem_B0box saddle_mem) (by simpa using CB.mem_smul ρ mem_dB)

/-- Connector radius. -/
def Dc : ℚ := 1 / 10 ^ 9

lemma chk_ePlus : (ePlusB.sub (CB.ofQ upStart.1 upStart.2)).normLe Dc = true := by decide +kernel
lemma chk_eMinus : (eMinusB.sub (CB.ofQ dnStart.1 dnStart.2)).normLe Dc = true := by
  decide +kernel

theorem ePlus_near : ePlus ∈ closedBall (toC upStart) Dc := by
  rw [mem_closedBall, dist_eq_norm]
  exact CB.norm_le_of_normLe (CB.mem_sub mem_ePlusB (CB.mem_ofQ _ _)) chk_ePlus

theorem eMinus_near : eMinus ∈ closedBall (toC dnStart) Dc := by
  rw [mem_closedBall, dist_eq_norm]
  exact CB.norm_le_of_normLe (CB.mem_sub mem_eMinusB (CB.mem_ofQ _ _)) chk_eMinus

end ZetaIrr.Z7.Interval
