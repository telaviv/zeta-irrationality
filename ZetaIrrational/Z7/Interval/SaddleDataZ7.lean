/-
# An instance of `Z7.Analytic.SaddleData` from the Z7 interval certificate

`Z7_saddleData : ZetaIrr.Z7.Analytic.SaddleData` — the saddle conditions (S0)–(S5) for instance Z7,
with
* `x₀` the certified saddle (`SaddleZ7.lean`), `d = dir`, `K = |Ψ''(x₀)|`, `M = Mcert ≈ 310.2`,
  `ρ = 1/20`;
* the path `v 0 = x_c, …, v 4 = dnStart, v 5 = x₀ - ρ d, v 6 = x₀ + ρ d, v 7 = upStart, …,
  v 23 = xtop` (`Kd = 5`, `Ktop = 23`), from `ContourZ7.lean`;
* `a = 1/100`, `η = π - 2.76`, `ηfar = 0.0199414`, `rate = q0 - 3π = 12 - 3π`, `Y₀ = 0`,
  `δ₀ = 10⁻⁷`;
* the field `sin_ne` (`sin(240 Im Ω) ≠ 0`) from `Z7_sinqtheta_le : sin(240 Im Ω) < -0.9`;
* `ReΩ_le` from `Z7_ReOmega_le : Re Ω ≤ -10.1167485`.

The first segment (moved start point, field `S2_first`) is handled by a mean-value bound on the
box around `[x_c, v 1]` widened by `δ₀` (`ConnZ7.lean`), costing `G δ₀ ≤ 10⁻⁵` of the far margin.
-/
import ZetaIrrational.Z7.Interval.BridgeZ7
import ZetaIrrational.Z7.Analytic.SaddleData

namespace ZetaIrr.Z7.Interval

open Complex Metric ZetaIrr.Interval ZetaIrr.Interval.IV ZetaIrr.Fam.Interval Real Set
open ZetaIrr.Z7.Analytic (SaddleData PsiZ Psi1Z Psi2Z Psi3Z phaseZ SectorAt)

/-! ## Polyline indexing -/

lemma onPoly_of_getD (a : ℚ × ℚ) (pts : List (ℚ × ℚ)) (i : ℕ) (hi : i < pts.length) {z : ℂ}
    (hz : z ∈ segment ℝ (toC ((a :: pts).getD i (0, 0))) (toC (pts.getD i (0, 0)))) :
    onPoly a pts z := by
  induction pts generalizing a i with
  | nil => simp at hi
  | cons b rest ih =>
    cases i with
    | zero => left; simpa using hz
    | succ i =>
      right
      exact ih b i (by simpa using hi) (by simpa using hz)

def lowL : List (ℚ × ℚ) := dnPts.reverse ++ [dnStart]
def upL : List (ℚ × ℚ) := upStart :: upPts

/-- The path vertices. -/
noncomputable def vZ7 (k : ℕ) : ℂ :=
  if k ≤ 4 then toC (lowL.getD k (0, 0)) else if k = 5 then eMinus else if k = 6 then ePlus
  else toC (upL.getD (k - 7) (0, 0))

lemma seg_param {p q z : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hz : z = p + t * (q - p)) :
    z ∈ segment ℝ p q := by
  rw [segment_eq_image']
  refine ⟨t, ht, ?_⟩
  change p + t • (q - p) = z
  rw [hz, Complex.real_smul]

lemma seg_param' {p q z : ℂ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (hz : z = p + t * (q - p)) :
    z ∈ segment ℝ p q := seg_param ⟨ht.1.le, ht.2⟩ hz

/-! ## Constants -/

noncomputable def etaS : ℝ := π - 276 / 100
noncomputable def ηfarD : ℝ := (ηfar : ℝ) - 1 / 10 ^ 5

lemma etaS_pos : 0 < etaS := by have := eta_pos; unfold etaS; linarith

lemma ηfarD_pos : 0 < ηfarD := by unfold ηfarD; norm_num [ηfar]

/-! ## The first segment, widened -/

lemma box_convex {lo1 hi1 lo2 hi2 : ℚ} {z w u : ℂ}
    (hz : (CB.mk (ival lo1 hi1) (ival lo2 hi2)).mem z)
    (hw : (CB.mk (ival lo1 hi1) (ival lo2 hi2)).mem w) (hu : u ∈ segment ℝ z w) :
    (CB.mk (ival lo1 hi1) (ival lo2 hi2)).mem u := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hu
  have h1 := combo_mem (x := z.re) (y := w.re) hs ht hst
  have h2 := combo_mem (x := z.im) (y := w.im) hs ht hst
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hz
  obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := hw
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul]
  · exact (le_min a1 b1).trans h1.1
  · exact h1.2.trans (max_le a2 b2)
  · exact (le_min a3 b3).trans h2.1
  · exact h2.2.trans (max_le a4 b4)

lemma mem_firstBox_of {z' z : ℂ} (hz' : z' ∈ segment ℝ (toC firstA) (toC firstB))
    (hzz : ‖z - z'‖ ≤ δ0) : firstBox.mem z := by
  have hb := mem_segBox hz'
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hb
  have hr := (Complex.abs_re_le_norm (z - z')).trans hzz
  have hi := (Complex.abs_im_le_norm (z - z')).trans hzz
  rw [sub_re, abs_le] at hr; rw [sub_im, abs_le] at hi
  simp only [Rat.cast_min, Rat.cast_max] at h1 h2 h3 h4
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_min,
    Rat.cast_max] <;> linarith [hr.1, hr.2, hi.1, hi.2]

theorem first_bound {z' z : ℂ} (hz' : z' ∈ segment ℝ (toC firstA) (toC firstB))
    (hzz : ‖z - z'‖ ≤ δ0) : (f z).re ≤ (f z').re + 1 / 10 ^ 5 := by
  have hbz : firstBox.mem z := mem_firstBox_of hz' hzz
  have hbz' : firstBox.mem z' := mem_firstBox_of hz' (by simp [δ0])
  have hsub : ∀ u ∈ segment ℝ z' z, firstBox.mem u := fun u hu => box_convex hbz' hbz hu
  obtain ⟨hgre, hgim⟩ := chk_first_re
  have hc := chk_first_G
  generalize hR : firstG.re = R at hgre hc
  generalize hI : firstG.im = Im at hgim hc
  cases R with
  | top => exact absurd rfl hgre
  | ival r1 r2 =>
  cases Im with
  | top => exact absurd rfl hgim
  | ival i1 i2 =>
  set Cq : ℚ := absHi (ival r1 r2) + absHi (ival i1 i2) with hCq
  have hG : ∀ u ∈ segment ℝ z' z, ‖gL 3 facZ7 u‖ ≤ (Cq : ℝ) := by
    intro u hu
    have hm : firstG.mem (gL 3 facZ7 u) :=
      CB.mem_sub (mem_dpsiB 40 16 facZ7 (hsub u hu)) (mem_phIB 3)
    have := norm_le_absHi hm hR hI
    rw [hCq]; push_cast; exact this
  have hmv := (convex_segment z' z).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fL 3 facZ7) (f' := gL 3 facZ7)
    (fun u hu => (hasDerivAt_fL (ω := 3) (good_of_goodB (hsub u hu) chk_first_good)).hasDerivWithinAt)
    hG (left_mem_segment ℝ z' z) (right_mem_segment ℝ z' z)
  have hc' : ((Cq * δ0 : ℚ) : ℝ) ≤ ((1 / 10 ^ 5 : ℚ) : ℝ) := by exact_mod_cast hc
  rw [Rat.cast_mul] at hc'
  have h5 : ((1 / 10 ^ 5 : ℚ) : ℝ) = 1 / 10 ^ 5 := by norm_num
  rw [h5] at hc'
  have hG0 : (0 : ℝ) ≤ (Cq : ℝ) := (norm_nonneg _).trans (hG z' (left_mem_segment ℝ z' z))
  have hδ : (Cq : ℝ) * ‖z - z'‖ ≤ (Cq : ℝ) * δ0 := mul_le_mul_of_nonneg_left hzz hG0
  have hre := (Complex.re_le_norm (fL 3 facZ7 z - fL 3 facZ7 z')).trans hmv
  rw [sub_re] at hre
  change (fL 3 facZ7 z).re ≤ (fL 3 facZ7 z').re + 1 / 10 ^ 5
  linarith

theorem first_sector {z' z : ℂ} (hz' : z' ∈ segment ℝ (toC firstA) (toC firstB))
    (hzz : ‖z - z'‖ ≤ δ0) : ∀ a ∈ facZ7, ((amin : ℚ) : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax :=
  sector_of_sectorQ 40 16 amin Amax (mem_firstBox_of hz' hzz) chk_first_sec

/-! ## Path facts -/

lemma lowL0 : lowL.getD 0 (0, 0) = (xc, 0) := by decide +kernel
lemma lowL1 : lowL.getD 1 (0, 0) = firstB := by decide +kernel

lemma v_low {k : ℕ} (hk : k ≤ 4) : vZ7 k = toC (lowL.getD k (0, 0)) := by
  unfold vZ7
  split_ifs <;> first | omega | rfl

lemma v0_eq : vZ7 0 = toC (xc, 0) := by rw [v_low (by norm_num), lowL0]

lemma v1_eq : vZ7 1 = toC firstB := by rw [v_low (by norm_num), lowL1]

lemma v5_eq : vZ7 5 = eMinus := by simp [vZ7]
lemma v6_eq : vZ7 6 = ePlus := by simp [vZ7]

lemma v_up {k : ℕ} (hk : 7 ≤ k) : vZ7 k = toC (upL.getD (k - 7) (0, 0)) := by
  unfold vZ7
  split_ifs <;> first | omega | rfl

lemma ePlus_mem_disc : ePlus ∈ closedBall x₀ (ρ : ℝ) := by
  rw [mem_closedBall, dist_eq_norm, ePlus]
  simp only [add_sub_cancel_left, norm_mul, dir_norm, mul_one]
  rw [show ((ρ : ℚ) : ℂ) = (((ρ : ℚ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num [ρ])]

lemma eMinus_mem_disc : eMinus ∈ closedBall x₀ (ρ : ℝ) := by
  rw [mem_closedBall, dist_eq_norm, eMinus]
  simp only [sub_sub_cancel_left, norm_neg, norm_mul, dir_norm, mul_one]
  rw [show ((ρ : ℚ) : ℂ) = (((ρ : ℚ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num [ρ])]

lemma chk_low_im : ∀ p ∈ lowL.tail, 0 < p.2 := by decide +kernel
lemma chk_up_im : ∀ p ∈ upL, 0 < p.2 := by decide +kernel
lemma chk_low_re : ∀ p ∈ lowL, 0 ≤ p.1 := by decide +kernel
lemma chk_up_re : ∀ p ∈ upL, 0 ≤ p.1 := by decide +kernel
lemma upL_len : upL.length = 17 := by decide +kernel
lemma lowL_len : lowL.length = 5 := by decide +kernel
lemma upPts_len : upPts.length = 16 := by decide +kernel

lemma getD_mem {L : List (ℚ × ℚ)} {i : ℕ} (hi : i < L.length) : L.getD i (0, 0) ∈ L := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

lemma v_im_pos {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 23) : 0 < (vZ7 k).im := by
  rcases le_or_gt k 4 with hk | hk
  · rw [v_low hk]
    have : lowL.getD k (0, 0) ∈ lowL.tail := by
      have e : lowL.getD k (0, 0) = lowL.tail.getD (k - 1) (0, 0) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        cases hL : lowL with
        | nil => simp [lowL] at hL
        | cons x xs => simp
      rw [e]
      exact getD_mem (L := lowL.tail) (i := k - 1) (by rw [List.length_tail, lowL_len]; omega)
    have := chk_low_im _ this
    simp only [toC]; exact_mod_cast this
  · rcases Nat.lt_or_ge k 7 with hk7 | hk7
    · interval_cases k
      · rw [v5_eq]; exact Z7_disc_upper eMinus_mem_disc
      · rw [v6_eq]; exact Z7_disc_upper ePlus_mem_disc
    · rw [v_up hk7]
      have := chk_up_im _ (getD_mem (L := upL) (i := k - 7) (by rw [upL_len]; omega))
      simp only [toC]; exact_mod_cast this

lemma ePlus_re : 0 ≤ ePlus.re := by
  have := ge_of_loGe mem_ePlusB.1 (by decide +kernel : ePlusB.re.loGe 0 = true)
  simpa using this

lemma eMinus_re : 0 ≤ eMinus.re := by
  have := ge_of_loGe mem_eMinusB.1 (by decide +kernel : eMinusB.re.loGe 0 = true)
  simpa using this

lemma v_re_nonneg {k : ℕ} (h2 : k ≤ 23) : 0 ≤ (vZ7 k).re := by
  rcases le_or_gt k 4 with hk | hk
  · rw [v_low hk]
    have := chk_low_re _ (getD_mem (L := lowL) (i := k) (by rw [lowL_len]; omega))
    simp only [toC]; exact_mod_cast this
  · rcases Nat.lt_or_ge k 7 with hk7 | hk7
    · interval_cases k
      · rw [v5_eq]; exact eMinus_re
      · rw [v6_eq]; exact ePlus_re
    · rw [v_up hk7]
      have := chk_up_re _ (getD_mem (L := upL) (i := k - 7) (by rw [upL_len]; omega))
      simp only [toC]; exact_mod_cast this

lemma upL_last : upL.getD 16 (0, 0) = xtop := by decide +kernel

lemma v23_eq : vZ7 23 = toC xtop := by rw [v_up (by norm_num)]; exact congrArg toC upL_last

/-! ## The far segments -/

lemma far_of_T0 {z : ℂ} (h : (f z).re ≤ T0) : (phaseZ z).re ≤ (phaseZ x₀).re - ηfarD := by
  rw [phaseZ_eq, phaseZ_eq]
  have := S2_le_ReOmega h
  unfold ηfarD; change (f z).re ≤ Ω.re - (ηfar - 1 / 10 ^ 5); linarith

lemma seg_far {k : ℕ} (hk : k < 23) (h1 : 1 ≤ k) (hne : k ≠ 5) {z : ℂ}
    (hz : z ∈ segment ℝ (vZ7 k) (vZ7 (k + 1))) :
    (f z).re ≤ T0 ∧ ∀ a ∈ facZ7, ((amin : ℚ) : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax := by
  rcases le_or_gt k 3 with hk3 | hk3
  · -- lower polyline, segment index `3 - k` (reversed)
    have hon : onPoly dnStart dnPts z := by
      refine onPoly_of_getD dnStart dnPts (3 - k) (by simp [dnPts]; omega) ?_
      rw [segment_symm]
      rw [v_low (by omega), v_low (by omega)] at hz
      interval_cases k <;> exact hz
    exact ⟨S2_dn z hon, (S4_dn z hon).1⟩
  · rcases Nat.lt_or_ge k 7 with hk7 | hk7
    · interval_cases k
      · rw [v_low (by norm_num), v5_eq] at hz
        rw [segment_symm] at hz
        have hz' : z ∈ segment ℝ eMinus (toC dnStart) := by
          have : lowL.getD 4 (0, 0) = dnStart := rfl
          rwa [this] at hz
        exact ⟨S2_conn_dn z hz', S4_conn_dn z hz'⟩
      · exact absurd rfl hne
      · rw [v6_eq, v_up (by norm_num)] at hz
        have hz' : z ∈ segment ℝ ePlus (toC upStart) := by
          have : upL.getD (7 - 7) (0, 0) = upStart := rfl
          rwa [this] at hz
        exact ⟨S2_conn_up z hz', S4_conn_up z hz'⟩
    · have hon : onPoly upStart upPts z := by
        refine onPoly_of_getD upStart upPts (k - 7) (by rw [upPts_len]; omega) ?_
        rw [v_up hk7, v_up (by omega)] at hz
        have e : k + 1 - 7 = (k - 7) + 1 := by omega
        rw [e] at hz
        simpa [upL] using hz
      exact ⟨S2_up z hon, (S4_up z hon).1⟩

/-! ## The instance -/

/-- **The certified saddle data for Z7.** -/
noncomputable def Z7_saddleData : SaddleData where
  x₀ := x₀
  d := dir
  K := Kx
  M := Mcert
  ρ := ((ρ : ℚ) : ℝ)
  v := vZ7
  Kd := 5
  Ktop := 23
  a := 1 / 100
  η := etaS
  ηfar := ηfarD
  rate := q0 - 3 * π
  Y₀ := 0
  δ₀ := δ0
  a_pos := by norm_num
  η_pos := etaS_pos
  η_le := by unfold etaS; linarith
  ηfar_pos := ηfarD_pos
  rate_pos := by linarith [q0_sub_three_pi]
  δ₀_pos := by norm_num [δ0]
  S0 := saddle_Psi1Z
  sin_ne := by
    rw [phase_saddle]; exact (lt_trans Z7_sinqtheta_le (by norm_num)).ne
  ReΩ_le := by
    rw [phase_saddle]; linarith [Z7_ReOmega_le]
  K_pos := Kx_pos
  d_norm := dir_norm
  S1_dir := saddle_Psi2Z_dir
  ρ_pos := by norm_num [ρ]
  S1_M := fun z hz => Psi3Z_bound hz
  S1_ρ := rho_M_Kx
  S1'_disc := by linarith [Z7_S1']
  Kd_pos := by norm_num
  Kd_lt := by norm_num
  v_disc_lo := by rw [v5_eq, eMinus]; push_cast; ring
  v_disc_hi := by rw [v6_eq, ePlus]; push_cast; ring
  v0_im := by rw [v0_eq]; simp [toC]
  δ₀_le := by rw [v0_eq]; simp [toC, xc, δ0]; norm_num
  v0_lt := by rw [v0_eq]; simp [toC, xc]; norm_num
  re_nonneg := fun k hk => v_re_nonneg hk
  top_re_pos := by rw [v23_eq]; simp [toC, xtop]
  path_im := by
    intro k hk t ht
    have h1 : 0 ≤ (vZ7 k).im := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [v0_eq]; simp [toC]
      · exact (v_im_pos hk0 (by omega)).le
    have h2 : 0 < (vZ7 (k + 1)).im := v_im_pos (by omega) (by omega)
    have e : (vZ7 k + t * (vZ7 (k + 1) - vZ7 k)).im
        = (1 - t) * (vZ7 k).im + t * (vZ7 (k + 1)).im := by simp; ring
    rw [e]
    have := ht.1; have := ht.2
    have : 0 ≤ (1 - t) * (vZ7 k).im := mul_nonneg (by linarith) h1
    have : 0 < t * (vZ7 (k + 1)).im := mul_pos ht.1 h2
    linarith
  S4_disc := by
    intro s hs
    apply sector_disc
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, dir_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact hs
  S2 := by
    intro k hk h1 hne t ht
    have hz := seg_param ht (z := vZ7 k + t * (vZ7 (k + 1) - vZ7 k)) rfl
    obtain ⟨hf, hs⟩ := seg_far hk h1 hne hz
    exact ⟨far_of_T0 hf, sectorAt_of hs⟩
  S2_first := by
    intro e he t ht
    set z := (vZ7 0 + e) + t * (vZ7 1 - (vZ7 0 + e))
    set z' := vZ7 0 + t * (vZ7 1 - vZ7 0)
    have hz' : z' ∈ segment ℝ (toC firstA) (toC firstB) := by
      rw [← v1_eq, show toC firstA = vZ7 0 from by rw [v0_eq]; rfl]
      exact seg_param' ht rfl
    have hzz : ‖z - z'‖ ≤ δ0 := by
      have : z - z' = ((e * (1 - t) : ℝ) : ℂ) := by simp only [z, z']; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have h1 : |e| ≤ δ0 := abs_le.2 he
      have h2 : |1 - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      calc |e| * |1 - t| ≤ δ0 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num [δ0])
        _ = δ0 := mul_one _
    -- `z'` lies on the lower polyline (its last segment)
    have hon : onPoly dnStart dnPts z' := by
      refine onPoly_of_getD dnStart dnPts 3 (by simp [dnPts]) ?_
      rw [segment_symm]
      have := seg_param' ht (p := vZ7 0) (q := vZ7 1) (z := z') rfl
      rw [v0_eq, v1_eq] at this
      have e1 : dnPts.getD 3 (0, 0) = (xc, 0) := by decide +kernel
      have e2 : (dnStart :: dnPts).getD 3 (0, 0) = firstB := by decide +kernel
      rw [e1, e2]
      exact this
    have hb := first_bound hz' hzz
    have hT := S2_dn z' hon
    refine ⟨?_, sectorAt_of (first_sector hz' hzz)⟩
    rw [phaseZ_eq, phaseZ_eq]
    have := T0_le_ReOmega
    unfold ηfarD; change (f z).re ≤ Ω.re - (ηfar - 1 / 10 ^ 5)
    linarith
  S3 := by
    intro y hy
    have e : vZ7 23 + y * I = ⟨X0, xtop.2 + y⟩ := by
      rw [v23_eq]; apply Complex.ext <;> simp [toC, X0]
    rw [e, phaseZ_eq, phaseZ_eq]
    refine ⟨?_, sectorAt_of (S4_ray _ (by linarith))⟩
    have h0 := S2_up _ xtop_on_up
    have e0 : toC xtop = ⟨X0, xtop.2⟩ := rfl
    rw [e0] at h0
    have hd := S3_h_decreasing (y1 := xtop.2) (y2 := xtop.2 + y) le_rfl (by linarith)
    have := T0_le_ReOmega
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ y - 0)]
    unfold ηfarD; change (f _).re ≤ Ω.re - (ηfar - 1 / 10 ^ 5) - (q0 - 3 * π) * (y - 0)
    have : (f ⟨X0, xtop.2 + y⟩).re ≤ T0 - (q0 - 3 * π) * y := by
      have : (xtop.2 : ℝ) + y - xtop.2 = y := by ring
      rw [this] at hd; linarith
    linarith

end ZetaIrr.Z7.Interval
