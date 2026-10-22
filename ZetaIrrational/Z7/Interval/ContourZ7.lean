/-
# Certified contour data (S2), (S4) for instance Z7

The contour `Γ_+` (from the real point `x_c` to `+i∞`) consists of
* the lower polyline `dnPts` reversed: `x_c → … → dnStart`, then the connector `[dnStart, eMinus]`;
* the Taylor segment `x₀ + s·dir`, `|s| ≤ ρ = 1/20` (`DirectionZ7.lean`), from `eMinus` to `ePlus`;
* the connector `[ePlus, upStart]` and the upper polyline `upStart → … → xtop`;
* the vertical ray `xtop + i y`, `y ≥ 0` (`RayZ7.lean`).

This file assembles the kernel checks of `UpChunk1..2.lean`, `DnChunk.lean` and `ConnZ7.lean`
(all `decide +kernel`) into statements about every point of the polylines, the connectors and the
Taylor disc (`f z = Ψ z - 3πi z`, `h = Re f`, `T0 = -10.1367 = -10.1167486 - ηfar`,
`ηfar = 0.0199514`, so `h ≤ T0` gives `h ≤ Re Ω - ηfar` by `Z7_ReOmega_ge`):
* **(S2)** `S2_up`, `S2_dn`, `S2_conn_up`, `S2_conn_dn`: `h ≤ T0` off the Taylor segment;
  `S2_le_ReOmega` converts to `h ≤ Re Ω - ηfar`.
* **(S4)** `S4_up`, `S4_dn`, `S4_disc`, `S4_conn_up`, `S4_conn_dn`: `|α_i| ≥ 1/100` and
  `|arg α_i| ≤ 2.76` (`π - 2.76 > 0.38`) for every factor; `Re(2z+1) > 0` (e-factor).

The top ray (S3) is in `RayZ7.lean`; the remaining path conditions (the polylines lie in `Im z > 0`
except at `x_c`, `0 < x_c < 11/12`, and the bound on the first segment, which contains (S5)) are
checked in `SaddleDataZ7.lean`.
-/
import ZetaIrrational.Z7.Interval.DirectionZ7
import ZetaIrrational.Z7.Interval.OmegaZ7
import ZetaIrrational.Z7.Interval.UpChunk1
import ZetaIrrational.Z7.Interval.UpChunk2
import ZetaIrrational.Z7.Interval.DnChunk
import ZetaIrrational.Z7.Interval.RayZ7
import ZetaIrrational.Z7.Interval.ConnZ7

namespace ZetaIrr.Z7.Interval

open Complex Metric ZetaIrr.Interval ZetaIrr.Interval.IV ZetaIrr.Fam.Interval Real

/-- The far margin: `T0 = -10.1167486 - ηfar`. -/
def ηfar : ℚ := 199514 / 10 ^ 7

lemma onPoly_last (a : ℚ × ℚ) (pts : List (ℚ × ℚ)) (h : pts ≠ []) :
    onPoly a pts (toC (pts.getLast h)) := by
  induction pts generalizing a with
  | nil => exact absurd rfl h
  | cons b rest ih =>
    cases rest with
    | nil => left; simpa using right_mem_segment ℝ (toC a) (toC b)
    | cons c rest' => right; simpa using ih b (by simp)

/-! ## Assembling the chunks -/

lemma chk_up : polyChk 3 40 16 facZ7 T0 upStart upPts = true := by
  have e : polyChk 3 40 16 facZ7 T0 upStart upPts =
      (polyChk 3 40 16 facZ7 T0 upStart upC1 && polyChk 3 40 16 facZ7 T0 upA2 upC2) := by
    simp only [upPts, polyChk_append]; rfl
  rw [e, chk_up1, chk_up2]; rfl

lemma chk_sec_up : polySectorQ 40 16 amin Amax facZ7 upStart upPts = true := by
  have e : polySectorQ 40 16 amin Amax facZ7 upStart upPts =
      (polySectorQ 40 16 amin Amax facZ7 upStart upC1 &&
        polySectorQ 40 16 amin Amax facZ7 upA2 upC2) := by
    simp only [upPts, polySectorQ_append]; rfl
  rw [e, chk_sec_up1, chk_sec_up2]; rfl

/-! ## (S2) far part -/

theorem S2_up : ∀ z, onPoly upStart upPts z → (f z).re ≤ T0 :=
  poly_bound 3 40 16 facZ7 T0 upStart upPts chk_up

theorem S2_dn : ∀ z, onPoly dnStart dnPts z → (f z).re ≤ T0 :=
  poly_bound 3 40 16 facZ7 T0 dnStart dnPts chk_dn

lemma Dc_nonneg : (0 : ℝ) ≤ (Dc : ℝ) := by norm_num [Dc]

theorem S2_conn_up : ∀ z ∈ segment ℝ ePlus (toC upStart), (f z).re ≤ T0 := by
  intro z hz
  have hsub := (convex_closedBall (toC upStart) (Dc : ℝ)).segment_subset ePlus_near
    (mem_closedBall_self Dc_nonneg)
  exact ball_bound 3 40 16 facZ7 T0 upStart Dc chk_cup z (hsub hz)

theorem S2_conn_dn : ∀ z ∈ segment ℝ eMinus (toC dnStart), (f z).re ≤ T0 := by
  intro z hz
  have hsub := (convex_closedBall (toC dnStart) (Dc : ℝ)).segment_subset eMinus_near
    (mem_closedBall_self Dc_nonneg)
  exact ball_bound 3 40 16 facZ7 T0 dnStart Dc chk_cdn z (hsub hz)

/-- `T0 = -10.1167486 - ηfar ≤ Re Ω - ηfar`. -/
theorem T0_le_ReOmega : (T0 : ℝ) ≤ Ω.re - ηfar := by
  have := Z7_ReOmega_ge
  have e : (T0 : ℝ) = -101167486 / 10 ^ 7 - ηfar := by norm_num [T0, ηfar]
  rw [e]; linarith

theorem S2_le_ReOmega {z : ℂ} (h : (f z).re ≤ T0) : (f z).re ≤ Ω.re - ηfar :=
  h.trans T0_le_ReOmega

/-! ## (S1′) upper half plane, `x_c` -/

lemma upPts_last : upPts.getLast (by simp [upPts, upC2]) = xtop := by decide +kernel

theorem xtop_on_up : onPoly upStart upPts (toC xtop) := by
  have := onPoly_last upStart upPts (by simp [upPts, upC2])
  rwa [upPts_last] at this

/-! ## (S4) sector bounds -/

lemma chk_sec_disc : sectorQ 40 16 amin Amax facZ7 (CB.ofQRad cRe cIm (ρ + R0)) = true :=
  chk_sec_disc_lit

lemma chk_sec_cup' : sectorQ 40 16 amin Amax facZ7 (CB.ofQRad upStart.1 upStart.2 Dc) = true :=
  chk_sec_cup

lemma chk_sec_cdn' : sectorQ 40 16 amin Amax facZ7 (CB.ofQRad dnStart.1 dnStart.2 Dc) = true :=
  chk_sec_cdn

theorem S4_up : ∀ z, onPoly upStart upPts z →
    (∀ a ∈ facZ7, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax) ∧ -1 / 2 < z.re :=
  poly_sectorQ 40 16 amin Amax facZ7 upStart upPts chk_sec_up

theorem S4_dn : ∀ z, onPoly dnStart dnPts z →
    (∀ a ∈ facZ7, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax) ∧ -1 / 2 < z.re :=
  poly_sectorQ 40 16 amin Amax facZ7 dnStart dnPts chk_sec_dn

/-- On the Taylor disc `closedBall x₀ ρ` (which contains the Taylor segment). -/
theorem S4_disc : ∀ z ∈ closedBall x₀ (ρ : ℝ),
    ∀ a ∈ facZ7, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax := by
  intro z hz
  have h := norm_sub_c0_le hz
  have hm : (CB.ofQRad cRe cIm (ρ + R0)).mem z := CB.mem_ofQRad (by simpa [c0] using h)
  exact sector_of_sectorQ 40 16 amin Amax hm chk_sec_disc

theorem S4_conn_up : ∀ z ∈ segment ℝ ePlus (toC upStart),
    ∀ a ∈ facZ7, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax := by
  intro z hz
  have hsub := (convex_closedBall (toC upStart) (Dc : ℝ)).segment_subset ePlus_near
    (mem_closedBall_self Dc_nonneg)
  have h := hsub hz
  rw [mem_closedBall, dist_eq_norm] at h
  exact sector_of_sectorQ 40 16 amin Amax (CB.mem_ofQRad (by simpa [toC] using h)) chk_sec_cup'

theorem S4_conn_dn : ∀ z ∈ segment ℝ eMinus (toC dnStart),
    ∀ a ∈ facZ7, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax := by
  intro z hz
  have hsub := (convex_closedBall (toC dnStart) (Dc : ℝ)).segment_subset eMinus_near
    (mem_closedBall_self Dc_nonneg)
  have h := hsub hz
  rw [mem_closedBall, dist_eq_norm] at h
  exact sector_of_sectorQ 40 16 amin Amax (CB.mem_ofQRad (by simpa [toC] using h)) chk_sec_cdn'

/-! ## (S2) on the top ray -/

end ZetaIrr.Z7.Interval
