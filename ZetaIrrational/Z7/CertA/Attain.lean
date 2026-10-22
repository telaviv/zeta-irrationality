/-
# `eStarInt x` is exactly `max_{0 ≤ y ≤ x} gfun(x, y)`, and `e*` is constant on event intervals (Z7)

* `eStarInt_realized`: for `x ≥ 1`, `eStarInt x = gfun x y` for some `0 ≤ y ≤ x`;
* `eStar_isGreatest`: for `x ≥ 1`, `eStar x` is the greatest element of
  `{gfun x y - G⌊x⌋ | 0 ≤ y ≤ x}` (`e*(x) = max(0, sup_y bracket) - G⌊x⌋`; the sup is attained,
  and `0 = gfun x 0` because no block contains `0`);
* `eStar_eq_mid`: for consecutive events `a < b` and `x ∈ (a, b)`, `e*(x) = e*((a+b)/2)`.
-/
import ZetaIrrational.Z7.CertA.Step

namespace ZetaIrr.Z7.CertA

lemma foldl_inv {α : Type*} (step : ℤ → α → ℤ) (P : ℤ → Prop)
    (h : ∀ acc a, P acc → P (step acc a)) :
    ∀ (l : List α) (init : ℤ), P init → P (l.foldl step init)
  | [], _, hi => hi
  | a :: l, init, hi => foldl_inv step P h l _ (h init a hi)

/-- `v` is realised: `v = gfun x y` for some `0 ≤ y ≤ x`. -/
def Realized (x : ℚ) (v : ℤ) : Prop := ∃ y, 0 ≤ y ∧ y ≤ x ∧ gfun x y = v

lemma valid_spec (P Q M k ri : ℤ) (hQ : 0 < Q) (hMdef : M = 240 * Q) (hM : ri < M)
    (right : Bool) (hv : Valid (P / Q) (240 * (P % Q)) ri k right) :
    0 ≤ k ∧ (if right then k * M + ri < 240 * P else k * M + ri ≤ 240 * P) := by
  have hPQ := Int.emod_add_ediv_mul P Q
  have hr0 : 0 ≤ P % Q := Int.emod_nonneg _ (by omega)
  have hrQ : P % Q < Q := Int.emod_lt_of_pos _ hQ
  have hX : 240 * P = (P / Q) * M + 240 * (P % Q) := by subst hMdef; linarith
  have hMpos : 0 < M := by omega
  obtain ⟨hk0, hkm⟩ := hv
  refine ⟨hk0, ?_⟩
  unfold kmax at hkm
  rcases lt_or_ge k (P / Q) with hlt | hge
  · have : (k + 1) * M ≤ (P / Q) * M := mul_le_mul_of_nonneg_right (by omega) (by omega)
    cases right <;> simp <;> nlinarith
  · have heq : k = P / Q := by split_ifs at hkm <;> omega
    have hc : if right then ri < 240 * (P % Q) else ri ≤ 240 * (P % Q) := by
      by_contra hc; rw [if_neg hc] at hkm; omega
    subst heq
    cases right <;> simp at hc ⊢ <;> omega

lemma floor_div_bounds (N M : ℤ) (hM : 0 < M) :
    ⌊(N : ℚ) / M⌋ * M ≤ N ∧ N < (⌊(N : ℚ) / M⌋ + 1) * M := by
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  have h1 := Int.floor_le ((N : ℚ) / M)
  have h2 := Int.lt_floor_add_one ((N : ℚ) / M)
  rw [le_div_iff₀ hM'] at h1
  rw [div_lt_iff₀ hM'] at h2
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- Every valid candidate value is realised. -/
lemma realized_pt (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 240 * x.den)
    (right : Bool) (hv : Valid (x.num / x.den) (240 * (x.num % x.den)) ri k right) :
    Realized x (phiAt (preOf x.num x.den) (qrOf x.num x.den (-220)) (qrOf x.num x.den 240)
      (qrOf x.num x.den 460) k ri right) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨hk0, hle⟩ := valid_spec x.num x.den (240 * x.den) k ri hQ rfl hM right hv
  set M : ℤ := 240 * (x.den : ℤ) with hMdef
  have hMpos : 0 < M := by omega
  have hMq : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hMpos
  have hxs : x = ((240 * x.num : ℤ) : ℚ) / (M : ℚ) := x_eq_scaled x
  have hc : candY x k ri = ((k * M + ri : ℤ) : ℚ) / (M : ℚ) := candY_eq x k ri
  have hc0 : 0 ≤ candY x k ri := by
    rw [hc]; apply div_nonneg _ hMq.le
    have : 0 ≤ k * M + ri := by nlinarith
    exact_mod_cast this
  cases right
  · simp only [Bool.false_eq_true, if_false] at hle
    refine ⟨candY x k ri, hc0, ?_, ?_⟩
    · rw [hc]
      conv_rhs => rw [hxs]
      apply div_le_div_of_nonneg_right _ hMq.le
      exact_mod_cast hle
    · rw [gfun_eq_Phi, phiAt_eq_Phi x k ri h0 hM false]
      simp
  · simp only [if_true] at hle
    set y := candY x k ri + 1 / (2 * (M : ℚ))
    have hsub : ∀ o : ℤ, y - offVal x o =
        (((2 * ((k - (qrOf x.num x.den o).1) * M + ri - (qrOf x.num x.den o).2) + 1 : ℤ)) : ℚ)
          / ((2 * M : ℤ) : ℚ) := by
      intro o
      have := candY_sub x k ri o
      rw [← hMdef] at this
      simp only [y]
      rw [show candY x k ri + 1 / (2 * (M : ℚ)) - offVal x o =
        (candY x k ri - offVal x o) + 1 / (2 * (M : ℚ)) by ring, this]
      field_simp
      push_cast
      ring
    have hfl : ∀ o : ℤ, ⌊y - offVal x o⌋ = ⌊candY x k ri - offVal x o⌋ := by
      intro o
      rw [hsub, candY_sub]
      set N := (k - (qrOf x.num x.den o).1) * M + ri - (qrOf x.num x.den o).2
      obtain ⟨b1, b2⟩ := floor_div_bounds N M hMpos
      apply floor_div_eq _ _ _ (by omega) <;> nlinarith
    have hcl : ∀ o : ℤ, ⌈y - offVal x o⌉ = ⌊candY x k ri - offVal x o⌋ + 1 := by
      intro o
      rw [hsub, candY_sub]
      set N := (k - (qrOf x.num x.den o).1) * M + ri - (qrOf x.num x.den o).2
      obtain ⟨b1, b2⟩ := floor_div_bounds N M hMpos
      apply ceil_div_eq _ _ _ (by omega) <;> nlinarith
    refine ⟨y, ?_, ?_, ?_⟩
    · simp only [y]; positivity
    · have : y = (((2 * (k * M + ri) + 1 : ℤ)) : ℚ) / ((2 * M : ℤ) : ℚ) := by
        simp only [y]; rw [hc]; field_simp; push_cast; ring
      rw [this]
      conv_rhs => rw [hxs, show ((240 * x.num : ℤ) : ℚ) / (M : ℚ) =
        ((480 * x.num : ℤ) : ℚ) / ((2 * M : ℤ) : ℚ) by push_cast; field_simp; ring]
      apply div_le_div_of_nonneg_right _ (by push_cast; positivity)
      exact_mod_cast (by omega : 2 * (k * M + ri) + 1 ≤ 480 * x.num)
    · rw [gfun_eq_Phi, phiAt_eq_Phi x k ri h0 hM true]
      simp only [if_true]
      congr 1
      · funext o; exact hfl o
      · funext o; exact hcl o

/-- `0` is realised (at `y = 0`, which lies in no block). -/
lemma realized_zero (x : ℚ) (hx : 0 < x) : Realized x 0 := by
  refine ⟨0, le_rfl, hx.le, ?_⟩
  have hS : Sfun x 0 = 0 := by
    unfold Sfun
    apply List.sum_eq_zero
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have h1 := (blocks_bounds b hb).1
    have : 0 < dlt b.1 * x := by
      unfold dlt
      have : (1 : ℚ) ≤ b.1 := by exact_mod_cast h1
      positivity
    rw [if_neg (by intro h; linarith [h.1])]
  unfold gfun; rw [if_pos hS]

lemma num_div_den_pos (x : ℚ) (hx : 1 ≤ x) : 0 < x.num / (x.den : ℤ) := by
  have hd : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
  have hle : (x.den : ℤ) ≤ x.num := by
    have h := x.num_div_den
    have hdq : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
    have : (x.den : ℚ) ≤ x.num := by
      rw [← h] at hx
      rwa [le_div_iff₀ hdq, one_mul] at hx
    exact_mod_cast this
  exact lt_of_lt_of_le one_pos (Int.le_ediv_of_mul_le hd (by simpa using hle))

/-- If `has1`, the value `T + 4 - c` is realised (at the first valid `k ≥ 1` of the witness block). -/
lemma realized_has1 (x : ℚ) (ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 240 * x.den) (right : Bool)
    (h : has1 (preOf x.num x.den) (x.num / x.den) (240 * (x.num % x.den)) ri right = true) :
    Realized x (Tval (preOf x.num x.den) ri right + 4 -
      cval (qrOf x.num x.den (-220)) (qrOf x.num x.den 240) (qrOf x.num x.den 460) ri right) := by
  unfold has1 at h
  rw [List.any_eq_true] at h
  obtain ⟨e, he, hc⟩ := h
  simp only [decide_eq_true_eq] at hc
  obtain ⟨hm, hU, hK⟩ := hc
  set k := max 1 (e.2.1.1 + (if ri < e.2.1.2 then 1 else 0)) with hk
  have hk1 : 1 ≤ k := le_max_left _ _
  have hkL : e.2.1.1 + (if ri < e.2.1.2 then 1 else 0) ≤ k := le_max_right _ _
  have hv : Valid (x.num / x.den) (240 * (x.num % x.den)) ri k right := ⟨by omega, hK⟩
  have hpre := preOf_ok x.num x.den
  -- the witness block contains `k`, so `S(k) ≥ e.1 > 0`
  have hS : ((preOf x.num x.den).map fun e =>
      blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2)).sum ≠ 0 := by
    have hnn : ∀ e' ∈ preOf x.num x.den, 0 ≤ blockS e'.1 (flAt k ri e'.2.1) (clAt k ri right e'.2.2) := by
      intro e' he'
      unfold blockS; split_ifs
      · exact hpre e' he'
      · exact le_rfl
    have hge : blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2) ≤
        ((preOf x.num x.den).map fun e =>
          blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2)).sum :=
      List.single_le_sum (fun a ha => by
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 ha
        exact hnn e' he') _ (List.mem_map.2 ⟨e, he, rfl⟩)
    have heq : blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2) = e.1 := by
      unfold blockS
      rw [if_pos]
      simp only [clAt, flAt]
      constructor <;> omega
    omega
  have hval := phiAt_of_pos (preOf x.num x.den) (qrOf x.num x.den (-220)) (qrOf x.num x.den 240)
    (qrOf x.num x.den 460) k ri right hk1 hS
  rw [← hval]
  exact realized_pt x k ri h0 hM right hv

lemma realized_max {x : ℚ} {a b : ℤ} (ha : Realized x a) (hb : Realized x b) :
    Realized x (max a b) := by
  rcases max_choice a b with h | h <;> rw [h]
  · exact ha
  · exact hb

lemma realized_cand (x : ℚ) (hx : 1 ≤ x) (ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 240 * x.den)
    (right : Bool) :
    Realized x (cand (preOf x.num x.den) (qrOf x.num x.den (-220)) (qrOf x.num x.den 240)
      (qrOf x.num x.den 460) (x.num / x.den) (240 * (x.num % x.den)) ri right) := by
  unfold cand
  refine realized_max ?_ ?_
  · apply realized_pt x 0 ri h0 hM right
    refine ⟨le_rfl, ?_⟩
    have := num_div_den_pos x hx
    unfold kmax; split_ifs <;> omega
  · split_ifs with h1
    · exact realized_has1 x ri h0 hM right h1
    · exact realized_zero x (by linarith)

/-- The computed integer max is realised by some `y ∈ [0, x]`. -/
lemma eStarInt_realized (x : ℚ) (hx : 1 ≤ x) : Realized x (eStarInt x) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  unfold eStarInt
  dsimp only
  apply foldl_inv _ (Realized x)
  · intro acc o hacc
    obtain ⟨-, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
    exact realized_max hacc (realized_max (realized_cand x hx _ hr0 hrM false)
      (realized_cand x hx _ hr0 hrM true))
  · exact realized_zero x (by linarith)

/-- **`e*(x) = max_{0 ≤ y ≤ x} gfun(x, y) - G⌊x⌋`**, for `x ≥ 1`. -/
theorem eStar_isGreatest (x : ℚ) (hx : 1 ≤ x) :
    IsGreatest {v | ∃ y, 0 ≤ y ∧ y ≤ x ∧ (gfun x y : ℚ) - G * ⌊x⌋ = v} (eStar x) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy0, hyx, hy⟩ := eStarInt_realized x hx
    exact ⟨y, hy0, hyx, by rw [hy, eStar, if_pos hx]⟩
  · rintro v ⟨y, hy0, hyx, rfl⟩
    rw [eStar, if_pos hx]
    have : (gfun x y : ℚ) ≤ eStarInt x := by exact_mod_cast gfun_le_eStarInt x y hy0 hyx
    linarith

/-- **Step function.** `e*` is constant on each open event interval:
`e*(x) = e*((a+b)/2)` for consecutive events `a < b` and `a < x < b`. -/
theorem eStar_eq_mid (a b : ℚ) (hc : Consec (events 400) a b) (x : ℚ) (hax : a < x)
    (hxb : x < b) : eStar x = eStar ((a + b) / 2) := by
  have ha := (events_bounds a hc.mem_left).1
  have hab := hc.lt (events_pairwise 400)
  have hm : a < (a + b) / 2 ∧ (a + b) / 2 < b := ⟨by linarith, by linarith⟩
  have hx1 : 1 ≤ x := by linarith
  have hm1 : 1 ≤ (a + b) / 2 := by linarith
  obtain ⟨hst, hfl⟩ := sameType_of_consec a b x ((a + b) / 2) hc ⟨hax, hxb⟩ hm
  obtain ⟨hst', -⟩ := sameType_of_consec a b ((a + b) / 2) x hc hm ⟨hax, hxb⟩
  rw [eStar, eStar, if_pos hx1, if_pos hm1, hfl]
  have h1 : eStarInt x ≤ eStarInt ((a + b) / 2) := by
    obtain ⟨y, hy0, hyx, hy⟩ := eStarInt_realized x hx1
    rw [← hy]; exact gfun_le_eStarInt_of_sameType x _ hst y hy0 hyx
  have h2 : eStarInt ((a + b) / 2) ≤ eStarInt x := by
    obtain ⟨y, hy0, hyx, hy⟩ := eStarInt_realized _ hm1
    rw [← hy]; exact gfun_le_eStarInt_of_sameType _ x hst' y hy0 hyx
  rw [le_antisymm h1 h2]

end ZetaIrr.Z7.CertA
