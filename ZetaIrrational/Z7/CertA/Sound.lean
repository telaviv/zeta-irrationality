/-
# The A-certificate for instance Z7: soundness of the computable `e*`

`PROOF_ZETA.md` §5.1. We prove that the computable `eStarInt x` of `Z7/CertA/Defs.lean` bounds
`gfun x y` for every `0 ≤ y ≤ x` (`x ≥ 1`): `gfun_le_eStarInt`. The scaling is `M = 240 Q`
(`x = P/Q`), so that every breakpoint `σ/240 · x + j` lies on the grid `(1/M) ℤ`.

Route: `gfun` equals `Phi` of the floor/ceiling data (`gfun_eq_Phi`); the largest breakpoint
`b ≤ y` is a grid point `k + r_i/M` with `r_i` the residue of some offset, and `y` has the same
floor data as `b` (if `y = b`) or as the right limit `b + 0`; `Phi` there is `phiAt … k r_i`,
which is at most `max 0 (cand … r_i)` for every valid `k` (`phiAt_le_cand`).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.CertA.Defs

namespace ZetaIrr.Z7.CertA

open Finset

/-! ## Floor/ceiling bookkeeping -/

lemma floor_eq_ceil_iff_fract (z : ℚ) : ⌊z⌋ = ⌈z⌉ ↔ Int.fract z = 0 := by
  rw [Int.fract_eq_zero_iff]
  constructor
  · intro h
    have h1 := Int.floor_le z
    have h2 := Int.le_ceil z
    rw [← h] at h2
    exact ⟨⌊z⌋, le_antisymm h1 h2⟩
  · rintro ⟨n, rfl⟩
    simp

lemma floor_eq_ceil_iff_fract_neg (z : ℚ) : ⌊z⌋ = ⌈z⌉ ↔ Int.fract (-z) = 0 := by
  rw [← floor_eq_ceil_iff_fract, Int.floor_neg, Int.ceil_neg]
  omega

lemma offVal_aOff (x : ℚ) (d : ℕ) : offVal x (aOff d) = dlt d * x := by
  simp only [offVal, aOff, dlt]; push_cast; ring

lemma offVal_bOff (x : ℚ) (d : ℕ) : offVal x (bOff d) = (1 - dlt d) * x := by
  simp only [offVal, bOff, dlt]; push_cast; ring

lemma offVal_zero (x : ℚ) : offVal x 0 = 0 := by simp [offVal]

lemma offVal_n (x : ℚ) : offVal x (-220) = -(rr * x) := by simp only [offVal, rr]; push_cast; ring

lemma offVal_240 (x : ℚ) : offVal x 240 = x := by simp only [offVal]; push_cast; ring

lemma offVal_460 (x : ℚ) : offVal x 460 = (1 + rr) * x := by simp only [offVal, rr]; push_cast; ring

/-- One block: `blockS` of the floor data is `m [in block]`. -/
lemma blockS_eq (m d : ℕ) (x y : ℚ) :
    blockS m ⌊y - offVal x (aOff d)⌋ ⌈y - offVal x (bOff d)⌉ =
      ((if dlt d * x ≤ y ∧ y ≤ (1 - dlt d) * x then m else 0 : ℕ) : ℤ) := by
  unfold blockS
  rw [offVal_aOff, offVal_bOff]
  have h1 : 0 ≤ ⌊y - dlt d * x⌋ ↔ dlt d * x ≤ y := by rw [Int.floor_nonneg, sub_nonneg]
  have h2 : ⌈y - (1 - dlt d) * x⌉ ≤ 0 ↔ y ≤ (1 - dlt d) * x := by
    rw [Int.ceil_le]; simp
  simp only [h1, h2]
  split_ifs <;> simp

/-- One block: `blockP` of the floor data is `m P_j`. -/
lemma blockP_eq (m d : ℕ) (x y : ℚ) :
    blockP m ⌊y - offVal x (aOff d)⌋ ⌈y - offVal x (aOff d)⌉ ⌊y - offVal x (bOff d)⌋
        ⌈y - offVal x (bOff d)⌉ = m * Pfun d x y := by
  unfold blockP Pfun
  rw [offVal_aOff, offVal_bOff]
  set a := dlt d * x
  set b := (1 - dlt d) * x
  have h1 : 0 ≤ ⌊y - a⌋ ↔ a ≤ y := by rw [Int.floor_nonneg, sub_nonneg]
  have h2 : ⌈y - b⌉ ≤ 0 ↔ y ≤ b := by
    rw [Int.ceil_le]; simp
  have h3 : ⌊y - a⌋ < 0 ↔ y < a := by
    rw [Int.floor_lt]; simp
  have h4 : ⌊b - y⌋ = -⌈y - b⌉ := by rw [show b - y = -(y - b) by ring, Int.floor_neg]
  have h5 : ⌊a - y⌋ = -⌈y - a⌉ := by rw [show a - y = -(y - a) by ring, Int.floor_neg]
  have h6 : ⌊y - a⌋ = ⌈y - a⌉ ↔ Int.fract (a - y) = 0 := by
    rw [floor_eq_ceil_iff_fract_neg, neg_sub]
  have h7 : ⌊y - b⌋ = ⌈y - b⌉ ↔ Int.fract (y - b) = 0 := floor_eq_ceil_iff_fract _
  simp only [h1, h2, h3, h4, h5, h6, h7]
  split_ifs <;> ring

lemma Sfun_cast (x y : ℚ) :
    (Sfun x y : ℤ) = (blocks.map fun b =>
      ((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0 : ℕ) : ℤ)).sum := by
  unfold Sfun
  rw [Nat.cast_list_sum, List.map_map]
  rfl

lemma cfun_eq (x y : ℚ) :
    cfun x y = 5 * (⌊y - offVal x (-220)⌋ - ⌊y - offVal x 0⌋) +
      5 * (⌈y - offVal x 240⌉ - ⌈y - offVal x 460⌉) := by
  simp only [cfun, offVal_n, offVal_zero, offVal_240, offVal_460, sub_neg_eq_add, sub_zero]

/-- **The floor-data form of `gfun`.** -/
lemma gfun_eq_Phi (x y : ℚ) :
    gfun x y = Phi (fun o => ⌊y - offVal x o⌋) (fun o => ⌈y - offVal x o⌉) := by
  have hS : (blocks.map fun b => blockS b.2 ⌊y - offVal x (aOff b.1)⌋ ⌈y - offVal x (bOff b.1)⌉).sum
      = (Sfun x y : ℤ) := by
    rw [Sfun_cast]
    congr 1
    apply List.map_congr_left
    intro b _
    exact blockS_eq b.2 b.1 x y
  have hP : (blocks.map fun b => blockP b.2 ⌊y - offVal x (aOff b.1)⌋ ⌈y - offVal x (aOff b.1)⌉
      ⌊y - offVal x (bOff b.1)⌋ ⌈y - offVal x (bOff b.1)⌉).sum = Ptot x y := by
    unfold Ptot
    congr 1
    apply List.map_congr_left
    intro b _
    exact blockP_eq b.2 b.1 x y
  have h1 : (1 ≤ ⌊y - offVal x 0⌋) ↔ (1 ≤ y) := by
    rw [offVal_zero, sub_zero, Int.le_floor]; simp
  unfold Phi gfun bracket
  simp only
  rw [hS, hP, ← cfun_eq]
  simp only [h1, Nat.cast_eq_zero]

/-! ## Integer scaling -/

lemma floor_div_eq (N M a : ℤ) (hM : 0 < M) (h1 : a * M ≤ N) (h2 : N < (a + 1) * M) :
    ⌊(N : ℚ) / M⌋ = a := by
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  rw [Int.floor_eq_iff, le_div_iff₀ hM', div_lt_iff₀ hM']
  constructor <;> exact_mod_cast (by linarith)

lemma ceil_div_eq (N M a : ℤ) (hM : 0 < M) (h1 : (a - 1) * M < N) (h2 : N ≤ a * M) :
    ⌈(N : ℚ) / M⌉ = a := by
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  rw [Int.ceil_eq_iff, lt_div_iff₀ hM', div_le_iff₀ hM']
  constructor <;> exact_mod_cast (by linarith)

/-- `x = P/Q`, `M = 240 Q`: the scaled offset. -/
lemma offVal_scaled (x : ℚ) (o : ℤ) :
    offVal x o = ((o * x.num : ℤ) : ℚ) / ((240 * (x.den : ℤ) : ℤ) : ℚ) := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : x = x.num / x.den := (Rat.num_div_den x).symm
  unfold offVal
  conv_lhs => rw [hx]
  push_cast
  field_simp

lemma qrOf_spec (P Q : ℤ) (hQ : 0 < Q) (o : ℤ) :
    o * P = (qrOf P Q o).1 * (240 * Q) + (qrOf P Q o).2 ∧
      0 ≤ (qrOf P Q o).2 ∧ (qrOf P Q o).2 < 240 * Q := by
  unfold qrOf
  simp only
  refine ⟨?_, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have := Int.emod_add_ediv_mul (o * P) (240 * Q)
  linarith

lemma qrOf_zero (P Q : ℤ) : qrOf P Q 0 = (0, 0) := by simp [qrOf]

/-- The candidate point `y = k + r_i / M`. -/
def candY (x : ℚ) (k ri : ℤ) : ℚ := (k : ℚ) + (ri : ℚ) / ((240 * (x.den : ℤ) : ℤ) : ℚ)

lemma candY_sub (x : ℚ) (k ri : ℤ) (o : ℤ) :
    candY x k ri - offVal x o =
      (((k - (qrOf x.num x.den o).1) * (240 * (x.den : ℤ)) + ri - (qrOf x.num x.den o).2 : ℤ) : ℚ)
        / ((240 * (x.den : ℤ) : ℤ) : ℚ) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨h1, -, -⟩ := qrOf_spec x.num x.den hQ o
  have hM : ((240 * (x.den : ℤ) : ℤ) : ℚ) ≠ 0 := by
    have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
    push_cast; positivity
  rw [offVal_scaled, h1, candY]
  field_simp
  push_cast
  ring

lemma floor_candY (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 240 * x.den) (o : ℤ) :
    ⌊candY x k ri - offVal x o⌋ = flAt k ri (qrOf x.num x.den o) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨-, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
  rw [candY_sub, flAt]
  set q := (qrOf x.num x.den o).1
  set r := (qrOf x.num x.den o).2
  rcases lt_or_ge ri r with h | h
  · rw [if_pos h]
    apply floor_div_eq _ _ _ (by omega) <;> nlinarith
  · rw [if_neg (not_lt.2 h)]
    apply floor_div_eq _ _ _ (by omega) <;> nlinarith

lemma ceil_candY (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 240 * x.den) (o : ℤ) :
    ⌈candY x k ri - offVal x o⌉ = clAt k ri false (qrOf x.num x.den o) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨-, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
  rw [candY_sub, clAt, flAt, ebAt]
  set q := (qrOf x.num x.den o).1
  set r := (qrOf x.num x.den o).2
  simp only [Bool.false_eq_true, if_false]
  rcases lt_trichotomy ri r with h | h | h
  · rw [if_pos h, if_neg (ne_of_lt h)]
    apply ceil_div_eq _ _ _ (by omega) <;> nlinarith
  · rw [if_neg (by omega), if_pos h]
    apply ceil_div_eq _ _ _ (by omega) <;> nlinarith
  · rw [if_neg (not_lt.2 h.le), if_neg (ne_of_gt h)]
    apply ceil_div_eq _ _ _ (by omega) <;> nlinarith

/-! ## `phiAt` is `Phi` at a candidate -/

lemma flAt_zero_off (k ri : ℤ) (h0 : 0 ≤ ri) : flAt k ri (0, 0) = k := by
  simp [flAt, not_lt.2 h0]

lemma phiAt_eq_Phi (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 240 * x.den) (right : Bool) :
    phiAt (preOf x.num x.den) (qrOf x.num x.den (-220)) (qrOf x.num x.den 240)
        (qrOf x.num x.den 460) k ri right =
      Phi (fun o => ⌊candY x k ri - offVal x o⌋)
        (fun o => if right then ⌊candY x k ri - offVal x o⌋ + 1
          else ⌈candY x k ri - offVal x o⌉) := by
  cases right
  · simp only [phiAt, Phi, preOf, List.map_map, Function.comp_def, floor_candY x k ri h0 hM,
      ceil_candY x k ri h0 hM, qrOf_zero, flAt_zero_off k ri h0, Bool.false_eq_true, if_false]
  · simp only [phiAt, Phi, preOf, List.map_map, Function.comp_def, floor_candY x k ri h0 hM,
      qrOf_zero, flAt_zero_off k ri h0, clAt, ebAt, if_true]

lemma aOff_mem (b : ℕ × ℕ) (hb : b ∈ blocks) : aOff b.1 ∈ offsets := by
  simp only [offsets, List.mem_cons]
  right; right; right; right
  exact List.mem_flatMap.2 ⟨b, hb, by simp⟩

lemma bOff_mem (b : ℕ × ℕ) (hb : b ∈ blocks) : bOff b.1 ∈ offsets := by
  simp only [offsets, List.mem_cons]
  right; right; right; right
  exact List.mem_flatMap.2 ⟨b, hb, by simp⟩

lemma zero_mem : (0 : ℤ) ∈ offsets := by simp [offsets]
lemma n_mem : (-220 : ℤ) ∈ offsets := by simp [offsets]
lemma o240_mem : (240 : ℤ) ∈ offsets := by simp [offsets]
lemma o460_mem : (460 : ℤ) ∈ offsets := by simp [offsets]

lemma Phi_congr (F C F' C' : ℤ → ℤ) (hF : ∀ o ∈ offsets, F o = F' o)
    (hC : ∀ o ∈ offsets, C o = C' o) : Phi F C = Phi F' C' := by
  unfold Phi
  rw [hF _ zero_mem, hF _ n_mem, hC _ o240_mem, hC _ o460_mem]
  have h1 : (blocks.map fun b => blockS b.2 (F (aOff b.1)) (C (bOff b.1))) =
      (blocks.map fun b => blockS b.2 (F' (aOff b.1)) (C' (bOff b.1))) := by
    apply List.map_congr_left
    intro b hb
    rw [hF _ (aOff_mem b hb), hC _ (bOff_mem b hb)]
  have h2 : (blocks.map fun b =>
      blockP b.2 (F (aOff b.1)) (C (aOff b.1)) (F (bOff b.1)) (C (bOff b.1))) =
      (blocks.map fun b =>
      blockP b.2 (F' (aOff b.1)) (C' (aOff b.1)) (F' (bOff b.1)) (C' (bOff b.1))) := by
    apply List.map_congr_left
    intro b hb
    rw [hF _ (aOff_mem b hb), hC _ (aOff_mem b hb), hF _ (bOff_mem b hb), hC _ (bOff_mem b hb)]
  rw [h1, h2]

/-! ## The closed form of `phiAt` for `k ≥ 1` -/

lemma ebAt_cases (ri : ℤ) (right : Bool) (ql : ℤ × ℤ) : ebAt ri right ql = 0 ∨ ebAt ri right ql = 1 := by
  unfold ebAt; split_ifs <;> simp

/-- `blockS + blockP = m (1 + F_a - C_b)` whenever each `C` is `F` or `F + 1`. -/
lemma blockSP_closed (m Fa Ca Fb Cb : ℤ) (ha : Ca = Fa ∨ Ca = Fa + 1)
    (hb : Cb = Fb ∨ Cb = Fb + 1) : blockS m Fa Cb + blockP m Fa Ca Fb Cb = m * (1 + Fa - Cb) := by
  unfold blockS blockP
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> split_ifs <;>
    first | ring1 | (exfalso; omega)

lemma clAt_cases (k ri : ℤ) (right : Bool) (ql : ℤ × ℤ) :
    clAt k ri right ql = flAt k ri ql ∨ clAt k ri right ql = flAt k ri ql + 1 := by
  unfold clAt
  rcases ebAt_cases ri right ql with h | h <;> rw [h] <;> simp

lemma flAt_shift (k ri : ℤ) (ql : ℤ × ℤ) : flAt k ri ql = k + flAt 0 ri ql := by
  unfold flAt; ring

lemma clAt_shift (k ri : ℤ) (right : Bool) (ql : ℤ × ℤ) :
    clAt k ri right ql = k + clAt 0 ri right ql := by
  unfold clAt; rw [flAt_shift]; ring

lemma sum_SP (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (k ri : ℤ) (right : Bool) :
    (pre.map fun e => blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2)).sum +
      (pre.map fun e => blockP e.1 (flAt k ri e.2.1) (clAt k ri right e.2.1)
        (flAt k ri e.2.2) (clAt k ri right e.2.2)).sum = Tval pre ri right := by
  unfold Tval
  induction pre with
  | nil => simp
  | cons e pre ih =>
    simp only [List.map_cons, List.sum_cons]
    have h := blockSP_closed e.1 (flAt k ri e.2.1) (clAt k ri right e.2.1) (flAt k ri e.2.2)
      (clAt k ri right e.2.2) (clAt_cases _ _ _ _) (clAt_cases _ _ _ _)
    have h2 : e.1 * (1 + flAt k ri e.2.1 - clAt k ri right e.2.2) =
        e.1 * (1 + flAt 0 ri e.2.1 - clAt 0 ri right e.2.2) := by
      rw [flAt_shift k, clAt_shift k]; ring
    linarith

lemma c_shift (qn q2 q3 : ℤ × ℤ) (k ri : ℤ) (right : Bool) :
    5 * (flAt k ri qn - k) + 5 * (clAt k ri right q2 - clAt k ri right q3) =
      cval qn q2 q3 ri right := by
  unfold cval
  rw [flAt_shift k, clAt_shift k, clAt_shift k]
  ring

/-- For `k ≥ 1` with some block containing the candidate, `phiAt = T + 4 - c`. -/
lemma phiAt_of_pos (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (qn q2 q3 : ℤ × ℤ) (k ri : ℤ)
    (right : Bool) (hk : 1 ≤ k)
    (hS : (pre.map fun e => blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2)).sum ≠ 0) :
    phiAt pre qn q2 q3 k ri right = Tval pre ri right + 4 - cval qn q2 q3 ri right := by
  have h1 := sum_SP pre k ri right
  have h2 := c_shift qn q2 q3 k ri right
  unfold phiAt
  simp only
  rw [if_neg hS, if_pos hk]
  linarith

/-! ## Validity -/

/-- The candidate `y = k + r_i/M` (or its right limit) lies in `[0, x]` (resp. `[0, x)`). -/
abbrev Valid (qX rX ri k : ℤ) (right : Bool) : Prop := 0 ≤ k ∧ k ≤ kmax qX rX ri right

lemma candY_eq (x : ℚ) (k ri : ℤ) :
    candY x k ri = ((k * (240 * (x.den : ℤ)) + ri : ℤ) : ℚ) / ((240 * (x.den : ℤ) : ℤ) : ℚ) := by
  have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
  unfold candY
  field_simp
  push_cast
  ring

lemma x_eq_scaled (x : ℚ) :
    x = ((240 * x.num : ℤ) : ℚ) / ((240 * (x.den : ℤ) : ℤ) : ℚ) := by
  have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
  conv_lhs => rw [← Rat.num_div_den x]
  field_simp
  push_cast
  ring

lemma valid_int (P Q M k ri : ℤ) (hQ : 0 < Q) (hMdef : M = 240 * Q) (h0 : 0 ≤ ri) (hM : ri < M)
    (hk : 0 ≤ k * M + ri) (right : Bool)
    (hle : if right then k * M + ri < 240 * P else k * M + ri ≤ 240 * P) :
    Valid (P / Q) (240 * (P % Q)) ri k right := by
  have hPQ := Int.emod_add_ediv_mul P Q
  have hr0 : 0 ≤ P % Q := Int.emod_nonneg _ (by omega)
  have hrQ : P % Q < Q := Int.emod_lt_of_pos _ hQ
  have hX : 240 * P = (P / Q) * M + 240 * (P % Q) := by subst hMdef; linarith
  have hMpos : 0 < M := by omega
  have hle' : k * M + ri ≤ 240 * P := by cases right <;> simp at hle <;> omega
  have hk0 : 0 ≤ k := by
    by_contra hneg
    have : (k + 1) * M ≤ 0 := by nlinarith
    nlinarith
  have hkq : k ≤ P / Q := by
    by_contra hgt
    have : (P / Q + 1) * M ≤ k * M := by
      apply mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  refine ⟨hk0, ?_⟩
  unfold kmax
  rcases lt_or_eq_of_le hkq with hlt | heq
  · split_ifs <;> omega
  · have hfin : if right then ri < 240 * (P % Q) else ri ≤ 240 * (P % Q) := by
      rw [heq] at hle
      cases right <;> simp at hle ⊢ <;> linarith
    rw [if_pos hfin]; omega

lemma valid_of_le (x : ℚ) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 240 * x.den)
    (hk : 0 ≤ candY x k ri) (right : Bool)
    (hle : if right then candY x k ri < x else candY x k ri ≤ x) :
    Valid (x.num / x.den) (240 * (x.num % x.den)) ri k right := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  have hMq : (0 : ℚ) < ((240 * (x.den : ℤ) : ℤ) : ℚ) := by
    exact_mod_cast (by omega : (0 : ℤ) < 240 * x.den)
  have hxM : x * ((240 * (x.den : ℤ) : ℤ) : ℚ) = ((240 * x.num : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  rw [candY_eq] at hk hle
  apply valid_int x.num x.den (240 * x.den) k ri hQ rfl h0 hM _ right
  · cases right
    · simp only [Bool.false_eq_true, if_false] at hle ⊢
      rw [div_le_iff₀ hMq, hxM] at hle
      exact_mod_cast hle
    · simp only [if_true] at hle ⊢
      rw [div_lt_iff₀ hMq, hxM] at hle
      exact_mod_cast hle
  · rw [le_div_iff₀ hMq, zero_mul] at hk
    exact_mod_cast hk

/-! ## Candidates are bounded by `cand` -/

lemma sum_blockS_ne_zero {pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))} {F C : ℤ × (ℤ × ℤ) × (ℤ × ℤ) → ℤ}
    (h : (pre.map fun e => blockS e.1 (F e) (C e)).sum ≠ 0) :
    ∃ e ∈ pre, e.1 ≠ 0 ∧ 0 ≤ F e ∧ C e ≤ 0 := by
  induction pre with
  | nil => simp at h
  | cons e pre ih =>
    simp only [List.map_cons, List.sum_cons] at h
    by_cases he : blockS e.1 (F e) (C e) = 0
    · rw [he, zero_add] at h
      obtain ⟨e', he', h'⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩
    · unfold blockS at he
      split_ifs at he with hc
      · exact ⟨e, List.mem_cons_self, he, hc⟩
      · exact absurd rfl he

/-- The block data are nonnegative multiplicities. -/
def PreOK (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) : Prop := ∀ e ∈ pre, 0 ≤ e.1

lemma preOf_ok (P Q : ℤ) : PreOK (preOf P Q) := by
  intro e he
  unfold preOf at he
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 he
  positivity

lemma has1_of (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (hpre : PreOK pre) (qX rX ri k : ℤ)
    (right : Bool) (hk : 1 ≤ k) (hv : k ≤ kmax qX rX ri right)
    (hS : (pre.map fun e => blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2)).sum ≠ 0) :
    has1 pre qX rX ri right = true := by
  obtain ⟨e, he, hm, hF, hC⟩ := sum_blockS_ne_zero hS
  unfold has1
  rw [List.any_eq_true]
  refine ⟨e, he, ?_⟩
  have hm' : 0 < e.1 := lt_of_le_of_ne (hpre e he) (Ne.symm hm)
  simp only [flAt, clAt] at hF hC
  simp only [decide_eq_true_eq]
  refine ⟨hm', ?_, ?_⟩
  · rw [max_le_iff]; constructor <;> omega
  · rw [max_le_iff]; constructor <;> omega

/-- **Every valid candidate is bounded by its residue's `cand`.** -/
lemma phiAt_le_cand (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (hpre : PreOK pre) (qn q2 q3 : ℤ × ℤ)
    (qX rX ri k : ℤ) (right : Bool) (hv : Valid qX rX ri k right) :
    phiAt pre qn q2 q3 k ri right ≤ max 0 (cand pre qn q2 q3 qX rX ri right) := by
  obtain ⟨hk0, hkm⟩ := hv
  by_cases hS : (pre.map fun e => blockS e.1 (flAt k ri e.2.1) (clAt k ri right e.2.2)).sum = 0
  · have : phiAt pre qn q2 q3 k ri right = 0 := by
      unfold phiAt; simp only; rw [if_pos hS]
    rw [this]; exact le_max_left _ _
  rcases eq_or_lt_of_le hk0 with h | h
  · subst h
    exact (le_max_left _ _).trans (le_max_right _ _)
  · have hk : 1 ≤ k := h
    rw [phiAt_of_pos pre qn q2 q3 k ri right hk hS]
    have h1 := has1_of pre hpre qX rX ri k right hk hkm hS
    unfold cand
    rw [h1, if_pos rfl]
    exact (le_max_right _ _).trans (le_max_right _ _)

/-! ## Folds -/

section Fold
variable {α : Type*}

lemma foldl_step_ge (step : ℤ → α → ℤ) (hstep : ∀ acc a, acc ≤ step acc a) :
    ∀ (l : List α) (init : ℤ), init ≤ l.foldl step init
  | [], _ => le_rfl
  | a :: l, init => (hstep init a).trans (foldl_step_ge step hstep l _)

lemma foldl_mem_ge (step : ℤ → α → ℤ) (hstep : ∀ acc a, acc ≤ step acc a) (v : ℤ) (a₀ : α)
    (hv : ∀ acc, v ≤ step acc a₀) :
    ∀ (l : List α) (init : ℤ), a₀ ∈ l → v ≤ l.foldl step init
  | [], _, h => by simp at h
  | a :: l, init, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (hv init).trans (foldl_step_ge step hstep l _)
    · exact foldl_mem_ge step hstep v a₀ hv l _ h

end Fold

lemma eStarInt_nonneg (x : ℚ) : 0 ≤ eStarInt x := by
  unfold eStarInt
  exact foldl_step_ge _ (fun acc o => le_max_left _ _) _ _

lemma cand_le_eStarInt (x : ℚ) (o : ℤ) (ho : o ∈ offsets) (right : Bool) :
    cand (preOf x.num x.den) (qrOf x.num x.den (-220)) (qrOf x.num x.den 240)
      (qrOf x.num x.den 460) (x.num / x.den) (240 * (x.num % x.den)) (qrOf x.num x.den o).2
      right ≤ eStarInt x := by
  unfold eStarInt
  dsimp only
  apply foldl_mem_ge _ (fun acc o => le_max_left _ _) _ o _ offsets _ ho
  intro acc
  cases right
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- A valid candidate of residue class `o` is bounded by `eStarInt`. -/
lemma phiAt_le_eStarInt (x : ℚ) (o : ℤ) (ho : o ∈ offsets) (k : ℤ) (right : Bool)
    (hv : Valid (x.num / x.den) (240 * (x.num % x.den)) (qrOf x.num x.den o).2 k right) :
    phiAt (preOf x.num x.den) (qrOf x.num x.den (-220)) (qrOf x.num x.den 240)
      (qrOf x.num x.den 460) k (qrOf x.num x.den o).2 right ≤ eStarInt x :=
  (phiAt_le_cand _ (preOf_ok _ _) _ _ _ _ _ _ k right hv).trans
    (max_le (eStarInt_nonneg x) (cand_le_eStarInt x o ho right))

/-! ## Main soundness theorem -/

/-- **`eStarInt` bounds `gfun`.** For `x ≥ 1` (in fact `x > 0`) and every `0 ≤ y ≤ x`,
`gfun x y ≤ eStarInt x`. -/
theorem gfun_le_eStarInt (x y : ℚ) (hy0 : 0 ≤ y) (hyx : y ≤ x) : gfun x y ≤ eStarInt x := by
  rw [gfun_eq_Phi x y]
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  -- the largest breakpoint `≤ y`
  set bv : ℤ → ℚ := fun o => offVal x o + ⌊y - offVal x o⌋ with hbv
  have hmem0 : (0 : ℤ) ∈ offsets.toFinset := by rw [List.mem_toFinset]; exact zero_mem
  obtain ⟨o, ho, hmax⟩ := offsets.toFinset.exists_max_image bv ⟨0, hmem0⟩
  rw [List.mem_toFinset] at ho
  have hmax' : ∀ o' ∈ offsets, bv o' ≤ bv o := fun o' h' => hmax o' (List.mem_toFinset.2 h')
  set j := ⌊y - offVal x o⌋
  set b := bv o
  have hb_le : b ≤ y := by
    have := Int.floor_le (y - offVal x o)
    simp only [b, bv]; linarith
  have hb0 : 0 ≤ b := by
    have h1 := hmax' 0 zero_mem
    have h2 : bv 0 = ⌊y⌋ := by simp only [bv, offVal_zero]; simp
    have h3 : (0 : ℚ) ≤ ⌊y⌋ := by exact_mod_cast Int.floor_nonneg.2 hy0
    linarith
  have hFD : ∀ o' ∈ offsets, ⌊y - offVal x o'⌋ = ⌊b - offVal x o'⌋ := by
    intro o' h'
    apply le_antisymm
    · apply Int.le_floor.2
      have := hmax' o' h'
      simp only [bv] at this
      linarith
    · exact Int.floor_le_floor (by linarith)
  -- `b` as a candidate
  obtain ⟨hB, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
  set ri := (qrOf x.num x.den o).2
  set k := (qrOf x.num x.den o).1 + j
  have hbc : b = candY x k ri := by
    have hMne : ((240 * (x.den : ℤ) : ℤ) : ℚ) ≠ 0 := by
      have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
      push_cast; positivity
    have h1 : offVal x o = ((qrOf x.num x.den o).1 : ℚ) + (ri : ℚ) / ((240 * (x.den : ℤ) : ℤ) : ℚ) := by
      rw [offVal_scaled, hB]
      field_simp
      push_cast
      ring
    change offVal x o + (j : ℚ) = candY x k ri
    rw [h1, candY]
    simp only [k]
    push_cast
    ring
  rcases eq_or_lt_of_le hb_le with hby | hby
  · -- `y` is itself a breakpoint
    have hy' : y = candY x k ri := hby.symm.trans hbc
    have hv := valid_of_le x k ri hr0 hrM (hbc ▸ hb0) false (by simp; rw [← hy']; exact hyx)
    have := phiAt_le_eStarInt x o ho k false hv
    rw [phiAt_eq_Phi x k ri hr0 hrM false] at this
    simp only [Bool.false_eq_true, if_false] at this
    rw [hy']
    exact this
  · -- `y` lies strictly right of the breakpoint `b`
    have hCD : ∀ o' ∈ offsets, ⌈y - offVal x o'⌉ = ⌊b - offVal x o'⌋ + 1 := by
      intro o' h'
      rw [← hFD o' h']
      apply (Int.ceil_eq_floor_add_one_iff_notMem _).2
      rintro ⟨n, hn⟩
      have h1 := hmax' o' h'
      have h2 : ⌊y - offVal x o'⌋ = n := by rw [← hn, Int.floor_intCast]
      simp only [bv] at h1
      rw [h2, hn] at h1
      have : b < b := lt_of_lt_of_le hby (by linarith)
      exact lt_irrefl _ this
    have hv := valid_of_le x k ri hr0 hrM (hbc ▸ hb0) true
      (by simp; rw [← hbc]; exact lt_of_lt_of_le hby hyx)
    have := phiAt_le_eStarInt x o ho k true hv
    rw [phiAt_eq_Phi x k ri hr0 hrM true] at this
    simp only [if_true] at this
    rw [Phi_congr _ _ (fun o => ⌊candY x k ri - offVal x o⌋)
      (fun o => ⌊candY x k ri - offVal x o⌋ + 1)
      (fun o' h' => by rw [hFD o' h', hbc]) (fun o' h' => by rw [hCD o' h', hbc])]
    exact this

/-- The bracket where some block contains `y` is bounded by `eStarInt`. -/
theorem bracket_le_eStarInt (x y : ℚ) (hy0 : 0 ≤ y) (hyx : y ≤ x) (hS : 1 ≤ Sfun x y) :
    bracket x y ≤ eStarInt x := by
  have h := gfun_le_eStarInt x y hy0 hyx
  unfold gfun at h
  rwa [if_neg (by omega)] at h

end ZetaIrr.Z7.CertA
