/-
# Step-function property of `e*` between event points (PROOF_ZETA §5.3), instance Z7

For consecutive event points `a < b` of `events 400` and any `x ∈ (a, b)`:

  `∀ y ∈ [0, x], gfun(x, y) ≤ eStarInt((a+b)/2)`  (`gfun_le_eStarInt_mid`).

Proof. Every breakpoint line `y = offVal x o + j` (`o ∈ offsets`) belongs to one of the line
families `fams` (slope `o/240`). Between two events no two lines cross and no integer is passed, so
the relative order of all breakpoints (and `⌊x⌋`) is the same at `x` and at `mid` (`SameType`). Map
`y` to the corresponding point `y'` at `mid` (`gfun_le_eStarInt_of_sameType`): the floor data, hence
`gfun`, agree.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.CertA.Sound

namespace ZetaIrr.Z7.CertA

open Finset

/-! ## Breakpoints at a fixed `x` -/

/-- The largest breakpoint `b = offVal x o + j ≤ y`, and the floor data of `y` in terms of `b`. -/
lemma exists_break (x y : ℚ) (hy0 : 0 ≤ y) :
    ∃ o ∈ offsets, ∃ j : ℤ, 0 ≤ offVal x o + j ∧
      (∀ o' ∈ offsets, ⌊y - offVal x o'⌋ = ⌊offVal x o + j - offVal x o'⌋) ∧
      (offVal x o + j = y ∨ (offVal x o + j < y ∧
        ∀ o' ∈ offsets, ⌈y - offVal x o'⌉ = ⌊offVal x o + j - offVal x o'⌋ + 1)) := by
  set bv : ℤ → ℚ := fun o => offVal x o + ⌊y - offVal x o⌋ with hbv
  have hmem0 : (0 : ℤ) ∈ offsets.toFinset := List.mem_toFinset.2 zero_mem
  obtain ⟨o, ho, hmax⟩ := offsets.toFinset.exists_max_image bv ⟨0, hmem0⟩
  rw [List.mem_toFinset] at ho
  have hmax' : ∀ o' ∈ offsets, bv o' ≤ bv o := fun o' h' => hmax o' (List.mem_toFinset.2 h')
  refine ⟨o, ho, ⌊y - offVal x o⌋, ?_, ?_, ?_⟩
  · have h1 := hmax' 0 zero_mem
    have h2 : bv 0 = ⌊y⌋ := by simp only [bv, offVal_zero]; simp
    have h3 : (0 : ℚ) ≤ ⌊y⌋ := by exact_mod_cast Int.floor_nonneg.2 hy0
    simp only [bv] at h1 h2
    linarith
  · intro o' h'
    have hb_le : offVal x o + ⌊y - offVal x o⌋ ≤ y := by
      have := Int.floor_le (y - offVal x o); linarith
    apply le_antisymm
    · apply Int.le_floor.2
      have := hmax' o' h'
      simp only [bv] at this
      linarith
    · exact Int.floor_le_floor (by linarith)
  · have hb_le : offVal x o + ⌊y - offVal x o⌋ ≤ y := by
      have := Int.floor_le (y - offVal x o); linarith
    rcases eq_or_lt_of_le hb_le with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, fun o' h' => ?_⟩
      have hFD : ⌊y - offVal x o'⌋ = ⌊offVal x o + ⌊y - offVal x o⌋ - offVal x o'⌋ := by
        apply le_antisymm
        · apply Int.le_floor.2
          have := hmax' o' h'
          simp only [bv] at this
          linarith
        · exact Int.floor_le_floor (by linarith)
      rw [← hFD]
      apply (Int.ceil_eq_floor_add_one_iff_notMem _).2
      rintro ⟨n, hn⟩
      have h1 := hmax' o' h'
      have h2 : ⌊y - offVal x o'⌋ = n := by rw [← hn, Int.floor_intCast]
      simp only [bv] at h1
      rw [h2, hn] at h1
      linarith

/-- The breakpoint `b = offVal x o + j` as a grid candidate `k + r_i/M`. -/
lemma break_eq_candY (x : ℚ) (o : ℤ) (j : ℤ) :
    offVal x o + j = candY x ((qrOf x.num x.den o).1 + j) (qrOf x.num x.den o).2 := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨hB, -, -⟩ := qrOf_spec x.num x.den hQ o
  have hMne : ((240 * (x.den : ℤ) : ℤ) : ℚ) ≠ 0 := by
    have : (0 : ℚ) < x.den := by exact_mod_cast x.pos
    push_cast; positivity
  have h1 : offVal x o = ((qrOf x.num x.den o).1 : ℚ) +
      ((qrOf x.num x.den o).2 : ℚ) / ((240 * (x.den : ℤ) : ℤ) : ℚ) := by
    rw [offVal_scaled, hB]
    field_simp
    push_cast
    ring
  rw [h1, candY]
  push_cast
  ring

/-- The value at a breakpoint `b = offVal x o + j` with `0 ≤ b ≤ x` is a candidate. -/
lemma breakVal_le (x : ℚ) (o : ℤ) (ho : o ∈ offsets) (j : ℤ)
    (h0 : 0 ≤ offVal x o + j) (hle : offVal x o + j ≤ x) :
    Phi (fun o' => ⌊offVal x o + j - offVal x o'⌋)
      (fun o' => ⌈offVal x o + j - offVal x o'⌉) ≤ eStarInt x := by
  have h := gfun_le_eStarInt x _ h0 hle
  rwa [gfun_eq_Phi] at h

/-- The right-limit value at a breakpoint `b = offVal x o + j` with `0 ≤ b < x` is a candidate. -/
lemma rightLimit_le (x : ℚ) (o : ℤ) (ho : o ∈ offsets) (j : ℤ)
    (h0 : 0 ≤ offVal x o + j) (hlt : offVal x o + j < x) :
    Phi (fun o' => ⌊offVal x o + j - offVal x o'⌋)
      (fun o' => ⌊offVal x o + j - offVal x o'⌋ + 1) ≤ eStarInt x := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨-, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
  set ri := (qrOf x.num x.den o).2
  set k := (qrOf x.num x.den o).1 + j
  have hbc : offVal x o + j = candY x k ri := break_eq_candY x o j
  rw [hbc] at h0 hlt ⊢
  have hv := valid_of_le x k ri hr0 hrM h0 true (by simpa using hlt)
  have := phiAt_le_eStarInt x o ho k true hv
  rw [phiAt_eq_Phi x k ri hr0 hrM true] at this
  simpa using this

/-! ## Transfer between two `x` with the same order type -/

/-- `x` and `x'` have the same order type: for all offsets `o₁, o₂` the differences
`offVal o₁ - offVal o₂` lie on the same side of (or on) every integer. -/
def SameType (x x' : ℚ) : Prop :=
  ∀ o₁ ∈ offsets, ∀ o₂ ∈ offsets, ∀ n : ℤ,
    ((n : ℚ) ≤ offVal x o₁ - offVal x o₂ ↔ (n : ℚ) ≤ offVal x' o₁ - offVal x' o₂) ∧
    (offVal x o₁ - offVal x o₂ ≤ n ↔ offVal x' o₁ - offVal x' o₂ ≤ n)

lemma floor_transfer {x x' : ℚ} (h : SameType x x') {o₁ o₂ : ℤ} (h₁ : o₁ ∈ offsets)
    (h₂ : o₂ ∈ offsets) (j : ℤ) :
    ⌊offVal x o₁ + j - offVal x o₂⌋ = ⌊offVal x' o₁ + j - offVal x' o₂⌋ := by
  rw [show offVal x o₁ + j - offVal x o₂ = (offVal x o₁ - offVal x o₂) + j by ring,
    show offVal x' o₁ + j - offVal x' o₂ = (offVal x' o₁ - offVal x' o₂) + j by ring,
    Int.floor_add_intCast, Int.floor_add_intCast]
  congr 1
  apply le_antisymm
  · exact Int.le_floor.2 ((h o₁ h₁ o₂ h₂ _).1.1 (Int.floor_le _))
  · exact Int.le_floor.2 ((h o₁ h₁ o₂ h₂ _).1.2 (Int.floor_le _))

lemma ceil_transfer {x x' : ℚ} (h : SameType x x') {o₁ o₂ : ℤ} (h₁ : o₁ ∈ offsets)
    (h₂ : o₂ ∈ offsets) (j : ℤ) :
    ⌈offVal x o₁ + j - offVal x o₂⌉ = ⌈offVal x' o₁ + j - offVal x' o₂⌉ := by
  rw [show offVal x o₁ + j - offVal x o₂ = (offVal x o₁ - offVal x o₂) + j by ring,
    show offVal x' o₁ + j - offVal x' o₂ = (offVal x' o₁ - offVal x' o₂) + j by ring,
    Int.ceil_add_intCast, Int.ceil_add_intCast]
  congr 1
  apply le_antisymm
  · exact Int.ceil_le.2 ((h o₁ h₁ o₂ h₂ _).2.2 (Int.le_ceil _))
  · exact Int.ceil_le.2 ((h o₁ h₁ o₂ h₂ _).2.1 (Int.le_ceil _))

/-- **Transfer.** If `x, x'` have the same order type, then `gfun(x, y) ≤ eStarInt(x')` for all
`0 ≤ y ≤ x`. -/
theorem gfun_le_eStarInt_of_sameType (x x' : ℚ) (h : SameType x x') (y : ℚ) (hy0 : 0 ≤ y)
    (hyx : y ≤ x) : gfun x y ≤ eStarInt x' := by
  obtain ⟨o, ho, j, hb0, hFD, hcase⟩ := exists_break x y hy0
  have hF : ∀ o' ∈ offsets,
      ⌊offVal x o + j - offVal x o'⌋ = ⌊offVal x' o + j - offVal x' o'⌋ :=
    fun o' h' => floor_transfer h ho h' j
  have hC : ∀ o' ∈ offsets,
      ⌈offVal x o + j - offVal x o'⌉ = ⌈offVal x' o + j - offVal x' o'⌉ :=
    fun o' h' => ceil_transfer h ho h' j
  -- `b' = offVal x' o + j` lies in `[0, x']`
  have hb0' : 0 ≤ offVal x' o + j := by
    have := hF _ zero_mem
    rw [offVal_zero, offVal_zero, sub_zero, sub_zero] at this
    have h1 : 0 ≤ ⌊offVal x o + j⌋ := Int.floor_nonneg.2 hb0
    rw [this] at h1
    exact Int.floor_nonneg.1 h1
  rw [gfun_eq_Phi x y]
  rcases hcase with hby | ⟨hby, hCD⟩
  · -- `y` is a breakpoint
    have hbx' : offVal x' o + j ≤ x' := by
      have := hC _ o240_mem
      rw [offVal_240, offVal_240] at this
      have h1 : ⌈offVal x o + j - x⌉ ≤ 0 := by
        apply Int.ceil_le.2; simp; linarith
      rw [this] at h1
      have := Int.ceil_le.1 h1
      simp at this
      linarith
    rw [← hby]
    rw [Phi_congr _ _ (fun o' => ⌊offVal x' o + j - offVal x' o'⌋)
      (fun o' => ⌈offVal x' o + j - offVal x' o'⌉) hF hC]
    exact breakVal_le x' o ho j hb0' hbx'
  · -- `y` lies right of the breakpoint `b`
    have hbx' : offVal x' o + j < x' := by
      have := hF _ o240_mem
      rw [offVal_240, offVal_240] at this
      have h1 : ⌊offVal x o + j - x⌋ < 0 := by
        apply Int.floor_lt.2; simp; linarith
      rw [this] at h1
      have := Int.floor_lt.1 h1
      simp at this
      linarith
    rw [Phi_congr _ _ (fun o' => ⌊offVal x' o + j - offVal x' o'⌋)
      (fun o' => ⌊offVal x' o + j - offVal x' o'⌋ + 1)
      (fun o' h' => by rw [hFD o' h', hF o' h'])
      (fun o' h' => by rw [hCD o' h', hF o' h'])]
    exact rightLimit_le x' o ho j hb0' hbx'

/-! ## The event list -/

lemma mem_dedupAdj : ∀ (l : List ℚ) (z : ℚ), z ∈ dedupAdj l ↔ z ∈ l
  | a :: b :: l, z => by
    have ih := mem_dedupAdj (b :: l) z
    rw [dedupAdj]
    split_ifs with h
    · rw [ih]; subst h; simp
    · simp only [List.mem_cons] at ih ⊢; rw [ih]
  | [], z => by simp [dedupAdj]
  | [a], z => by simp [dedupAdj]

lemma pairwise_dedupAdj : ∀ (l : List ℚ), l.Pairwise (· ≤ ·) → (dedupAdj l).Pairwise (· < ·)
  | a :: b :: l, h => by
    have ih := pairwise_dedupAdj (b :: l) h.of_cons
    rw [dedupAdj]
    split_ifs with hab
    · exact ih
    · rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, ih⟩
      rw [mem_dedupAdj] at hz
      have hab' : a ≤ b := (List.pairwise_cons.1 h).1 b List.mem_cons_self
      have hbz : b ≤ z := by
        rcases List.mem_cons.1 hz with rfl | hz
        · exact le_rfl
        · exact (List.pairwise_cons.1 h.of_cons).1 z hz
      exact lt_of_lt_of_le (lt_of_le_of_ne hab' hab) hbz
  | [], _ => by simp [dedupAdj]
  | [a], _ => by simp [dedupAdj]

lemma mem_events (X : ℕ) (z : ℚ) : z ∈ events X ↔ z ∈ cuts X ∨ z ∈ crossings 1 X := by
  unfold events
  rw [mem_dedupAdj, List.mem_mergeSort, List.mem_append]

/-- (E4) The event list is strictly increasing. -/
lemma events_pairwise (X : ℕ) : (events X).Pairwise (· < ·) := by
  unfold events
  apply pairwise_dedupAdj
  have := List.pairwise_mergeSort (le := fun a b : ℚ => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; exact le_trans h1 h2)
    (fun a b => by simpa using le_total a b) (cuts X ++ crossings 1 X)
  simpa using this

/-- (E1) Events lie in `[1, 400]`. -/
lemma events_bounds (z : ℚ) (hz : z ∈ events 400) : 1 ≤ z ∧ z ≤ 400 := by
  rw [mem_events] at hz
  rcases hz with hz | hz
  · unfold cuts at hz
    rw [List.mem_append, List.mem_map, List.mem_map] at hz
    rcases hz with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [List.mem_range] at hj
      have : (j : ℚ) ≤ 39 := by exact_mod_cast (by omega : j ≤ 39)
      have : (0 : ℚ) ≤ j := by positivity
      constructor <;> linarith
    · rw [List.mem_range] at hj
      have : (j : ℚ) ≤ 794 := by exact_mod_cast (by omega : j ≤ 794)
      have : (0 : ℚ) ≤ j := by positivity
      constructor <;> linarith
  · unfold crossings at hz
    rw [List.mem_flatMap] at hz
    obtain ⟨p₁, -, hz⟩ := hz
    rw [List.mem_flatMap] at hz
    obtain ⟨p₂, -, hz⟩ := hz
    unfold crossPair at hz
    split_ifs at hz
    · rw [List.mem_filter] at hz
      have := hz.2
      simp only [decide_eq_true_eq] at this
      push_cast at this
      constructor <;> linarith [this.1, this.2]
    · simp at hz

/-- (E2) Every integer in `[1, 400]` is an event. -/
lemma int_mem_events (n : ℤ) (h1 : 1 ≤ n) (h2 : n ≤ 400) : (n : ℚ) ∈ events 400 := by
  rw [mem_events]
  left
  unfold cuts
  rw [List.mem_append, List.mem_map, List.mem_map]
  by_cases hn : n ≤ 2
  · left
    refine ⟨(20 * (n - 1)).toNat, by rw [List.mem_range]; omega, ?_⟩
    have : (((20 * (n - 1)).toNat : ℕ) : ℚ) = 20 * ((n : ℚ) - 1) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [this]; ring
  · right
    refine ⟨(2 * (n - 3)).toNat, by rw [List.mem_range]; omega, ?_⟩
    have : (((2 * (n - 3)).toNat : ℕ) : ℚ) = 2 * ((n : ℚ) - 3) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [this]; ring

/-- (E3) Every crossing of two families inside `(1, 400)` is an event. -/
lemma cross_mem_events (s₁ s₂ : ℚ) (h₁ : s₁ ∈ fams) (h₂ : s₂ ∈ fams) (hs : s₂ < s₁)
    (m : ℤ) (hz1 : 1 < (m : ℚ) / (s₁ - s₂)) (hz2 : (m : ℚ) / (s₁ - s₂) < 400) :
    (m : ℚ) / (s₁ - s₂) ∈ events 400 := by
  rw [mem_events]
  right
  unfold crossings
  rw [List.mem_flatMap]
  refine ⟨s₁, h₁, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨s₂, h₂, ?_⟩
  unfold crossPair
  rw [if_pos hs]
  have hds : 0 < s₁ - s₂ := by linarith
  have hz1' := hz1
  have hz2' := hz2
  rw [lt_div_iff₀ hds, one_mul] at hz1'
  rw [div_lt_iff₀ hds] at hz2'
  have hm0 : ⌊(1 : ℚ) * (s₁ - s₂)⌋ ≤ m := by
    have := Int.floor_le ((1 : ℚ) * (s₁ - s₂))
    have : ((⌊(1 : ℚ) * (s₁ - s₂)⌋ : ℤ) : ℚ) < m := by linarith
    exact_mod_cast this.le
  have hm1 : m ≤ ⌈((400 : ℕ) : ℚ) * (s₁ - s₂)⌉ := by
    have := Int.le_ceil (((400 : ℕ) : ℚ) * (s₁ - s₂))
    have : (m : ℚ) < ⌈((400 : ℕ) : ℚ) * (s₁ - s₂)⌉ := by
      push_cast at this ⊢; linarith
    exact_mod_cast this.le
  rw [List.mem_filter, List.mem_map]
  refine ⟨⟨(m - ⌊(1 : ℚ) * (s₁ - s₂)⌋).toNat, ?_, ?_⟩, ?_⟩
  · rw [List.mem_range]; omega
  · have hnn : 0 ≤ m - ⌊(1 : ℚ) * (s₁ - s₂)⌋ := by omega
    have hi : ⌊(1 : ℚ) * (s₁ - s₂)⌋ +
        (((m - ⌊(1 : ℚ) * (s₁ - s₂)⌋).toNat : ℕ) : ℤ) = m := by
      rw [Int.toNat_of_nonneg hnn]; ring
    rw [hi]
  · simp only [decide_eq_true_eq]
    push_cast
    exact ⟨hz1, hz2⟩

/-- (E5) Every offset is (the scaled form of) a line family. -/
lemma fam_of_offset (o : ℤ) (ho : o ∈ offsets) : (o : ℚ) / 240 ∈ fams := by
  unfold fams
  rw [List.mem_dedup]
  unfold offsets at ho
  simp only [List.mem_cons, List.mem_flatMap] at ho
  rcases ho with rfl | rfl | rfl | rfl | ⟨b, hb, hb'⟩
  · refine List.mem_append_left _ ?_; norm_num
  · refine List.mem_append_left _ ?_; norm_num
  · refine List.mem_append_left _ ?_; norm_num
  · refine List.mem_append_left _ ?_; norm_num
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨b, hb, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl
    · simp only [aOff, dlt, List.mem_cons]
      left; push_cast; ring
    · simp only [bOff, dlt, List.mem_cons]
      right; left; push_cast; ring

/-! ## Consecutive events -/

/-- `a, b` are adjacent entries of `l`. -/
def Consec (l : List ℚ) (a b : ℚ) : Prop := ∃ l₁ l₂, l = l₁ ++ a :: b :: l₂

lemma Consec.mem_left {l : List ℚ} {a b : ℚ} (h : Consec l a b) : a ∈ l := by
  obtain ⟨l₁, l₂, rfl⟩ := h; simp

lemma Consec.mem_right {l : List ℚ} {a b : ℚ} (h : Consec l a b) : b ∈ l := by
  obtain ⟨l₁, l₂, rfl⟩ := h; simp

lemma Consec.no_between {l : List ℚ} {a b : ℚ} (h : Consec l a b) (hl : l.Pairwise (· < ·))
    (z : ℚ) (hz : z ∈ l) : ¬ (a < z ∧ z < b) := by
  obtain ⟨l₁, l₂, rfl⟩ := h
  rintro ⟨h1, h2⟩
  rw [List.pairwise_append] at hl
  obtain ⟨-, hr, hcross⟩ := hl
  rw [List.mem_append] at hz
  rcases hz with hz | hz
  · have := hcross z hz a List.mem_cons_self
    linarith
  · rcases List.mem_cons.1 hz with rfl | hz
    · linarith
    rcases List.mem_cons.1 hz with rfl | hz
    · linarith
    · have := (List.pairwise_cons.1 (List.pairwise_cons.1 hr).2).1 z hz
      linarith

lemma Consec.lt {l : List ℚ} {a b : ℚ} (h : Consec l a b) (hl : l.Pairwise (· < ·)) :
    a < b := by
  obtain ⟨l₁, l₂, rfl⟩ := h
  rw [List.pairwise_append] at hl
  exact (List.pairwise_cons.1 hl.2.1).1 b List.mem_cons_self

/-- A crossing value `z0` of the two families of `o₁, o₂` (with `s₁ > s₂`) is not strictly inside
an event interval. -/
lemma cross_not_between (a b : ℚ) (hc : Consec (events 400) a b) (o₁ o₂ : ℤ)
    (h₁ : o₁ ∈ offsets) (h₂ : o₂ ∈ offsets) (n : ℤ)
    (hs : (o₂ : ℚ) / 240 < (o₁ : ℚ) / 240) :
    let z0 := (n : ℚ) / ((o₁ : ℚ) / 240 - (o₂ : ℚ) / 240)
    z0 ≤ a ∨ b ≤ z0 := by
  intro z0
  have ha := (events_bounds a hc.mem_left).1
  have hb := (events_bounds b hc.mem_right).2
  by_contra hin
  push_neg at hin
  have hmem := cross_mem_events _ _ (fam_of_offset o₁ h₁) (fam_of_offset o₂ h₂) hs n
    (lt_of_le_of_lt ha hin.1) (lt_of_lt_of_le hin.2 hb)
  exact hc.no_between (events_pairwise 400) _ hmem hin

/-- Between consecutive events the order type and `⌊x⌋` are constant. -/
lemma sameType_of_consec (a b x x' : ℚ) (hc : Consec (events 400) a b) (hx : a < x ∧ x < b)
    (hx' : a < x' ∧ x' < b) : SameType x x' ∧ ⌊x⌋ = ⌊x'⌋ := by
  have hpw := events_pairwise 400
  have ha := (events_bounds a hc.mem_left).1
  have hb := (events_bounds b hc.mem_right).2
  have hnb := hc.no_between hpw
  refine ⟨?_, ?_⟩
  · intro o₁ h₁ o₂ h₂ n
    have hD : ∀ z, offVal z o₁ - offVal z o₂ = ((o₁ : ℚ) / 240 - (o₂ : ℚ) / 240) * z := by
      intro z; simp only [offVal]; ring
    rw [hD, hD]
    rcases lt_trichotomy ((o₁ : ℚ) / 240) ((o₂ : ℚ) / 240) with hs | hs | hs
    · -- decreasing in `z`: use the crossing for `(o₂, o₁)` with `m = -n`
      have hout := cross_not_between a b hc o₂ o₁ h₂ h₁ (-n) hs
      simp only at hout
      set z0 := ((-n : ℤ) : ℚ) / ((o₂ : ℚ) / 240 - (o₁ : ℚ) / 240)
      have hpos : 0 < (o₂ : ℚ) / 240 - (o₁ : ℚ) / 240 := by linarith
      have hne : (o₂ : ℚ) / 240 - (o₁ : ℚ) / 240 ≠ 0 := hpos.ne'
      have hz0 : ((o₂ : ℚ) / 240 - (o₁ : ℚ) / 240) * z0 = -n := by
        simp only [z0]; rw [mul_div_cancel₀ _ hne]; push_cast; ring
      rcases hout with h | h
      · constructor <;> constructor <;> intro <;> nlinarith
      · constructor <;> constructor <;> intro <;> nlinarith
    · rw [hs]; simp
    · have hout := cross_not_between a b hc o₁ o₂ h₁ h₂ n hs
      simp only at hout
      set z0 := (n : ℚ) / ((o₁ : ℚ) / 240 - (o₂ : ℚ) / 240)
      have hpos : 0 < (o₁ : ℚ) / 240 - (o₂ : ℚ) / 240 := by linarith
      have hne : (o₁ : ℚ) / 240 - (o₂ : ℚ) / 240 ≠ 0 := hpos.ne'
      have hz0 : ((o₁ : ℚ) / 240 - (o₂ : ℚ) / 240) * z0 = n := by
        simp only [z0]; rw [mul_div_cancel₀ _ hne]
      rcases hout with h | h
      · constructor <;> constructor <;> intro <;> nlinarith
      · constructor <;> constructor <;> intro <;> nlinarith
  · have key : ∀ u v : ℚ, a < u ∧ u < b → a < v ∧ v < b → ⌊u⌋ ≤ ⌊v⌋ := by
      intro u v hu hv
      apply Int.le_floor.2
      have h1 : 1 ≤ ⌊u⌋ := Int.le_floor.2 (by push_cast; linarith)
      have hfu := Int.floor_le u
      have h2 : ⌊u⌋ ≤ 400 := by
        have : (⌊u⌋ : ℚ) ≤ 400 := by linarith
        exact_mod_cast this
      have hmem := int_mem_events ⌊u⌋ h1 h2
      have := hnb _ hmem
      by_contra hlt
      push_neg at hlt
      exact this ⟨by linarith, by linarith⟩
    exact le_antisymm (key x x' hx hx') (key x' x hx' hx)

/-- **Step-function property (PROOF_ZETA §5.3).** For consecutive events `a < b` and any
`x ∈ (a, b)`: `gfun(x, y) ≤ eStarInt((a+b)/2)` for all `0 ≤ y ≤ x`. -/
theorem gfun_le_eStarInt_mid (a b : ℚ) (hc : Consec (events 400) a b) (x : ℚ) (hax : a < x)
    (hxb : x < b) (y : ℚ) (hy0 : 0 ≤ y) (hyx : y ≤ x) : gfun x y ≤ eStarInt ((a + b) / 2) := by
  have hab := hc.lt (events_pairwise 400)
  have hm : a < (a + b) / 2 ∧ (a + b) / 2 < b := ⟨by linarith, by linarith⟩
  obtain ⟨hst, -⟩ := sameType_of_consec a b x ((a + b) / 2) hc ⟨hax, hxb⟩ hm
  exact gfun_le_eStarInt_of_sameType x _ hst y hy0 hyx

end ZetaIrr.Z7.CertA
