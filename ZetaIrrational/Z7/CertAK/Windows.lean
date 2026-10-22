/-
# The A-certificate for Z7: the event list, window by window

`events 400` is too large to sort in a single kernel computation. We cut `[1, 400]`
into the 133 windows `[bnd j, bnd (j+1))`, `bnd j = 1 + 3j`, and sort each window separately:
`win j` is the sorted, deduplicated list of the cuts in `[bnd j, bnd (j+1))` and the crossings in
`(bnd j, bnd (j+1))`.

* `mem_crossings_iff` — membership in `crossings lo hi` (the `m`-range of `crossPair` is complete);
* `mem_winList` — the members of `(range 133).flatMap win ++ [400]` are exactly the cuts and the
  crossings in `[1, 400]`, i.e. the members of `events 400`;
* `events_eq_of_windows` — if each `win j` equals a given list and the concatenation is strictly
  increasing, then `events 400` is that concatenation;
* `pairSum_flatten` — splitting `pairSum` over chunks (`chunkSums`).

The kernel checks themselves are in the generated files `Z7/CertAK/EvData.lean`, `Z7/CertAK/EvWin*.lean`
and `Z7/CertAK/EvSum*.lean`.
-/
import ZetaIrrational.Z7.CertA.Step
import ZetaIrrational.Z7.CertAK.EvSort

namespace ZetaIrr.Z7.CertA

/-! ## Crossings -/

lemma mem_crossPair_iff (lo hi z : ℚ) (s₁ s₂ : ℚ) :
    z ∈ crossPair lo hi s₁ s₂ ↔ s₂ < s₁ ∧ lo < z ∧ z < hi ∧
      ∃ m : ℤ, z = (m : ℚ) / (s₁ - s₂) := by
  unfold crossPair
  split_ifs with hs
  · simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨i, -, rfl⟩, h1, h2⟩
      exact ⟨hs, h1, h2, _, rfl⟩
    · rintro ⟨-, hz1, hz2, m, rfl⟩
      have hds : 0 < s₁ - s₂ := by linarith
      have hz1' := hz1
      have hz2' := hz2
      rw [lt_div_iff₀ hds] at hz1'
      rw [div_lt_iff₀ hds] at hz2'
      have hm0 : ⌊lo * (s₁ - s₂)⌋ ≤ m := by
        have := Int.floor_le (lo * (s₁ - s₂))
        have : ((⌊lo * (s₁ - s₂)⌋ : ℤ) : ℚ) < m := by linarith
        exact_mod_cast this.le
      have hm1 : m ≤ ⌈hi * (s₁ - s₂)⌉ := by
        have := Int.le_ceil (hi * (s₁ - s₂))
        have : (m : ℚ) < ⌈hi * (s₁ - s₂)⌉ := by linarith
        exact_mod_cast this.le
      refine ⟨⟨(m - ⌊lo * (s₁ - s₂)⌋).toNat, by omega, ?_⟩, hz1, hz2⟩
      have hnn : 0 ≤ m - ⌊lo * (s₁ - s₂)⌋ := by omega
      have hi' : ⌊lo * (s₁ - s₂)⌋ +
          (((m - ⌊lo * (s₁ - s₂)⌋).toNat : ℕ) : ℤ) = m := by
        rw [Int.toNat_of_nonneg hnn]; ring
      rw [hi']
  · simp only [List.not_mem_nil, false_iff, not_and]
    intro h; exact absurd h hs

lemma mem_crossings_iff (lo hi z : ℚ) :
    z ∈ crossings lo hi ↔ lo < z ∧ z < hi ∧ ∃ s₁ ∈ fams, ∃ s₂ ∈ fams, s₂ < s₁ ∧
      ∃ m : ℤ, z = (m : ℚ) / (s₁ - s₂) := by
  unfold crossings
  simp only [List.mem_flatMap, mem_crossPair_iff]
  constructor
  · rintro ⟨s₁, h₁, s₂, h₂, hs, hz1, hz2, hm⟩
    exact ⟨hz1, hz2, s₁, h₁, s₂, h₂, hs, hm⟩
  · rintro ⟨hz1, hz2, s₁, h₁, s₂, h₂, hs, hm⟩
    exact ⟨s₁, h₁, s₂, h₂, hs, hz1, hz2, hm⟩

lemma crossings_restrict (lo hi lo' hi' z : ℚ) (hz : z ∈ crossings lo hi) (h1 : lo' < z)
    (h2 : z < hi') : z ∈ crossings lo' hi' := by
  rw [mem_crossings_iff] at hz ⊢
  exact ⟨h1, h2, hz.2.2⟩

/-! ## Cuts -/

lemma cuts_bounds (z : ℚ) (hz : z ∈ cuts 400) : 1 ≤ z ∧ z ≤ 400 :=
  events_bounds z ((mem_events 400 z).2 (Or.inl hz))

lemma int_mem_cuts (n : ℤ) (h1 : 1 ≤ n) (h2 : n ≤ 400) : (n : ℚ) ∈ cuts 400 := by
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

/-! ## Windows -/

/-- Window boundaries `bnd j = 1 + 3j` (`bnd 133 = 400`). -/
def bnd (j : ℕ) : ℚ := 1 + 3 * (j : ℚ)

/-- The events in the window `[bnd j, bnd (j+1))`, sorted and deduplicated. -/
def win (j : ℕ) : List ℚ :=
  dedupAdj (msort qleN 20 ((cuts 400).filter (fun z => decide (bnd j ≤ z ∧ z < bnd (j + 1))) ++
    crossings (bnd j) (bnd (j + 1))))

lemma mem_win (j : ℕ) (z : ℚ) :
    z ∈ win j ↔ (z ∈ cuts 400 ∧ bnd j ≤ z ∧ z < bnd (j + 1)) ∨
      z ∈ crossings (bnd j) (bnd (j + 1)) := by
  unfold win
  rw [mem_dedupAdj, mem_msort, List.mem_append, List.mem_filter]
  simp only [decide_eq_true_eq]

lemma exists_win (z : ℚ) (h1 : 1 ≤ z) (h2 : z < 400) :
    ∃ j < 133, bnd j ≤ z ∧ z < bnd (j + 1) := by
  set t := ⌊(z - 1) / 3⌋ with ht
  have ht0 : 0 ≤ t := Int.floor_nonneg.2 (by linarith)
  have hle := Int.floor_le ((z - 1) / 3)
  have hlt := Int.lt_floor_add_one ((z - 1) / 3)
  rw [← ht] at hle hlt
  have ht133 : t < 133 := by
    have : (t : ℚ) < 133 := by linarith
    exact_mod_cast this
  refine ⟨t.toNat, by omega, ?_, ?_⟩
  · have : ((t.toNat : ℕ) : ℚ) = t := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg ht0]
    simp only [bnd, this]; linarith
  · have : ((t.toNat + 1 : ℕ) : ℚ) = t + 1 := by
      push_cast; rw [← Int.cast_natCast, Int.toNat_of_nonneg ht0]
    simp only [bnd, this]; linarith

lemma bnd_ge (j : ℕ) : 1 ≤ bnd j := by
  unfold bnd; have : (0 : ℚ) ≤ j := by positivity
  linarith

lemma bnd_le (j : ℕ) (hj : j ≤ 133) : bnd j ≤ 400 := by
  unfold bnd; have : (j : ℚ) ≤ 133 := by exact_mod_cast hj
  linarith

/-- The concatenation of the windows, with the final point `400`. -/
def winList : List ℚ := (List.range 133).flatMap win ++ [400]

lemma mem_winList (z : ℚ) : z ∈ winList ↔ z ∈ cuts 400 ∨ z ∈ crossings 1 400 := by
  unfold winList
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton]
  constructor
  · rintro (⟨j, hj, hz⟩ | rfl)
    · rcases (mem_win j z).1 hz with hz | hz
      · exact Or.inl hz.1
      · right
        have hb := (mem_crossings_iff _ _ _).1 hz
        exact crossings_restrict _ _ _ _ _ hz (by linarith [bnd_ge j, hb.1])
          (by linarith [bnd_le (j + 1) (by omega), hb.2.1])
    · left
      have := int_mem_cuts 400 (by norm_num) le_rfl
      simpa using this
  · rintro (hz | hz)
    · obtain ⟨h1, h2⟩ := cuts_bounds z hz
      rcases eq_or_lt_of_le h2 with h | h
      · exact Or.inr h
      · obtain ⟨j, hj, hj1, hj2⟩ := exists_win z h1 h
        exact Or.inl ⟨j, hj, (mem_win j z).2 (Or.inl ⟨hz, hj1, hj2⟩)⟩
    · have hb := (mem_crossings_iff _ _ _).1 hz
      obtain ⟨j, hj, hj1, hj2⟩ := exists_win z hb.1.le (by exact_mod_cast hb.2.1)
      left
      refine ⟨j, hj, (mem_win j z).2 ?_⟩
      rcases eq_or_lt_of_le hj1 with h | h
      · left
        refine ⟨?_, hj1, hj2⟩
        rw [← h]
        have := int_mem_cuts (1 + 3 * j) (by omega) (by omega)
        simpa [bnd] using this
      · right
        exact crossings_restrict _ _ _ _ _ hz h hj2

/-- **The event list, from the windows.** If `win j = W j` for all `j < 133` and the concatenation
of the `W j` (followed by `400`) is strictly increasing, then it is `events 400`. -/
theorem events_eq_of_windows (W : ℕ → List ℚ) (hW : ∀ j < 133, win j = W j)
    (hs : sortedLT ((List.range 133).flatMap W ++ [400]) = true) :
    events 400 = (List.range 133).flatMap W ++ [400] := by
  have hE : winList = (List.range 133).flatMap W ++ [400] := by
    unfold winList
    congr 1
    apply List.flatMap_congr
    intro j hj
    exact hW j (List.mem_range.1 hj)
  rw [← hE] at hs ⊢
  apply eq_of_pairwise_lt _ _ (events_pairwise 400) (pairwise_of_sortedLT _ hs)
  intro z
  rw [mem_events, mem_winList]
  norm_num

/-! ## Splitting `pairSum` into chunks -/

/-- The first point after the chunks `cs` (or `z` if there are none). -/
def nextHead : List (List ℚ) → ℚ → ℚ
  | [], z => z
  | c :: _, z => c.headD z

/-- `Σ_i pairSum g (c_i ++ [first point of c_{i+1}])`. -/
def chunkSums (g : ℚ → ℚ → ℤ) : List (List ℚ) → ℚ → ℤ
  | [], _ => 0
  | c :: cs, z => pairSum g (c ++ [nextHead cs z]) + chunkSums g cs z

lemma pairSum_append_cons (g : ℚ → ℚ → ℤ) :
    ∀ (A : List ℚ) (b : ℚ) (R : List ℚ),
      pairSum g (A ++ b :: R) = pairSum g (A ++ [b]) + pairSum g (b :: R)
  | [], b, R => by simp [pairSum]
  | [a], b, R => by simp [pairSum]
  | a :: a' :: A, b, R => by
    have ih := pairSum_append_cons g (a' :: A) b R
    simp only [List.cons_append] at ih ⊢
    rw [pairSum, pairSum, ih]
    ring

lemma pairSum_flatten (g : ℚ → ℚ → ℤ) :
    ∀ (cs : List (List ℚ)) (z : ℚ), (∀ c ∈ cs, c ≠ []) →
      pairSum g (cs.flatten ++ [z]) = chunkSums g cs z
  | [], z, _ => by simp [pairSum, chunkSums]
  | c :: cs, z, h => by
    have ih := pairSum_flatten g cs z (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have hR : ∃ R, cs.flatten ++ [z] = nextHead cs z :: R := by
      cases cs with
      | nil => exact ⟨[], rfl⟩
      | cons c' cs' =>
        have hc' : c' ≠ [] := h c' (List.mem_cons_of_mem _ List.mem_cons_self)
        obtain ⟨b, B, rfl⟩ := List.exists_cons_of_ne_nil hc'
        exact ⟨B ++ cs'.flatten ++ [z], by simp [nextHead]⟩
    obtain ⟨R, hR⟩ := hR
    rw [chunkSums, ← ih, List.flatten_cons, List.append_assoc, hR, pairSum_append_cons, ← hR]

lemma flatMap_range_getD (ws : List (List (List ℚ))) :
    (List.range ws.length).flatMap (fun j => (ws.getD j []).flatten) = ws.flatten.flatten := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Function.comp_def]
    rw [ih, List.flatten_cons, List.flatten_append]

end ZetaIrr.Z7.CertA
