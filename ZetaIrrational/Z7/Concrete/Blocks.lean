/-
# Instance Z7: block bookkeeping

Facts about the block-membership count `Z7.Bk` (PROOF_ZETA §1):
* `prod_blocks`: `Π_j (Π_{k ∈ block j} x_k)^{m_j} = Π_{k ≤ n} x_k^{B_k}` (any commutative monoid);
* `Bk_le`: `B_k ≤ S = 18`; `Bk_mirror`: `B_{n-k} = B_k`;
* `sum_Bk`: `Σ_{k ≤ n} B_k = 3294(m+1) + 18` (even);
* `Bk_zero_of_lt`: no block contains `k < 3(m+1)` (so there is no pole at `0`).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Concrete.Data

namespace ZetaIrr.Z7

open Finset
open scoped BigOperators

/-- The index interval of block `b = (k, m_j)`: `[3k(m+1), n - 3k(m+1)]`. -/
def blk (m : ℕ) (b : ℕ × ℕ) : Finset ℕ := Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))

lemma Bk_eq (m k : ℕ) : Bk m k = (blocks.map (fun b => if k ∈ blk m b then b.2 else 0)).sum := by
  simp only [Bk, blk, Finset.mem_Icc]

/-- Reorganising a product of block products (general list version). -/
lemma prod_list_blocks {M : Type*} [CommMonoid M] (x : ℕ → M) (I : ℕ × ℕ → Finset ℕ)
    (U : Finset ℕ) (L : List (ℕ × ℕ)) (hsub : ∀ b ∈ L, I b ⊆ U) :
    (L.map (fun b => (∏ k ∈ I b, x k) ^ b.2)).prod
      = ∏ k ∈ U, x k ^ (L.map (fun b => if k ∈ I b then b.2 else 0)).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, Finset.prod_mul_distrib]
    rw [ih (fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    simp only [pow_ite, pow_zero]
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr (hsub b (List.mem_cons_self ..)),
      Finset.prod_pow]

/-- Additive version: counting with multiplicity. -/
lemma sum_list_blocks (I : ℕ × ℕ → Finset ℕ) (U : Finset ℕ) (L : List (ℕ × ℕ))
    (hsub : ∀ b ∈ L, I b ⊆ U) :
    ∑ k ∈ U, (L.map (fun b => if k ∈ I b then b.2 else 0)).sum
      = (L.map (fun b => b.2 * (I b).card)).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih (fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub b (List.mem_cons_self ..)),
      Finset.sum_const, smul_eq_mul, mul_comm]

lemma blocks_fst_le : ∀ b ∈ blocks, b.1 ≤ 18 := by decide

lemma blocks_fst_ge : ∀ b ∈ blocks, 1 ≤ b.1 := by decide

lemma blocks_snd : ∀ b ∈ blocks, b.2 = 1 := by decide

lemma blk_subset (m : ℕ) : ∀ b ∈ blocks, blk m b ⊆ range (nOf m + 1) := by
  intro b _ k hk
  simp only [blk, Finset.mem_Icc] at hk
  simp only [Finset.mem_range]
  omega

/-- The block product equals `Π_{k ≤ n} x_k^{B_k}`. -/
lemma prod_blocks {M : Type*} [CommMonoid M] (m : ℕ) (x : ℕ → M) :
    (blocks.map (fun b => (∏ k ∈ blk m b, x k) ^ b.2)).prod
      = ∏ k ∈ range (nOf m + 1), x k ^ Bk m k := by
  rw [prod_list_blocks x (blk m) _ blocks (blk_subset m)]
  simp only [Bk_eq]

lemma list_sum_ite_le (L : List (ℕ × ℕ)) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (L.map (fun b => if P b then b.2 else 0)).sum ≤ (L.map Prod.snd).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (if P b then b.2 else 0) ≤ b.2 := by split_ifs <;> omega
    omega

/-- `B_k ≤ S = 18`. -/
lemma Bk_le (m k : ℕ) : Bk m k ≤ 18 := by
  rw [Bk, ← S_eq]
  exact list_sum_ite_le blocks _

lemma mem_blk_iff (m : ℕ) (b : ℕ × ℕ) (k : ℕ) :
    k ∈ blk m b ↔ 3 * b.1 * (m + 1) ≤ k ∧ k ≤ nOf m - 3 * b.1 * (m + 1) := by
  simp [blk]

/-- Mirror symmetry of the block counts: `B_{n-k} = B_k`. -/
lemma Bk_mirror (m k : ℕ) (hk : k ≤ nOf m) : Bk m (nOf m - k) = Bk m k := by
  rw [Bk_eq, Bk_eq]
  congr 1
  refine List.map_congr_left (fun b hb => ?_)
  have h18 := blocks_fst_le b hb
  have hn : nOf m = 240 * (m + 1) := rfl
  have hiff : nOf m - k ∈ blk m b ↔ k ∈ blk m b := by
    have hq : 3 * b.1 * (m + 1) ≤ nOf m := by rw [hn]; nlinarith
    simp only [blk, Finset.mem_Icc]
    generalize 3 * b.1 * (m + 1) = q at *
    omega
  simp only [hiff]

/-- No block contains `k < 3(m+1)`. -/
lemma Bk_zero_of_lt (m k : ℕ) (hk : k < 3 * (m + 1)) : Bk m k = 0 := by
  rw [Bk_eq]
  have : ∀ b ∈ blocks, (if k ∈ blk m b then b.2 else 0) = 0 := by
    intro b hb
    have h1 := blocks_fst_ge b hb
    have : k ∉ blk m b := by
      rw [mem_blk_iff]
      have : 3 * (m + 1) ≤ 3 * b.1 * (m + 1) := by nlinarith
      omega
    simp [this]
  rw [List.map_congr_left this]
  simp

/-- `Σ_{k ≤ n} B_k = 3294(m+1) + 18`. -/
lemma sum_Bk (m : ℕ) : ∑ k ∈ range (nOf m + 1), Bk m k = 3294 * (m + 1) + 18 := by
  simp only [Bk_eq]
  rw [sum_list_blocks (blk m) _ blocks (blk_subset m)]
  simp only [blocks, blk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.card_Icc,
    nOf]
  omega

end ZetaIrr.Z7
