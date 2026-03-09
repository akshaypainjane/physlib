/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib

/-! # Majorization and weak log-majorization

This file develops the theory of majorization for finite sequences, leading to
the key singular value inequality needed for the Schatten–Hölder inequality.

## Main results

* `sum_rpow_singularValues_mul_le`: for `r > 0`, the singular values of `A * B`
  satisfy `∑ σᵢ(AB)^r ≤ ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r`.
* `holder_step_for_singularValues`: the Hölder step giving
  `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σᵢ(A)^p)^{r/p} · (∑ σᵢ(B)^q)^{r/q}`.
-/

open Finset BigOperators Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section

/-! ## Sorted singular values -/

/-- The singular values of a square complex matrix `A`, defined as the square
roots of the eigenvalues of `A†A`. These are indexed by `d` without a
particular ordering.

Note: We use `A.conjTranspose` as the argument to `isHermitian_mul_conjTranspose_self`
so that the underlying Hermitian matrix is `A† * A` (matching the convention in `schattenNorm`). -/
def singularValues (A : Matrix d d ℂ) : d → ℝ :=
  fun i => Real.sqrt ((isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i)

/-- Singular values are nonneg. -/
lemma singularValues_nonneg (A : Matrix d d ℂ) (i : d) :
    0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

/-- The sorted singular values of a square complex matrix, in decreasing order,
indexed by `Fin (Fintype.card d)`.

We define them by sorting the multiset of singular values. -/
noncomputable def singularValuesSorted (A : Matrix d d ℂ) :
    Fin (Fintype.card d) → ℝ :=
  fun i =>
    let vals : Multiset ℝ := Finset.univ.val.map (singularValues A)
    let sorted := vals.sort (· ≥ ·)
    sorted.get ⟨i.val, by rw [Multiset.length_sort]; show i.val < (Multiset.map (singularValues A) univ.val).card; rw [Multiset.card_map]; simp [Finset.card_univ]⟩

/-- Sorted singular values are nonneg. -/
lemma singularValuesSorted_nonneg (A : Matrix d d ℂ) (i : Fin (Fintype.card d)) :
    0 ≤ singularValuesSorted A i := by
  have h_nonneg : ∀ i, 0 ≤ (singularValues A i) := by
    exact singularValues_nonneg A;
  have h_sorted_nonneg : ∀ {l : List ℝ}, (∀ x ∈ l, 0 ≤ x) → ∀ i < l.length, 0 ≤ l[i]! := by
    aesop;
  contrapose! h_sorted_nonneg;
  use Multiset.sort (· ≥ ·) (Finset.univ.val.map (singularValues A));
  refine' ⟨ _, i, _, _ ⟩;
  · aesop;
  · simp [ Finset.card_univ ];
  · convert h_sorted_nonneg using 1;
    unfold singularValuesSorted; aesop;

/-- The sum `∑ singularValues A i ^ p` equals the sum over sorted singular values. -/
lemma sum_singularValues_rpow_eq_sum_sorted (A : Matrix d d ℂ) (p : ℝ) :
    ∑ i : d, singularValues A i ^ p =
    ∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p := by
  have h_perm : Multiset.map (fun i => singularValues A i) Finset.univ.val = Multiset.map (fun i => singularValuesSorted A i) Finset.univ.val := by
    have h_multiset : Multiset.map (fun i => singularValues A i) Finset.univ.val = Multiset.sort (fun i j => j ≤ i) (Multiset.map (fun i => singularValues A i) Finset.univ.val) := by
      aesop;
    convert h_multiset using 1;
    refine' congr_arg _ ( List.ext_get _ _ ) <;> simp [ singularValuesSorted ];
  have h_sum_eq : Multiset.sum (Multiset.map (fun x => x ^ p) (Multiset.map (fun i => singularValues A i) Finset.univ.val)) = Multiset.sum (Multiset.map (fun x => x ^ p) (Multiset.map (fun i => singularValuesSorted A i) Finset.univ.val)) := by
    rw [h_perm];
  convert h_sum_eq using 1;
  · erw [ Multiset.map_map, Finset.sum_eq_multiset_sum ];
    rfl;
  · simp [ Finset.sum ];
    rfl

/-! ## Key singular value inequality for products

The deep result: for `r > 0`,
  `∑ σᵢ(AB)^r ≤ ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r`.

This follows from weak log-majorization of singular values of products
(Horn's inequality), combined with the implication from weak log-majorization
to weak majorization of powers.

### Proof outline

The proof can be decomposed into three independent pieces:

1. **Sorted singular values are antitone**: `singularValuesSorted A` is
   decreasing, by the sorting construction.

2. **Horn's inequality (weak log-majorization)**:
   For all `k`, `∏_{i<k} σ↓ᵢ(AB) ≤ ∏_{i<k} σ↓ᵢ(A) · σ↓ᵢ(B)`.

   *Proof via compound matrices*: The largest singular value of the k-th
   exterior power `∧^k(M)` equals `∏_{i<k} σ↓ᵢ(M)`. Since exterior powers
   are multiplicative (`∧^k(AB) = ∧^k(A) · ∧^k(B)`) and operator norms are
   submultiplicative, we get
     `∏_{i<k} σ↓ᵢ(AB) = σ₁(∧^k(AB)) ≤ σ₁(∧^k(A)) · σ₁(∧^k(B)) = ∏_{i<k} σ↓ᵢ(A) · ∏_{i<k} σ↓ᵢ(B)`.

3. **From weak log-majorization to sum inequality**:
   If nonneg decreasing sequences satisfy `∏_{i<k} xᵢ ≤ ∏_{i<k} yᵢ`
   for all `k`, then for `r > 0`, `∑ xᵢ^r ≤ ∑ yᵢ^r`.

   This follows from the Schur-convexity of `∑ tᵢ^r` on the nonneg cone,
   or equivalently by an inductive argument using the AM-GM inequality.

Combining these gives `∑ σ↓ᵢ(AB)^r ≤ ∑ (σ↓ᵢ(A) · σ↓ᵢ(B))^r = ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r`.
-/
lemma sum_rpow_singularValues_mul_le (A B : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
    ∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ r ≤
    ∑ i : Fin (Fintype.card d),
      (singularValuesSorted A i ^ r * singularValuesSorted B i ^ r) := by
  sorry

/-! ## Hölder inequality step -/

/--
The finite-sum Hölder inequality applied to sequences of r-th powers of
sorted singular values.

With conjugate exponents `p' = p/r > 1` and `q' = q/r > 1` (which satisfy
`1/p' + 1/q' = 1` when `1/r = 1/p + 1/q`), this gives:
  `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q}`

Note: The sums on the RHS don't depend on the ordering, so we can replace
sorted singular values with unsorted ones.
-/
lemma holder_step_for_singularValues (A B : Matrix d d ℂ)
    {r p q : ℝ} (hr : 0 < r) (hp : 0 < p) (hq : 0 < q)
    (hpqr : 1 / r = 1 / p + 1 / q) :
    (∑ i : Fin (Fintype.card d),
      (singularValuesSorted A i ^ r * singularValuesSorted B i ^ r)) ≤
    (∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) ^ (r / p) *
    (∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ q) ^ (r / q) := by
  -- Apply Hölder's inequality with p' = p/r and q' = q/r.
  have h_holder : (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) * (singularValuesSorted B i ^ r)) ≤ (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) ^ (p / r)) ^ (r / p) * (∑ i : Fin (Fintype.card d), (singularValuesSorted B i ^ r) ^ (q / r)) ^ (r / q) := by
    have := @Real.inner_le_Lp_mul_Lq;
    convert @this ( Fin ( Fintype.card d ) ) Finset.univ ( fun i => singularValuesSorted A i ^ r ) ( fun i => singularValuesSorted B i ^ r ) ( p / r ) ( q / r ) _ using 1 <;> norm_num [ hr.ne', hp.ne', hq.ne', div_eq_mul_inv ];
    · simp only [abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg A _) _),
              abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg B _) _)];
    · constructor <;> norm_num [ hr.ne', hp.ne', hq.ne' ] at hpqr ⊢ <;> ring_nf at hpqr ⊢ <;> nlinarith [ inv_pos.2 hr, inv_pos.2 hp, inv_pos.2 hq, mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ hp.ne', mul_inv_cancel₀ hq.ne' ];
  convert h_holder using 3 <;> push_cast [ ← Real.rpow_mul ( singularValuesSorted_nonneg _ _ ), mul_div_cancel₀ _ hr.ne' ] <;> ring_nf

end
