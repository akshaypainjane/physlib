/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib
import QuantumInfo.ForMathlib.Matrix

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

/-! ## Weak log-majorization and its consequences -/

/-- Sorted singular values are antitone (decreasing). -/
lemma singularValuesSorted_antitone (A : Matrix d d ℂ) :
    Antitone (singularValuesSorted A) := by
  intro i j hij
  have h_sorted : List.Sorted (· ≥ ·) (Finset.univ.val.map (singularValues A) |>.sort (· ≥ ·)) := by
    exact Multiset.sort_sorted _ _
  exact h_sorted.rel_get_of_le hij

/-- The product of nonneg antitone sequences is antitone. -/
lemma antitone_mul_of_antitone_nonneg {n : ℕ}
    {f g : Fin n → ℝ} (hf : Antitone f) (hg : Antitone g)
    (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) :
    Antitone (fun i => f i * g i) := by
  exact fun i j hij => mul_le_mul (hf hij) (hg hij) (hg_nn _) (hf_nn _)

/-! ### Compound matrices and auxiliary lemmas for Horn's inequality

The proof of Horn's inequality uses the *compound matrix* (or *k-th exterior power*
of a matrix).  For a `d × d` matrix `M` and `k ≤ card d`, the `k`-th compound matrix
`C_k(M)` is indexed by `k`-element subsets of the index type, with entry `(S, T)` being
the minor `det M[S, T]`.

The key properties are:
1. **Cauchy–Binet**: `C_k(M N) = C_k(M) · C_k(N)`.
2. **Spectral characterisation**: the largest singular value of `C_k(M)` is
   `∏_{i=1}^k σ↓ᵢ(M)`.
3. **Operator-norm submultiplicativity**: `σ₁(A B) ≤ σ₁(A) · σ₁(B)`.

Combining these gives Horn's inequality:
  `∏ σ↓(AB) = σ₁(C_k(AB)) = σ₁(C_k(A) C_k(B)) ≤ σ₁(C_k(A)) σ₁(C_k(B))
            = (∏ σ↓(A))(∏ σ↓(B))`.
-/

/-- A `LinearOrder` on any `Fintype`, obtained classically via well-ordering. -/
noncomputable instance fintypeLinearOrderClassical (α : Type*) [Fintype α] [DecidableEq α] :
    LinearOrder α := by
  classical
  exact linearOrderOfSTO (WellOrderingRel)

/-- The `k`-th compound (exterior-power) matrix of `M`. -/
noncomputable def compoundMatrix (M : Matrix d d ℂ) (k : ℕ) :
    Matrix {S : Finset d // S.card = k} {S : Finset d // S.card = k} ℂ :=
  fun S T =>
    @Matrix.det (Fin k) _ _ ℂ _
      (M.submatrix (fun i => S.1.orderEmbOfFin S.2 i) (fun j => T.1.orderEmbOfFin T.2 j))

/-
PROBLEM
**Cauchy–Binet formula** for rectangular matrices: if `A` is `m × n` and `B` is
`n × m`, then `det(A * B) = ∑_S det(A[:,S]) * det(B[S,:])` where the sum is
over `m`-element subsets `S` of the column/row index.

PROVIDED SOLUTION
Proof follows the same structure as the Mathlib proof of Matrix.det_mul, adapted for rectangular matrices.

Step 1: Expand det(A * B) using Matrix.det_apply' to get:
∑ σ : Perm (Fin m), sign(σ) * ∏ i, (A * B)(i, σ i)
= ∑ σ, sign(σ) * ∏ i, ∑ j, A(i, j) * B(j, σ i)

Step 2: Distribute the product of sums using Finset.prod_sum (which converts ∏ i, ∑ j to ∑ over pi-type). This gives:
= ∑ σ, sign(σ) * ∑ f (in the pi type Fin m → n), ∏ i, A(i, f(i)) * B(f(i), σ i)

Step 3: Swap the two sums (by Finset.sum_comm):
= ∑ f, ∑ σ, sign(σ) * ∏ i, A(i, f(i)) * B(f(i), σ i)

Step 4: Split the product and factor out the A part (which doesn't depend on σ):
= ∑ f, (∏ i, A(i, f(i))) * (∑ σ, sign(σ) * ∏ i, B(f(i), σ i))
= ∑ f, (∏ i, A(i, f(i))) * det(B.submatrix f id)

Step 5: For non-injective f, det(B.submatrix f id) = 0 (since B.submatrix f id has two equal rows). Use Matrix.det_zero_of_row_eq with the witnesses from Function.not_injective_iff.

Step 6: For injective f, group by the image set S = range(f). Each injective f : Fin m → n with image S factors uniquely as f = (S.orderEmbOfFin hS) ∘ τ where τ is a permutation of Fin m determined by the ordering.

Then det(B.submatrix f id) = det(B.submatrix ((S.orderEmbOfFin hS) ∘ τ) id) = det((B.submatrix (S.orderEmbOfFin hS) id).submatrix τ id) = sign(τ) * det(B.submatrix (S.orderEmbOfFin hS) id) by Matrix.det_permute.

And ∏ i, A(i, f(i)) = ∏ i, A(i, (S.orderEmbOfFin hS)(τ i)).

Step 7: Summing over all τ:
∑ τ, (∏ i, A(i, eS(τ i))) * sign(τ) * det(B.submatrix eS id)
= (∑ τ, sign(τ) * ∏ i, A(i, eS(τ i))) * det(B.submatrix eS id)
= det(A.submatrix id eS) * det(B.submatrix eS id)

where the last step uses the Leibniz formula det(A.submatrix id eS) = ∑ τ, sign(τ) * ∏ i, (A.submatrix id eS)(i, τ i) = ∑ τ, sign(τ) * ∏ i, A(i, eS(τ i)).

Step 8: Summing over all S gives the Cauchy-Binet formula. QED.
-/
set_option maxHeartbeats 1600000 in
lemma cauchyBinet {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    {R : Type*} [CommRing R]
    (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset n // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
      (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  have h_cauchy_binet : ∀ (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R), Matrix.det (A * B) = ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) := by
    simp +decide [ Matrix.det_apply' ];
    simp +decide [ Matrix.mul_apply, Finset.prod_mul_distrib, Finset.mul_sum _ _ _ ];
    intro A B; rw [ ← Finset.sum_comm ] ; congr; ext x; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.prod_mul_distrib ] ;
    simp +decide only [prod_sum, sum_mul];
    refine' Finset.sum_bij ( fun f _ => fun i => f ( x.symm i ) ( Finset.mem_univ _ ) ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
    · simp +decide [ funext_iff ];
      exact fun a₁ a₂ h i => by simpa using h ( x i ) ;
    · exact fun b => ⟨ fun i _ => b ( x i ), by ext i; simp +decide ⟩;
    · intro a; rw [ ← Equiv.prod_comp x.symm ] ; ring;
      rw [ ← Equiv.prod_comp x.symm ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      conv_rhs => rw [ ← Equiv.prod_comp x ] ;
      simp +decide [ Equiv.symm_apply_apply ];
  -- Split the sum into injective and non-injective functions.
  have h_split : ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) = ∑ σ : Fin m → n, if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0 := by
    refine' Finset.sum_congr rfl fun σ _ => _;
    split_ifs with hσ <;> simp_all +decide [ Function.Injective, Matrix.det_zero_of_row_eq ] ;
    obtain ⟨ i, j, hij, hne ⟩ := hσ; exact mul_eq_zero_of_right _ ( Matrix.det_zero_of_row_eq hne ( by aesop ) ) ;
  -- Group the sum by the image of the injective functions.
  have h_group : ∑ σ : Fin m → n, (if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) := by
    rw [ ← Finset.sum_comm, Finset.sum_congr rfl ];
    intro σ _; by_cases hσ : Function.Injective σ <;> simp +decide [ hσ ] ;
    rw [ Finset.sum_eq_single ⟨ Finset.image σ Finset.univ, by simp +decide [ Finset.card_image_of_injective _ hσ ] ⟩ ] <;> simp +decide [ hσ.eq_iff ];
    grind;
  -- For each subset $S$ of size $m$, the inner sum is equal to the product of the determinants of the submatrices of $A$ and $B$ corresponding to $S$.
  have h_inner : ∀ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = Matrix.det (Matrix.submatrix A id (S.val.orderEmbOfFin S.property)) * Matrix.det (Matrix.submatrix B (S.val.orderEmbOfFin S.property) id) := by
    intro S
    have h_inner_sum : ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ τ : Equiv.Perm (Fin m), (∏ i, A i (S.val.orderEmbOfFin S.property (τ i))) * Matrix.det (Matrix.of (fun i j ↦ B (S.val.orderEmbOfFin S.property (τ i)) j)) := by
      have h_inner_sum : Finset.filter (fun σ : Fin m → n => Function.Injective σ ∧ Finset.image σ Finset.univ = S.val) Finset.univ = Finset.image (fun τ : Equiv.Perm (Fin m) => fun i => S.val.orderEmbOfFin S.property (τ i)) Finset.univ := by
        ext σ; simp [Finset.mem_image];
        constructor;
        · intro hσ
          obtain ⟨a, ha⟩ : ∃ a : Fin m → Fin m, ∀ i, σ i = S.val.orderEmbOfFin S.property (a i) := by
            have h_exists_a : ∀ i, ∃ a : Fin m, σ i = S.val.orderEmbOfFin S.property a := by
              intro i
              have h_exists_a : σ i ∈ S.val := by
                exact hσ.2 ▸ Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
              have h_exists_a : Finset.image (fun a : Fin m => S.val.orderEmbOfFin S.property a) Finset.univ = S.val := by
                refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun a _ => Finset.orderEmbOfFin_mem _ _ _ ) _;
                rw [ Finset.card_image_of_injective _ fun a b h => by simpa [ Fin.ext_iff ] using h ] ; simp +decide [ S.2 ];
              grind;
            exact ⟨ fun i => Classical.choose ( h_exists_a i ), fun i => Classical.choose_spec ( h_exists_a i ) ⟩;
          have ha_inj : Function.Injective a := by
            exact fun i j hij => hσ.1 <| by simp +decide [ ha, hij ] ;
          exact ⟨ Equiv.ofBijective a ⟨ ha_inj, Finite.injective_iff_surjective.mp ha_inj ⟩, funext fun i => ha i ▸ rfl ⟩;
        · rintro ⟨ a, rfl ⟩;
          refine' ⟨ _, _ ⟩;
          · exact fun i j hij => a.injective <| by simpa using hij;
          · refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _ ) _;
            rw [ Finset.card_image_of_injective _ fun i j hij => by simpa [ Fin.ext_iff ] using hij ] ; simp +decide [ S.2 ];
      rw [ ← Finset.sum_filter, h_inner_sum, Finset.sum_image ];
      exact fun τ _ τ' _ h => Equiv.Perm.ext fun i => by simpa using congr_fun h i;
    rw [ h_inner_sum, Matrix.det_apply', Matrix.det_apply' ];
    simp +decide [ Matrix.det_apply', Finset.prod_mul_distrib, Finset.sum_mul ];
    refine' Finset.sum_bij ( fun σ _ => σ⁻¹ ) _ _ _ _ <;> simp +decide [ Equiv.Perm.sign_inv ];
    · exact fun b => ⟨ b⁻¹, inv_inv b ⟩;
    · intro σ; rw [ ← Equiv.prod_comp σ⁻¹ ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
      refine' Finset.sum_bij ( fun τ _ => σ * τ ) _ _ _ _ <;> simp +decide [ Equiv.Perm.sign_mul ];
      · exact fun b => ⟨ σ⁻¹ * b, by simp +decide ⟩;
      · cases' Int.units_eq_one_or ( Equiv.Perm.sign σ ) with h h <;> simp +decide [ h ];
  rw [ h_cauchy_binet, h_split, h_group, Finset.sum_congr rfl fun S hS => h_inner S ]

/-
PROBLEM
**Cauchy–Binet**: the compound of a product is the product of the compounds.

PROVIDED SOLUTION
Use `ext` to reduce to pointwise equality for ⟨S, hS⟩ ⟨T, hT⟩. Then unfold both sides.

LHS: compoundMatrix (M * N) k ⟨S, hS⟩ ⟨T, hT⟩ = det((M * N).submatrix eS eT) where eS = S.orderEmbOfFin hS, eT = T.orderEmbOfFin hT.

RHS: (compoundMatrix M k * compoundMatrix N k) ⟨S,hS⟩ ⟨T,hT⟩ = ∑_U (compoundMatrix M k ⟨S,hS⟩ U) * (compoundMatrix N k U ⟨T,hT⟩) = ∑_U det(M.submatrix eS eU) * det(N.submatrix eU eT)

For the LHS, use Matrix.submatrix_mul with Function.bijective_id to get:
(M * N).submatrix eS eT = (M.submatrix eS id) * (N.submatrix id eT)

Then apply cauchyBinet to get:
det((M.submatrix eS id) * (N.submatrix id eT)) = ∑_U det((M.submatrix eS id).submatrix id eU) * det((N.submatrix id eT).submatrix eU id)

Use Matrix.submatrix_submatrix to simplify:
(M.submatrix eS id).submatrix id eU = M.submatrix (eS ∘ id) (id ∘ eU) = M.submatrix eS eU
(N.submatrix id eT).submatrix eU id = N.submatrix (id ∘ eU) (eT ∘ id) = N.submatrix eU eT

This matches the RHS. QED.
-/
lemma compoundMatrix_mul (M N : Matrix d d ℂ) (k : ℕ) :
    compoundMatrix (M * N) k = compoundMatrix M k * compoundMatrix N k := by
  -- By definition of compound matrix, we can expand both sides.
  ext S T; simp [compoundMatrix];
  convert cauchyBinet _ _ using 3;
  infer_instance

/-
PROBLEM
The compound matrix of the conjugate transpose is the conjugate transpose of
    the compound matrix. This follows from `det(M†[S,T]) = conj(det(M[T,S]))`.

PROVIDED SOLUTION
Need to show: for all S, T (k-subsets of d):
compoundMatrix M† k S T = conj(compoundMatrix M k T S)

LHS = det(M†.submatrix eS eT)
RHS = conj(det(M.submatrix eT eS))

Now M†.submatrix eS eT has entry (i,j) = M†(eS(i), eT(j)) = conj(M(eT(j), eS(i))).
And M.submatrix eT eS has entry (i,j) = M(eT(i), eS(j)).

So M†.submatrix eS eT = (M.submatrix eT eS)†  (conjugate transpose).

Therefore det(M†.submatrix eS eT) = det((M.submatrix eT eS)†) = conj(det(M.submatrix eT eS)) by Matrix.det_conjTranspose.

This proves LHS = RHS.

Key Mathlib lemmas: Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix, and the definition of compoundMatrix.
-/
lemma compoundMatrix_conjTranspose (M : Matrix d d ℂ) (k : ℕ) :
    compoundMatrix M.conjTranspose k = (compoundMatrix M k).conjTranspose := by
  -- By definition of conjugate transpose, we have:
  have h_conj_transpose : ∀ (k : ℕ) (S T : {S : Finset d // S.card = k}), (compoundMatrix Mᴴ k S T) = star (compoundMatrix M k T S) := by
    unfold compoundMatrix;
    intro k S T; rw [ ← Matrix.det_conjTranspose ] ; simp +decide [ Matrix.conjTranspose_submatrix ] ;
  exact?

/-
PROBLEM
The compound matrix of a diagonal matrix is diagonal, with entries being
    products of eigenvalues over k-subsets.

PROVIDED SOLUTION
Need to show: for k-subsets S ≠ T, det(diagonal(f).submatrix eS eT) = 0; and for S = T, det(diagonal(f).submatrix eS eS) = ∏_{i∈Fin k} f(eS(i)).

For S = T: (diagonal f).submatrix eS eS is a diagonal matrix with entries f(eS(i)) on the diagonal. Its determinant is the product of diagonal entries = ∏ f(eS(i)). This follows from Matrix.det_diagonal.

Actually, (diagonal f).submatrix eS eS has entry (i,j) = diagonal(f)(eS(i), eS(j)) = if eS(i) = eS(j) then f(eS(i)) else 0. Since eS is injective (it's an order embedding), eS(i) = eS(j) iff i = j. So (diagonal f).submatrix eS eS = diagonal(f ∘ eS), which is a diagonal matrix.

Therefore det = ∏ i, (f ∘ eS)(i) = ∏ i, f(eS(i)).

For S ≠ T: Need to show the entry is 0, i.e., det(diagonal(f).submatrix eS eT) = 0.
(diagonal f).submatrix eS eT has entry (i,j) = diagonal(f)(eS(i), eT(j)) = if eS(i) = eT(j) then f(eS(i)) else 0.
If S ≠ T, then there exists some row of this submatrix that is all zeros (since eS and eT select different subsets, some eS(i) is not in range(eT), making all entries in that row zero). So the determinant is 0.

Actually, the fact that we need this for ALL S ≠ T is trickier. It's possible that some rows have nonzero entries even when S ≠ T (if S and T overlap). But the determinant is still 0 because the matrix has rank < k when S ≠ T (since the nonzero entries can only occur when eS(i) = eT(j), and since S ≠ T, there's at least one row of S not in T that produces a zero row, or one column of T not in S that produces a zero column).

More precisely: since S ≠ T, there exists i₀ ∈ S \ T. The row corresponding to i₀ in the submatrix has entry (i₀, j) = 0 for all j (since eS(i₀) ∉ range(eT) because eS(i₀) ∈ S but eS(i₀) ∉ T). So the matrix has a zero row, and its determinant is 0. Use Matrix.det_eq_zero_of_row_eq_zero.

Then the whole matrix compoundMatrix (diagonal f) k is diagonal, with the stated entries. Use ext and split on S = T.
-/
lemma compoundMatrix_diagonal (f : d → ℂ) (k : ℕ) :
    compoundMatrix (Matrix.diagonal f) k =
    Matrix.diagonal (fun S : {S : Finset d // S.card = k} =>
      ∏ i : Fin k, f (S.1.orderEmbOfFin S.2 i)) := by
  ext S T; by_cases h : S = T <;> simp_all +decide [ Matrix.diagonal ] ;
  · refine' Matrix.det_of_upperTriangular _ |> fun h => h.trans _;
    · intro i j hij; aesop;
    · aesop;
  · -- Since $S \neq T$, there exists some $i \in S$ such that $i \notin T$.
    obtain ⟨i, hiS, hiT⟩ : ∃ i ∈ S.val, i ∉ T.val := by
      contrapose! h;
      exact Subtype.ext ( Finset.eq_of_subset_of_card_le h ( by simp +decide [ S.2, T.2 ] ) );
    obtain ⟨j, hj⟩ : ∃ j : Fin k, (S.val.orderEmbOfFin S.2) j = i := by
      have h_row_zero : Finset.image (fun j : Fin k => S.val.orderEmbOfFin S.2 j) Finset.univ = S.val := by
        refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun j _ => Finset.orderEmbOfFin_mem _ _ _ ) _ ; simp +decide [ Finset.card_image_of_injective, Function.Injective, * ] ; aesop;
      exact Exists.elim ( Finset.mem_image.mp ( h_row_zero.symm ▸ hiS ) ) fun j hj => ⟨ j, hj.2 ⟩;
    -- Since the row corresponding to $i$ in the submatrix is all zeros, the determinant of this submatrix is zero.
    have h_det_zero : Matrix.det (Matrix.of (fun i j => if (S.val.orderEmbOfFin S.2 i) = (T.val.orderEmbOfFin T.2 j) then f (T.val.orderEmbOfFin T.2 j) else 0) : Matrix (Fin k) (Fin k) ℂ) = 0 := by
      rw [ Matrix.det_eq_zero_of_row_eq_zero j ] ; aesop;
    convert h_det_zero using 1

/-
PROBLEM
The eigenvalues of the compound matrix of a Hermitian matrix are the products
    of eigenvalues over k-subsets. More precisely, the singular values of
    `compoundMatrix M k` are the square roots of products of eigenvalues of M†M
    over k-subsets.

PROVIDED SOLUTION
Use the spectral theorem and the lemma IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal.

Step 1: The singular values of C_k(M) at index j are sqrt(eigenvalue_j of (C_k(M))† * C_k(M)).

Step 2: By compoundMatrix_conjTranspose: (C_k(M))† = C_k(M†).
So (C_k(M))† * C_k(M) = C_k(M†) * C_k(M) = C_k(M† * M) (by compoundMatrix_mul, noting that M†*M = M.conjTranspose * M).

Wait, actually we need to be careful: the definition of singularValues uses isHermitian_mul_conjTranspose_self A.conjTranspose which gives the eigenvalues of A†*(A†)† = A†*A. For compoundMatrix M k, the conjTranspose is compoundMatrix M† k (by compoundMatrix_conjTranspose).

So the eigenvalues used in singularValues (compoundMatrix M k) are the eigenvalues of (compoundMatrix M k)† * (compoundMatrix M k) = compoundMatrix M† k * compoundMatrix M k = compoundMatrix (M† * M) k.

Hmm actually, we need isHermitian_mul_conjTranspose_self (compoundMatrix M k).conjTranspose which gives eigenvalues of (compoundMatrix M k).conjTranspose * ((compoundMatrix M k).conjTranspose).conjTranspose = (compoundMatrix M k)† * (compoundMatrix M k) by the double conjTranspose.

Wait, let me re-read the definition carefully. singularValues A i = sqrt(eigenvalues of (isHermitian_mul_conjTranspose_self A†)). And isHermitian_mul_conjTranspose_self A† proves that A† * (A†)† = A† * A is Hermitian. So the eigenvalues are of A†*A. Good.

For A = compoundMatrix M k:
A†*A = (compoundMatrix M k)† * compoundMatrix M k
= compoundMatrix M† k * compoundMatrix M k  (by compoundMatrix_conjTranspose)
= compoundMatrix (M† * M) k  (by compoundMatrix_mul, since M.conjTranspose * M = M†*M)

Wait, but compoundMatrix_mul says C_k(P*Q) = C_k(P) * C_k(Q). So C_k(M†) * C_k(M) = C_k(M† * M). ✓

Step 3: M†*M is Hermitian. By the spectral theorem:
M†*M = U * diag(λ) * U† where λ = eigenvalues of M†*M and U = eigenvectorUnitary.

Step 4: C_k(M†*M) = C_k(U * diag(λ) * U†) = C_k(U) * C_k(diag(λ)) * C_k(U†) (by compoundMatrix_mul twice, treating M†*M = (U * diag(λ)) * U†, so C_k = C_k(U * diag(λ)) * C_k(U†), and then C_k(U * diag(λ)) = C_k(U) * C_k(diag(λ))).

Step 5: C_k(U†) = (C_k(U))† (by compoundMatrix_conjTranspose, since U† = U.conjTranspose).

Step 6: C_k(diag(λ)) is diagonal with entries ∏_{i∈S} λ_i (by compoundMatrix_diagonal, with f = RCLike.ofReal ∘ eigenvalues).

Step 7: So (C_k(M))† * C_k(M) = C_k(U) * diag(∏ λ) * (C_k(U))†. This is a unitary similarity, so by IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal, the eigenvalues of (C_k(M))† * C_k(M) are a permutation of {∏_{i∈S} λ_i : S k-subset}.

Step 8: The singular values of C_k(M) at index j = sqrt(eigenvalue_j of (C_k(M))†*C_k(M)).
For each k-subset S, there exists j such that eigenvalue_j = ∏_{i∈S} λ_i.
So singularValues(C_k(M)) at some j = sqrt(∏ λ_i) = ∏ sqrt(λ_i) = ∏ singularValues(M)(eS(i)).

The last step uses that λ_i are nonneg (eigenvalues of M†M are nonneg), so sqrt(∏ λ_i) = ∏ sqrt(λ_i).

Key Mathlib lemmas:
- isHermitian_mul_conjTranspose_self for Hermitian proof
- Matrix.IsHermitian.spectral_theorem for spectral decomposition
- compoundMatrix_mul, compoundMatrix_conjTranspose, compoundMatrix_diagonal (all proved above)
- IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal from QuantumInfo.ForMathlib.Matrix
- Matrix.eigenvalues_conjTranspose_mul_self_nonneg for nonnegativity
- Real.sqrt_prod_of_nonneg or similar for sqrt of product
-/
lemma singularValues_compoundMatrix_eq (M : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d)
    (hcard : 0 < Fintype.card {S : Finset d // S.card = k}) :
    ∀ (S : {S : Finset d // S.card = k}),
    ∃ (j : {S : Finset d // S.card = k}),
    singularValues (compoundMatrix M k) j =
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) := by
  unfold singularValues;
  intro S;
  have h_eigenvalues : ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k}, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self (compoundMatrix M k).conjTranspose) ∘ σ) = fun S => ∏ i : Fin k, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self M.conjTranspose)) (S.1.orderEmbOfFin S.2 i) := by
    apply IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal;
    rotate_right;
    exact compoundMatrix ( Matrix.IsHermitian.eigenvectorUnitary ( isHermitian_mul_conjTranspose_self M.conjTranspose ) ) k;
    · have h_unitary : ∀ (U : Matrix d d ℂ), U ∈ unitaryGroup d ℂ → compoundMatrix U k ∈ unitaryGroup {S : Finset d // S.card = k} ℂ := by
        intro U hU
        have h_unitary : (compoundMatrix U k).conjTranspose * compoundMatrix U k = 1 := by
          have h_unitary : (compoundMatrix U k).conjTranspose * compoundMatrix U k = compoundMatrix (U.conjTranspose * U) k := by
            rw [ ← compoundMatrix_conjTranspose, ← compoundMatrix_mul ];
          have h_unitary : Uᴴ * U = 1 := by
            exact hU.1.symm ▸ by simp +decide [ Matrix.mul_eq_one_comm ] ;
          -- Since the identity matrix's compound matrix is the identity matrix, we can conclude that the product is the identity matrix.
          have h_id : compoundMatrix (1 : Matrix d d ℂ) k = 1 := by
            convert compoundMatrix_diagonal ( fun _ => 1 ) k using 1 ; aesop
            skip;
          grind
        have h_unitary' : compoundMatrix U k * (compoundMatrix U k).conjTranspose = 1 := by
          rw [ ← Matrix.mul_eq_one_comm, h_unitary ]
        exact ⟨by
        exact h_unitary, by
          exact h_unitary'⟩
        skip;
      exact h_unitary _ ( by simp +decide [ unitaryGroup ] );
    · have h_compoundMatrix_mul : compoundMatrix (M.conjTranspose * M) k = compoundMatrix M.conjTranspose k * compoundMatrix M k := by
        exact compoundMatrix_mul _ _ _;
      have h_compoundMatrix_conjTranspose : compoundMatrix M.conjTranspose k = (compoundMatrix M k).conjTranspose := by
        exact?;
      have := Matrix.IsHermitian.spectral_theorem ( isHermitian_mul_conjTranspose_self M.conjTranspose );
      convert congr_arg ( fun x => compoundMatrix x k ) this using 1 <;> simp +decide [ h_compoundMatrix_mul, h_compoundMatrix_conjTranspose ];
      rw [ compoundMatrix_mul, compoundMatrix_mul ];
      rw [ ← compoundMatrix_conjTranspose ];
      rw [ compoundMatrix_diagonal ] ; simp +decide [ Matrix.mul_assoc ] ;
      congr! 3;
  obtain ⟨ σ, hσ ⟩ := h_eigenvalues;
  use σ S; simp_all +decide [ funext_iff ] ;
  rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> norm_num [ Finset.prod_nonneg, Real.sqrt_nonneg ];
  · rw [ ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun _ _ => Real.mul_self_sqrt ( _ ) ];
    intro i hi; exact (by
    apply Matrix.eigenvalues_conjTranspose_mul_self_nonneg);
  · refine' Finset.prod_nonneg fun i _ => _;
    exact?

/-- The product of nonneg values over a k-subset is at most the product of the
    k largest values. -/
lemma prod_le_prod_sorted {n : ℕ} {f : Fin n → ℝ}
    (hf : Antitone f) (hf_nn : ∀ i, 0 ≤ f i)
    (k : ℕ) (hk : k ≤ n)
    (g : Fin k → Fin n) (hg : Function.Injective g) :
    ∏ i : Fin k, f (g i) ≤ ∏ i : Fin k, f ⟨i.val, by omega⟩ := by
  -- The sorted values at positions g(i) are bounded by the sorted values at positions i,
  -- because g is injective so g(i) ≥ i (in the sorted sense), and f is antitone.
  -- We use the fact that for injective g : Fin k → Fin n, sorting g gives values ≥ identity.
  -- First sort g to get g' with g'(0) < g'(1) < ... < g'(k-1)
  -- Then g'(i) ≥ i since we're choosing k distinct values from Fin n
  -- So f(g'(i)) ≤ f(i) by antitonicity
  -- And the product is preserved under sorting (it's the same set of values)
  have h_exists_sorted : ∃ (g' : Fin k → Fin n),
      Function.Injective g' ∧ StrictMono g' ∧
      Finset.image g Finset.univ = Finset.image g' Finset.univ := by
    exact ⟨Finset.orderEmbOfFin (Finset.image g Finset.univ) (by simp [Finset.card_image_of_injective _ hg]),
      fun a b h => by simpa using h,
      fun a b h => by simpa using h,
      by ext x; simp [Finset.orderEmbOfFin_mem]⟩
  obtain ⟨g', hg'_inj, hg'_mono, hg'_eq⟩ := h_exists_sorted
  have h_prod_eq : ∏ i : Fin k, f (g i) = ∏ i : Fin k, f (g' i) := by
    rw [← Finset.prod_image (f := f) (fun a _ b _ h => hg (by simpa using h)),
        ← Finset.prod_image (f := f) (fun a _ b _ h => hg'_inj (by simpa using h))]
    exact Finset.prod_congr hg'_eq (fun _ _ => rfl)
  rw [h_prod_eq]
  apply Finset.prod_le_prod (fun i _ => hf_nn _) (fun i _ => ?_)
  apply hf
  -- Need: i.val ≤ (g' i).val for strictly monotone g'
  -- By induction: g'(0) ≥ 0, and g'(j+1) > g'(j) ≥ j implies g'(j+1) ≥ j+1
  suffices h : ∀ (m : ℕ) (hm : m < k), m ≤ (g' ⟨m, hm⟩).val from h i.val i.isLt
  intro m hm
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have ihm := ih (by omega)
    have := hg'_mono (show (⟨m, by omega⟩ : Fin k) < ⟨m + 1, hm⟩ by simp [Fin.lt_iff_val_lt_val])
    omega

set_option maxHeartbeats 800000 in
lemma prod_singularValuesSorted_eq_compoundSV (M : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) :
    ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ =
    singularValuesSorted (compoundMatrix M k) ⟨0, by
      have : Fintype.card {S : Finset d // S.card = k} = (Fintype.card d).choose k := by
        simp [Fintype.card_subtype]
      rw [this]; exact Nat.choose_pos hk⟩ := by
  sorry

/-
PROBLEM
The 0th sorted singular value is the maximum of the singular values.

PROVIDED SOLUTION
singularValuesSorted A ⟨0, h⟩ is the first element of the list obtained by sorting the multiset {singularValues A i : i ∈ univ} in decreasing order (· ≥ ·). The first element of a list sorted in decreasing order is the maximum of the list.

The maximum of the list equals Finset.sup' univ ... (singularValues A) by definition of sup'.

More precisely:
1. Unfold singularValuesSorted to get the 0th element of the sorted list.
2. The 0th element of a sorted (in ≥ order) list is the list's maximum.
3. The list is the sort of the multiset of singular values.
4. The elements of this multiset are exactly {singularValues A i : i ∈ Finset.univ}.
5. The maximum of these elements is Finset.sup' univ ... (singularValues A).

Key Mathlib lemmas:
- List.Sorted.head_le or similar for the first element being the max
- Multiset.sort preserves elements
- Finset.sup' properties
-/
lemma singularValuesSorted_zero_eq_sup {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) :
    singularValuesSorted A ⟨0, h⟩ = Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp h))
      (singularValues A) := by
  refine' le_antisymm _ _;
  · -- Since the list is sorted in decreasing order, every element in the list is less than or equal to the supremum of the original set.
    have h_le_sup : ∀ x ∈ Multiset.sort (· ≥ ·) (Multiset.map (singularValues A) Finset.univ.val), x ≤ Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨Classical.choose (Finset.card_pos.mp h)⟩) (singularValues A) := by
      aesop;
    exact h_le_sup _ ( by simp +decide [ singularValuesSorted ] );
  · have h_max_le_ge : ∀ i, singularValues A i ≤ singularValuesSorted A ⟨0, h⟩ := by
      intro i
      have h_max_le_ge : ∀ j, singularValuesSorted A j ≤ singularValuesSorted A ⟨0, h⟩ := by
        exact fun j => singularValuesSorted_antitone A ( Nat.zero_le _ )
      exact (by
      have h_max_le_ge : ∃ j, singularValues A i = singularValuesSorted A j := by
        have h_exists_j : singularValues A i ∈ Multiset.sort (· ≥ ·) (Finset.univ.val.map (singularValues A)) := by
          simp +decide [ Multiset.mem_sort ];
        obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp h_exists_j;
        exact ⟨ ⟨ j, by simpa using j.2 ⟩, hj.symm ⟩;
      aesop);
    exact Finset.sup'_le _ _ fun i _ => h_max_le_ge i

/-
PROBLEM
For a PSD Hermitian matrix H with eigenvalues λ, we have
    v† H v ≤ (max λ) · v† v for all v.
    This is the Rayleigh quotient bound.

PROVIDED SOLUTION
Use the spectral theorem for Hermitian matrices. By Matrix.IsHermitian.spectral_theorem, H = U * diagonal(ofReal ∘ λ) * star U where U = hH.eigenvectorUnitary and λ = hH.eigenvalues.

Let w = star U * v (i.e., the coordinates in the eigenbasis). The key idea: the Hermitian matrix can be diagonalized, reducing the quadratic form to a sum of eigenvalue * |coordinate|² terms.

Step 1: Express star v ⬝ᵥ H.mulVec v in terms of eigenvalues.
Using the spectral decomposition H = U * D * U†:
star v ⬝ᵥ H.mulVec v = star v ⬝ᵥ (U * D * U†).mulVec v

Since U is unitary (from eigenvectorUnitary), U† * U = 1, so:
This equals star(U† v) ⬝ᵥ (D * (U† v)) [by associativity and unitarity]

For the diagonal matrix D = diagonal(ofReal ∘ λ):
star w ⬝ᵥ D.mulVec w = ∑ i, starRingEnd ℂ (w i) * (ofReal (λ i) * w i)
= ∑ i, (ofReal (λ i)) * (starRingEnd ℂ (w i) * w i)
= ∑ i, (ofReal (λ i)) * ‖w i‖²   [since conj(z) * z = |z|²]

The real part is ∑ i, λ i * ‖w i‖².

Step 2: Bound by max eigenvalue.
Since λ i ≤ sup' univ λ for all i:
∑ i, λ i * ‖w i‖² ≤ (sup' univ λ) * ∑ i ‖w i‖² = (sup' univ λ) * ‖w‖²

Step 3: Show ‖w‖² = star v ⬝ᵥ v.
Since U is unitary, ‖U† v‖² = ‖v‖², i.e., star(U†v) ⬝ᵥ (U†v) = star v ⬝ᵥ v.

This completes the proof.
-/
lemma IsHermitian.inner_le_sup_eigenvalue_mul_inner
    {e : Type*} [Fintype e] [DecidableEq e]
    (H : Matrix e e ℂ) (hH : H.IsHermitian)
    (hPSD : ∀ i, 0 ≤ hH.eigenvalues i)
    (he : 0 < Fintype.card e)
    (v : e → ℂ) :
    Complex.re (star v ⬝ᵥ H.mulVec v) ≤
    Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp he))
      hH.eigenvalues * Complex.re (star v ⬝ᵥ v) := by
  have := hH.spectral_theorem
  generalize_proofs at *;
  -- Let $w = U^* v$, then $v^* H v = w^* D w$.
  set w : e → ℂ := star (hH.eigenvectorUnitary : Matrix e e ℂ) |> Matrix.mulVec <| v
  have h_eq : (star v ⬝ᵥ H *ᵥ v).re = (star w ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ w).re := by
    replace this := congr_arg ( fun m => star v ⬝ᵥ m *ᵥ v ) this ; simp_all +decide [ Matrix.mul_assoc ] ;
    simp +zetaDelta at *;
    simp +decide [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.star_mulVec ];
    congr! 3;
    ext i j; simp +decide [ Matrix.mul_apply, Matrix.diagonal ] ;
  -- Since $D$ is diagonal with eigenvalues $\lambda_i$, we have $w^* D w = \sum_{i} \lambda_i |w_i|^2$.
  have h_diag : (star w ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ w).re = ∑ i, (hH.eigenvalues i) * ‖w i‖ ^ 2 := by
    simp +decide [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Complex.normSq_eq_norm_sq, Complex.mul_conj ];
    simp +decide [ Complex.normSq, Complex.sq_norm, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, diagonal ];
    rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ Finset.sum_eq_single i, Finset.sum_eq_single i ] <;> simp +contextual [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ] ; ring;
    · exact fun j hj => Or.inl ( by rw [ if_neg ( Ne.symm hj ) ] ; norm_num );
    · exact fun j hj => Or.inl ( by rw [ if_neg ( Ne.symm hj ) ] ; norm_num );
  -- Since $U$ is unitary, we have $\|w\|^2 = \|v\|^2$.
  have h_unitary : ∑ i, ‖w i‖ ^ 2 = (star v ⬝ᵥ v).re := by
    have h_unitary : ∀ (U : Matrix e e ℂ), U.conjTranspose * U = 1 → ∀ (v : e → ℂ), ∑ i, ‖(U.mulVec v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      intro U hU v
      have h_unitary : (star (U.mulVec v) ⬝ᵥ U.mulVec v) = (star v ⬝ᵥ v) := by
        have h_unitary : (star (U.mulVec v) ⬝ᵥ U.mulVec v) = (star v ⬝ᵥ (Uᴴ * U).mulVec v) := by
          simp +decide [ Matrix.mulVec, dotProduct ];
          simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm ) |> Eq.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;
        generalize_proofs at *; (
        rw [ h_unitary, hU, Matrix.one_mulVec ])
      generalize_proofs at *; (
      convert congr_arg Complex.re h_unitary using 1 <;> simp +decide [ Complex.ext_iff, sq ] ; ring!;
      · simp +decide [ Complex.ext_iff, dotProduct, sq ] ; ring!;
        simp +decide [ Complex.normSq, Complex.sq_norm ] ; ring!;
      · simp +decide [ Complex.ext_iff, dotProduct ];
        simp +decide [ ← sq, Complex.normSq_apply, Complex.sq_norm ]);
    convert h_unitary ( star ( hH.eigenvectorUnitary : Matrix e e ℂ ) ) _ v using 1 <;> norm_num [ Matrix.mulVec, dotProduct ];
    · norm_num [ Complex.normSq, Complex.sq_norm ];
    · simp +decide [ Matrix.star_eq_conjTranspose ];
      simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
  rw [ h_eq, h_diag, ← h_unitary, Finset.mul_sum _ _ _ ];
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( Finset.le_sup' ( fun i => hH.eigenvalues i ) ( Finset.mem_univ i ) ) ( sq_nonneg _ )

/-
PROBLEM
All eigenvalues of A†A are bounded by (max singular value)².

PROVIDED SOLUTION
The eigenvalue (isHermitian_mul_conjTranspose_self A†).eigenvalues i equals the eigenvalue of A†A at index i.

singularValuesSorted A ⟨0, h⟩ = sup' univ (singularValues A) by singularValuesSorted_zero_eq_sup.
singularValues A j = sqrt(eigenvalue_j of A†A) for each j.

So (singularValuesSorted A ⟨0, h⟩)² = (sup_j sqrt(eigenvalue_j))² = sup_j (eigenvalue_j) [since sqrt is monotone and eigenvalues are nonneg, the sup of sqrt equals sqrt of sup, so squaring gives the sup of eigenvalues].

More precisely:
(sup_j sqrt(eigenvalue_j))² ≥ sqrt(eigenvalue_i)² = eigenvalue_i for all i.

Proof:
1. singularValuesSorted_zero_eq_sup gives singularValuesSorted A ⟨0, h⟩ = sup' univ (singularValues A).
2. singularValues A j = sqrt(eigenvalue_j of A†A) by definition.
3. So singularValuesSorted A ⟨0, h⟩ ≥ singularValues A (some j corresponding to i)...

Actually more directly: eigenvalue_i ≤ sup eigenvalue ≤ (sup sqrt eigenvalue)² = (singularValuesSorted A ⟨0, h⟩)².

The second inequality follows from: if x = sup sqrt(λ_j), then x ≥ sqrt(λ_j) for all j, so x² ≥ λ_j for all j. And sup λ_j ≤ x² since each λ_j ≤ x².

For the first part: eigenvalue_i ≤ sup eigenvalue is immediate from le_sup'.
But actually, using a simpler argument: eigenvalue_i = (sqrt(eigenvalue_i))² (since eigenvalues are ≥ 0 by Matrix.eigenvalues_conjTranspose_mul_self_nonneg). And sqrt(eigenvalue_i) = singularValues A (some index). And singularValues A (some index) ≤ sup' singularValues A = singularValuesSorted A ⟨0, h⟩. So squaring: eigenvalue_i ≤ (singularValuesSorted A ⟨0, h⟩)².

Use Matrix.eigenvalues_conjTranspose_mul_self_nonneg or similar for nonnegativity of eigenvalues, Real.sq_sqrt for sqrt² = original, and Finset.le_sup' for the bound.
-/
lemma eigenvalue_le_singularValuesSorted_sq {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) (i : e) :
    (isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i ≤
    (singularValuesSorted A ⟨0, h⟩) ^ 2 := by
  -- By definition of singular values, we know that $\sigma_i(A)^2 = \lambda_i(A^*A)$.
  have h_singular_value_squared : ∀ i, (singularValues A i) ^ 2 = (isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i := by
    intro i
    simp [singularValues];
    rw [ Real.sq_sqrt ( _ ) ];
    convert Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i using 1;
  rw [ ← h_singular_value_squared i ];
  gcongr;
  · exact Real.sqrt_nonneg _;
  · convert singularValuesSorted_zero_eq_sup A h |> fun h => h.ge.trans' _;
    exact Finset.le_sup' ( fun i => singularValues A i ) ( Finset.mem_univ i )

/-
PROBLEM
The quadratic form of A†A is bounded by (max singular value)² * ‖v‖².

PROVIDED SOLUTION
Apply IsHermitian.inner_le_sup_eigenvalue_mul_inner to H = A†A (which is PSD Hermitian) to get:
Re(v† (A†A) v) ≤ (sup eigenvalue of A†A) * Re(v† v)

Then show sup eigenvalue of A†A ≤ (singularValuesSorted A ⟨0, h⟩)².

The sup eigenvalue equals sup' univ (eigenvalues of A†A). Each eigenvalue_i ≤ (singularValuesSorted A ⟨0, h⟩)² by eigenvalue_le_singularValuesSorted_sq. So sup eigenvalue ≤ (singularValuesSorted A ⟨0, h⟩)².

Therefore Re(v† (A†A) v) ≤ (singularValuesSorted A ⟨0, h⟩)² * Re(v† v).

Use:
- IsHermitian.inner_le_sup_eigenvalue_mul_inner with H = A†A
- isHermitian_mul_conjTranspose_self A† for the Hermitian proof
- Matrix.eigenvalues_conjTranspose_mul_self_nonneg for PSD
- eigenvalue_le_singularValuesSorted_sq for the eigenvalue bound
- Finset.sup'_le for bounding the sup
-/
lemma quadratic_form_le_singularValuesSorted_sq {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) (v : e → ℂ) :
    Complex.re (star v ⬝ᵥ (A.conjTranspose * A).mulVec v) ≤
    (singularValuesSorted A ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
  apply le_trans (IsHermitian.inner_le_sup_eigenvalue_mul_inner (Aᴴ * A) (by
  simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc ]) (by
  exact?) (by
  exact h) v);
  all_goals generalize_proofs at *;
  apply_rules [ mul_le_mul_of_nonneg_right, Finset.sup'_le ];
  · intro i _;
    convert eigenvalue_le_singularValuesSorted_sq A h i using 1;
    simp +decide [ Matrix.conjTranspose_conjTranspose ];
  · simp +decide [ dotProduct, Complex.mul_conj ];
    exact Finset.sum_nonneg fun _ _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ )

/-
PROBLEM
The largest singular value of a matrix product is at most the product of the
    largest singular values: `σ₁(M * N) ≤ σ₁(M) * σ₁(N)`.
    This is operator-norm submultiplicativity.

PROVIDED SOLUTION
Step 1: Rewrite using singularValuesSorted_zero_eq_sup:
singularValuesSorted (M*N) ⟨0, h⟩ = sup' univ (singularValues (M*N))
singularValues (M*N) i = sqrt(eigenvalue_i of (MN)†(MN))

Step 2: Show each eigenvalue of (MN)†(MN) ≤ (singularValuesSorted M ⟨0,h⟩ * singularValuesSorted N ⟨0,h⟩)².

For each eigenvalue λ_i with eigenvector v_i:
λ_i = Re(v_i† (MN)†(MN) v_i) / Re(v_i† v_i) [from eigenvalue equation]

By Matrix.IsHermitian.eigenvalues_eq, λ_i = Re(star w ⬝ᵥ (MN)†(MN).mulVec w) where w = eigenvector.

Now (MN)†(MN) = N†(M†M)N. So:
Re(w† N†M†MN w) = Re((Nw)† M†M (Nw)) ≤ (σ_max(M))² * Re((Nw)† (Nw)) [by quadratic_form_le_singularValuesSorted_sq for M]
= (σ_max(M))² * Re(w† N†N w) ≤ (σ_max(M))² * (σ_max(N))² * Re(w† w) [by quadratic_form_le_singularValuesSorted_sq for N]

But we also know Re(w† w) is the norm-squared of the eigenvector, and λ_i = Re(w† (MN)†(MN) w) / Re(w† w) [for normalized eigenvector].

So λ_i ≤ (σ_max(M) * σ_max(N))².

Step 3: Since λ_i ≤ (σ_max(M) * σ_max(N))² and eigenvalues are nonneg:
sqrt(λ_i) ≤ σ_max(M) * σ_max(N)
So singularValues (M*N) i ≤ σ_max(M) * σ_max(N) for all i.
Therefore sup singularValues (M*N) ≤ σ_max(M) * σ_max(N).
By singularValuesSorted_zero_eq_sup, singularValuesSorted (M*N) ⟨0, h⟩ ≤ σ_max(M) * σ_max(N).

Key lemmas to use: singularValuesSorted_zero_eq_sup, quadratic_form_le_singularValuesSorted_sq, eigenvalue_le_singularValuesSorted_sq, Finset.sup'_le, Real.sqrt_le_sqrt.
-/
lemma singularValuesSorted_mul_le {e : Type*} [Fintype e] [DecidableEq e]
    (M N : Matrix e e ℂ) (h : 0 < Fintype.card e) :
    singularValuesSorted (M * N) ⟨0, h⟩ ≤
    singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
  rw [ singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup ];
  -- Apply the inequality eigenvalue_le_singularValuesSorted_sq to each eigenvalue of (MN)†(MN).
  have h_eigenvalue_le : ∀ i, (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩) ^ 2 := by
    intro i
    have h_eigenvalue_le : (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * (singularValuesSorted N ⟨0, h⟩) ^ 2 := by
      -- By the properties of singular values and eigenvalues, we know that the eigenvalues of $(MN)^* (MN)$ are bounded by the product of the squares of the singular values of $M$ and $N$.
      have h_eigenvalue_bound : ∀ (v : e → ℂ), Complex.re (star v ⬝ᵥ ((M * N).conjTranspose * (M * N)).mulVec v) ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * (singularValuesSorted N ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
        intro v
        have h_quadratic_form : Complex.re (star v ⬝ᵥ ((M * N).conjTranspose * (M * N)).mulVec v) ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ (N.conjTranspose * N).mulVec v) := by
          have := quadratic_form_le_singularValuesSorted_sq M h ( N.mulVec v );
          convert this using 1 <;> simp +decide [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.star_mulVec ];
        have h_quadratic_form_N : Complex.re (star v ⬝ᵥ (N.conjTranspose * N).mulVec v) ≤ (singularValuesSorted N ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
          convert quadratic_form_le_singularValuesSorted_sq N h v using 1;
        simpa only [ mul_assoc ] using h_quadratic_form.trans ( mul_le_mul_of_nonneg_left h_quadratic_form_N ( sq_nonneg _ ) );
      convert h_eigenvalue_bound ( ( isHermitian_mul_conjTranspose_self ( M * N ).conjTranspose ).eigenvectorBasis i ) using 1;
      · have := ( isHermitian_mul_conjTranspose_self ( M * N ).conjTranspose ).eigenvalues_eq i; aesop;
      · simp +decide [ dotProduct, Complex.ext_iff ];
        have := ( isHermitian_mul_conjTranspose_self ( M * N ).conjTranspose ).eigenvectorBasis.orthonormal;
        rw [ orthonormal_iff_ite ] at this;
        simp_all +decide [ Complex.ext_iff, inner ];
    linarith;
  -- Apply the inequality eigenvalue_le_singularValuesSorted_sq to each eigenvalue of (MN)†(MN) and take the square root.
  have h_sqrt_eigenvalue_le : ∀ i, singularValues (M * N) i ≤ singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
    intro i
    have h_sqrt_eigenvalue_le_i : (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩) ^ 2 := h_eigenvalue_le i
    have h_sqrt_eigenvalue_le_i' : Real.sqrt ((isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i) ≤ singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
      exact Real.sqrt_le_iff.mpr ⟨ mul_nonneg ( singularValuesSorted_nonneg M ⟨ 0, h ⟩ ) ( singularValuesSorted_nonneg N ⟨ 0, h ⟩ ), h_sqrt_eigenvalue_le_i ⟩
    exact h_sqrt_eigenvalue_le_i' |> le_trans (by
    exact le_rfl);
  simp_all +decide [ Finset.sup'_le_iff ];
  convert h_sqrt_eigenvalue_le using 1;
  rw [ singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup ]

/-- Horn's inequality (weak log-majorization of singular values):
For all `k`, `∏_{i<k} σ↓ᵢ(AB) ≤ ∏_{i<k} σ↓ᵢ(A) · σ↓ᵢ(B)`.
This follows from submultiplicativity of the operator norm applied to
exterior powers of the matrices. -/
lemma horn_weak_log_majorization (A B : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) :
    ∏ i : Fin k, singularValuesSorted (A * B) ⟨i.val, by omega⟩ ≤
    ∏ i : Fin k, (singularValuesSorted A ⟨i.val, by omega⟩ *
                   singularValuesSorted B ⟨i.val, by omega⟩) := by
  -- Rewrite the RHS as (prod of σ↓(A)) * (prod of σ↓(B))
  rw [Finset.prod_mul_distrib]
  -- Use the compound matrix characterisation and submultiplicativity
  have hcard : 0 < Fintype.card {S : Finset d // S.card = k} := by
    have : Fintype.card {S : Finset d // S.card = k} = (Fintype.card d).choose k := by
      simp [Fintype.card_subtype]
    rw [this]; exact Nat.choose_pos hk
  calc ∏ i : Fin k, singularValuesSorted (A * B) ⟨i.val, by omega⟩
      = singularValuesSorted (compoundMatrix (A * B) k) ⟨0, hcard⟩ :=
        prod_singularValuesSorted_eq_compoundSV (A * B) k hk
    _ = singularValuesSorted (compoundMatrix A k * compoundMatrix B k) ⟨0, hcard⟩ := by
        rw [compoundMatrix_mul]
    _ ≤ singularValuesSorted (compoundMatrix A k) ⟨0, hcard⟩ *
        singularValuesSorted (compoundMatrix B k) ⟨0, hcard⟩ :=
        singularValuesSorted_mul_le _ _ hcard
    _ = (∏ i : Fin k, singularValuesSorted A ⟨i.val, by omega⟩) *
        (∏ i : Fin k, singularValuesSorted B ⟨i.val, by omega⟩) := by
        rw [← prod_singularValuesSorted_eq_compoundSV A k hk,
            ← prod_singularValuesSorted_eq_compoundSV B k hk]

/-! ### Weak log-majorization implies sum of powers inequality -/

/-- Raising nonneg antitone sequences to a positive power preserves antitonicity. -/
lemma rpow_antitone_of_nonneg_antitone {n : ℕ}
    {f : Fin n → ℝ} (hf : Antitone f) (hf_nn : ∀ i, 0 ≤ f i)
    {r : ℝ} (hr : 0 < r) :
    Antitone (fun i => f i ^ r) := by
  exact fun i j hij => Real.rpow_le_rpow (hf_nn _) (hf hij) hr.le

/-- Weak log-majorization is preserved under positive powers. -/
lemma rpow_preserves_weak_log_maj {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩)
    {r : ℝ} (hr : 0 < r) :
    ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, (fun j => x j ^ r) ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, (fun j => y j ^ r) ⟨i.val, by omega⟩ := by
  intro k hk
  convert Real.rpow_le_rpow _ (h_log_maj k hk) hr.le using 1 <;>
    norm_num [Real.finset_prod_rpow _ _ fun i _ => hx_nn _,
              Real.finset_prod_rpow _ _ fun i _ => hy_nn _]
  exact Finset.prod_nonneg fun _ _ => hx_nn _

/-
The Abel summation identity (a rewriting of the sum) gives:
∑_{i=0}^{n-1} x_i * d_i = x_{n-1} * D_{n-1} + ∑_{i=0}^{n-2} (x_i - x_{i+1}) * D_i
(This is essentially Finset.sum_range_by_parts with f = x and g = d.)
Each term is nonneg because:
- x_{n-1} ≥ 0 (positive) and D_{n-1} ≥ 0 (see below)
- x_i - x_{i+1} ≥ 0 (x is antitone) and D_i ≥ 0 (see below)
D_k = ∑_{j=0}^k log(y_j/x_j) = log(∏_{j=0}^k y_j/x_j) = log(∏ y_j / ∏ x_j) ≥ log(1) = 0
because ∏ y_j ≥ ∏ x_j (weak log-majorization) and both products are positive.
So ∑ x_i * d_i is a sum of nonneg terms, hence ≥ 0.
Use Finset.sum_range_by_parts from Mathlib. The key Mathlib lemma is:
Finset.sum_range_by_parts f g n = f (n-1) • ∑_{i<n} g i - ∑_{i<n-1} (f(i+1) - f(i)) • ∑_{j<i+1} g j
Here f i = x ⟨i, ...⟩ (antitone) and g i = log(y ⟨i,...⟩ / x ⟨i,...⟩).
Actually, it may be easier to prove this directly by induction on n, without using Finset.sum_range_by_parts. The induction step would split off the last term and use the IH.
For the direct induction approach on n:
- n = 0: sum is empty, 0 ≥ 0.
- n = 1: x_0 * log(y_0/x_0) ≥ 0 since x_0 > 0 and log(y_0/x_0) ≥ 0 (from ∏_{i<1} x_i ≤ ∏_{i<1} y_i, i.e., x_0 ≤ y_0, so y_0/x_0 ≥ 1, so log(y_0/x_0) ≥ 0).
- n+1 → n+2: Split ∑_{i=0}^{n+1} x_i * log(y_i/x_i) = ∑_{i=0}^{n} x_i * log(y_i/x_i) + x_{n+1} * log(y_{n+1}/x_{n+1}).
  Now ∑_{i=0}^{n} x_i * log(y_i/x_i) ≥ ∑_{i=0}^{n} x_{n+1} * log(y_i/x_i) (since x_i ≥ x_{n+1} and log(y_i/x_i) could be negative, but x_i * log(y_i/x_i) ≥ x_{n+1} * log(y_i/x_i) when log(y_i/x_i) ≥ 0).
Hmm, this doesn't work cleanly because log(y_i/x_i) can be negative for some i.
Better approach: prove it directly using the Abel summation identity and nonnegativity of each term.
-/
set_option maxHeartbeats 800000 in
lemma sum_mul_log_nonneg_of_weak_log_maj {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_pos : ∀ i, 0 < x i) (hy_pos : ∀ i, 0 < y i)
    (hx_anti : Antitone x)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩) :
    0 ≤ ∑ i, x i * Real.log (y i / x i) := by
  by_contra h_neg
  -- Let $d_i = \log(y_i / x_i)$ and $D_k = \sum_{j=0}^{k} d_j$.
  set d : Fin n → ℝ := fun i => Real.log (y i / x i)
  set D : Fin n → ℝ := fun k => ∑ i ∈ Finset.Iic k, d i;
  -- By Abel's summation formula, we have $\sum_{i=0}^{n-1} x_i d_i = x_{n-1} D_{n-1} + \sum_{i=0}^{n-2} (x_i - x_{i+1}) D_i$.
  have hn : n ≠ 0 := by rintro rfl; simp at h_neg
  have h_abel : ∑ i, x i * d i = x ⟨n - 1, by omega⟩ * D ⟨n - 1, by omega⟩ + ∑ i : Fin (n - 1),
      (x ⟨i.val, by omega⟩ - x ⟨i.val + 1, by omega⟩) * D ⟨i.val, by omega⟩ := by
    rcases n with ⟨ ⟩ <;> norm_num at *;
    rename_i n;
    have h_abel : ∀ m : Fin (n + 1), ∑ i ∈ Finset.Iic m, x i * d i = x m * D m + ∑ i ∈ Finset.Iio m, (x i - x (i + 1)) * D i := by
      intro m;
      induction' m using Fin.inductionOn with m ih;
      · simp +zetaDelta at *;
        rw [ Finset.sum_eq_single 0, Finset.sum_eq_single 0 ] <;> aesop;
      · rw [ show ( Finset.Iic ( Fin.succ m ) : Finset ( Fin ( n + 1 ) ) ) = Finset.Iic ( Fin.castSucc m ) ∪ { Fin.succ m } from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_singleton, Finset.sum_union, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
        · rw [ show ( Finset.Iio ( Fin.succ m ) : Finset ( Fin ( n + 1 ) ) ) = Finset.Iio ( Fin.castSucc m ) ∪ { Fin.castSucc m } from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_singleton, Finset.sum_union, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
          · rw [ ih ]
            ring_nf!
            rw [ show ( Finset.Iic ( Fin.succ m ) : Finset ( Fin ( n + 1 ) ) ) = Finset.Iic ( Fin.castSucc m ) ∪ { Fin.succ m } from ?_, Finset.sum_union ] <;> norm_num ; ring!;
            ext i; simp [Finset.mem_Iic, Finset.mem_insert];
            exact ⟨ fun hi => or_iff_not_imp_left.mpr fun hi' => Nat.le_of_lt_succ <| hi.lt_of_ne hi', fun hi => hi.elim ( fun hi => hi.symm ▸ le_rfl ) fun hi => Nat.le_trans hi ( Nat.le_succ _ ) ⟩;
          · ext i; simp [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val];
            exact Nat.lt_succ_iff;
        · ext i; simp [Finset.mem_Iic, Finset.mem_insert];
          exact ⟨ fun hi => or_iff_not_imp_left.mpr fun hi' => Nat.le_of_lt_succ <| hi.lt_of_ne hi', fun hi => hi.elim ( fun hi => hi.symm ▸ le_rfl ) fun hi => Nat.le_trans hi ( Nat.le_succ _ ) ⟩;
    convert h_abel ⟨ n, Nat.lt_succ_self _ ⟩ using 1;
    · rw [ show ( Iic ⟨ n, Nat.lt_succ_self _ ⟩ : Finset ( Fin ( n + 1 ) ) ) = Finset.univ from Finset.eq_univ_of_forall fun i => Finset.mem_Iic.mpr ( Nat.le_of_lt_succ i.2 ) ];
    · refine' congr rfl ( Finset.sum_bij ( fun i hi => ⟨ i, by omega⟩ ) _ _ _ _ ) <;> simp [ Fin.add_def, Nat.mod_eq_of_lt ];
      · exact fun i j h => Fin.ext h;
      · exact fun i hi => ⟨ ⟨ i, by linarith [ Fin.is_lt i, show ( i : ℕ ) < n from hi ] ⟩, rfl ⟩
  -- Since $D_k \geq 0$ for all $k$, we have $x_{n-1} D_{n-1} \geq 0$ and $(x_i - x_{i+1}) D_i \geq 0$ for all $i$.
  have h_nonneg : ∀ k : Fin n, 0 ≤ D k := by
    intro k
    have h_prod : ∏ i ∈ Finset.Iic k, y i ≥ ∏ i ∈ Finset.Iic k, x i := by
      specialize h_log_maj ( k + 1 ) ( by linarith [ Fin.is_lt k ] );
      rw [ show ( Finset.Iic k : Finset ( Fin n ) ) = Finset.image ( fun i : Fin ( k + 1 ) => ⟨ i, by linarith [ Fin.is_lt k, Fin.is_lt i ] ⟩ ) Finset.univ from ?_, Finset.prod_image ] <;> norm_num
      · rwa [ Finset.prod_image <| by intros i hi j hj hij; simpa [ Fin.ext_iff ] using hij ];
      · exact fun i _ j _ hij => Fin.ext <| by simpa using congr_arg Fin.val hij;
      · ext ⟨ i, hi ⟩ ; simp [ Fin.ext_iff, Fin.le_iff_val_le_val ] ;
        exact ⟨ fun hi' => ⟨ ⟨ i, by linarith [ Fin.is_lt k ] ⟩, rfl ⟩, fun ⟨ a, ha ⟩ => ha ▸ Nat.le_trans ( Nat.le_of_lt_succ ( by linarith [ Fin.is_lt a, Fin.is_lt k ] ) ) ( Nat.le_refl _ ) ⟩
    simp +zetaDelta at *;
    rw [ ← Real.log_prod _ _ fun i hi => ne_of_gt ( div_pos ( hy_pos i ) ( hx_pos i ) ) ] ; exact Real.log_nonneg ( by rw [ Finset.prod_div_distrib ] ; exact by rw [ le_div_iff₀ ( Finset.prod_pos fun i hi => hx_pos i ) ] ; linarith ) ;
  exact h_neg <| h_abel.symm ▸ add_nonneg ( mul_nonneg ( le_of_lt ( hx_pos _ ) ) ( h_nonneg _ ) ) ( Finset.sum_nonneg fun i hi => mul_nonneg ( sub_nonneg.mpr ( hx_anti <| Nat.le_succ _ ) ) ( h_nonneg _ ) )

/-
PROBLEM
For positive reals a, b: b - a ≥ a · log(b/a).
Equivalently: t - 1 ≥ log(t) for t = b/a.
PROVIDED SOLUTION
We need b - a ≥ a * log(b/a) for a, b > 0. Equivalently, dividing by a > 0: b/a - 1 ≥ log(b/a). Let t = b/a > 0. Then we need t - 1 ≥ log(t), which is equivalent to log(t) ≤ t - 1. This is Real.log_le_sub_one_of_le or follows from Real.add_one_le_exp: for any x, 1 + x ≤ exp(x). Taking x = log(t): 1 + log(t) ≤ exp(log(t)) = t, so log(t) ≤ t - 1. Multiply by a > 0 to get a * log(b/a) ≤ a * (b/a - 1) = b - a.
-/
lemma sub_ge_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b - a ≥ a * Real.log (b / a) := by
  nlinarith [ Real.log_le_sub_one_of_pos ( div_pos hb ha ), mul_div_cancel₀ b ha.ne' ]

/- Weak log-majorization of nonneg antitone sequences implies the sum inequality ∑ x_i ≤ ∑ y_i. -/
set_option maxHeartbeats 800000 in
lemma weak_log_maj_sum_le {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (hx_anti : Antitone x) (hy_anti : Antitone y)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩) :
    ∑ i, x i ≤ ∑ i, y i := by
  induction' n with n ih
  · norm_num +zetaDelta at *;
  · by_cases h_last : x (Fin.last n) = 0;
    · simp [ Fin.sum_univ_castSucc, h_last]
      refine le_add_of_le_of_nonneg ( ih ( fun i => hx_nn _ ) ( fun i => hy_nn _ ) ( fun i j hij => hx_anti hij ) ( fun i j hij => hy_anti hij ) ?_ ) ( hy_nn _ );
      intro k hk
      simp
      exact h_log_maj k (by linarith)
    · -- Since $x_{\text{last}} > 0$, we have $x_i > 0$ for all $i$.
      have hx_pos : ∀ i, 0 < x i := by
        exact fun i => lt_of_lt_of_le ( lt_of_le_of_ne ( hx_nn _ ) ( Ne.symm h_last ) ) ( hx_anti ( Fin.le_last _ ) )
      have hy_pos : ∀ i, 0 < y i := by
        intro i; specialize h_log_maj ( n + 1 ) le_rfl; contrapose! h_log_maj; simp_all [ Fin.prod_univ_castSucc ] ;
        exact lt_of_le_of_lt ( mul_nonpos_of_nonneg_of_nonpos ( Finset.prod_nonneg fun _ _ => hy_nn _ ) ( by linarith [ hy_anti ( show i ≤ Fin.last n from Fin.le_last i ) ] ) ) ( mul_pos ( Finset.prod_pos fun _ _ => hx_pos _ ) ( hx_pos _ ) )
      have h_sum_mul_log_nonneg : 0 ≤ ∑ i, x i * Real.log (y i / x i) := by
        apply sum_mul_log_nonneg_of_weak_log_maj (fun i => hx_pos i) (fun i => hy_pos i) hx_anti (fun k hk => h_log_maj k hk)
      have h_sum_mul_log_nonneg : ∑ i, (y i - x i) ≥ ∑ i, x i * Real.log (y i / x i) := by
        exact Finset.sum_le_sum fun i _ => by have := sub_ge_mul_log_div ( hx_pos i ) ( hy_pos i ) ; ring_nf at *; linarith;
      norm_num at *; linarith;

/-- Weak log-majorization of nonneg antitone sequences implies the sum of
powers inequality. -/
lemma weak_log_maj_sum_rpow_le {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (hx_anti : Antitone x) (hy_anti : Antitone y)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩)
    {r : ℝ} (hr : 0 < r) :
    ∑ i, x i ^ r ≤ ∑ i, y i ^ r := by
  apply weak_log_maj_sum_le
  · exact fun i => Real.rpow_nonneg (hx_nn i) r
  · exact fun i => Real.rpow_nonneg (hy_nn i) r
  · exact rpow_antitone_of_nonneg_antitone hx_anti hx_nn hr
  · exact rpow_antitone_of_nonneg_antitone hy_anti hy_nn hr
  · exact rpow_preserves_weak_log_maj hx_nn hy_nn h_log_maj hr

/-! ## Key singular value inequality for products -/

lemma sum_rpow_singularValues_mul_le (A B : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
    ∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ r ≤
    ∑ i : Fin (Fintype.card d),
      (singularValuesSorted A i ^ r * singularValuesSorted B i ^ r) := by
  have h_rw : ∀ i : Fin (Fintype.card d),
      singularValuesSorted A i ^ r * singularValuesSorted B i ^ r =
      (singularValuesSorted A i * singularValuesSorted B i) ^ r := by
    intro i
    rw [Real.mul_rpow (singularValuesSorted_nonneg A i) (singularValuesSorted_nonneg B i)]
  simp_rw [h_rw]
  apply weak_log_maj_sum_rpow_le
  · exact fun i => singularValuesSorted_nonneg (A * B) i
  · exact fun i => mul_nonneg (singularValuesSorted_nonneg A i) (singularValuesSorted_nonneg B i)
  · exact singularValuesSorted_antitone (A * B)
  · exact antitone_mul_of_antitone_nonneg
      (singularValuesSorted_antitone A) (singularValuesSorted_antitone B)
      (singularValuesSorted_nonneg A) (singularValuesSorted_nonneg B)
  · exact horn_weak_log_majorization A B
  · exact hr

/-! ## Hölder inequality for singular values -/

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
  have h_holder : (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) * (singularValuesSorted B i ^ r)) ≤ (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) ^ (p / r)) ^ (r / p) * (∑ i : Fin (Fintype.card d), (singularValuesSorted B i ^ r) ^ (q / r)) ^ (r / q) := by
    have := @Real.inner_le_Lp_mul_Lq;
    convert @this ( Fin ( Fintype.card d ) ) Finset.univ ( fun i => singularValuesSorted A i ^ r ) ( fun i => singularValuesSorted B i ^ r ) ( p / r ) ( q / r ) _ using 1 <;> norm_num [ hr.ne', hp.ne', hq.ne', div_eq_mul_inv ];
    · simp only [abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg A _) _),
              abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg B _) _)];
    · constructor <;> norm_num [ hr.ne', hp.ne', hq.ne' ] at hpqr ⊢ <;> ring_nf at hpqr ⊢ <;> nlinarith [ inv_pos.2 hr, inv_pos.2 hp, inv_pos.2 hq, mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ hp.ne', mul_inv_cancel₀ hq.ne' ];
  convert h_holder using 3 <;> push_cast [ ← Real.rpow_mul ( singularValuesSorted_nonneg _ _ ), mul_div_cancel₀ _ hr.ne' ] <;> ring_nf

end
