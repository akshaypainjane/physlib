/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

/-!
Quantities of quantum _relative entropy_, namely the (standard) quantum relative
entropy, and generalizations such as sandwiched Rényi relative entropy.
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}


open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix

/-
The operator norm of a matrix is the operator norm of the linear map it represents, with respect to the Euclidean norm.
-/
/-- The operator norm of a matrix, with respect to the Euclidean norm (l2 norm) on the domain and codomain. -/
noncomputable def Matrix.opNorm {m n 𝕜 : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [RCLike 𝕜] (A : Matrix m n 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-
An isometry preserves the Euclidean norm.
-/
theorem Matrix.isometry_preserves_norm {n m 𝕜 : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [RCLike 𝕜]
    (A : Matrix n m 𝕜) (hA : A.Isometry) (x : EuclideanSpace 𝕜 m) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  rw [ ← sq_eq_sq₀ ( by positivity ) ( by positivity ), Matrix.Isometry ] at *;
  simp [ EuclideanSpace.norm_eq]
  have h_inner : ∀ x y : EuclideanSpace 𝕜 m, inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x y := by
    intro x y
    have h_inner_eq : inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x (toEuclideanLin A.conjTranspose (toEuclideanLin A y)) := by
      simp [ Matrix.toEuclideanLin, inner ];
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, ];
      simp [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
    simp_all [ Matrix.toEuclideanLin];
  convert congr_arg Real.sqrt ( congr_arg ( fun z => ‖z‖ ) ( h_inner x x ) ) using 1;
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ];
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ]

/-
The operator norm of an isometry is 1 (assuming the domain is non-empty).
-/
theorem Matrix.opNorm_isometry {n m 𝕜 : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [RCLike 𝕜] [Nonempty m]
    (A : Matrix n m 𝕜) (hA : A.Isometry) : Matrix.opNorm A = 1 := by
  have h_opNorm : ∀ x : EuclideanSpace 𝕜 m, ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
    convert Matrix.isometry_preserves_norm A hA;
  refine' le_antisymm ( csInf_le _ _ ) ( le_csInf _ _ );
  · exact ⟨ 0, fun c hc => hc.1 ⟩;
  · aesop;
  · exact ⟨ 1, ⟨zero_le_one, fun x => le_of_eq (by simp [h_opNorm])⟩ ⟩;
  · norm_num +zetaDelta at *;
    intro b hb h; specialize h ( EuclideanSpace.single ( Classical.arbitrary m ) 1 ) ; aesop;

/-- The matrix representation of the map $v \mapsto v \otimes \sum_k |k\rangle|k\rangle$.
    The output index is `(d1 \times d2) \times d2`. -/
def map_to_tensor_MES (d1 d2 : Type*) [Fintype d1] [Fintype d2] [DecidableEq d1] [DecidableEq d2] :
    Matrix ((d1 × d2) × d2) d1 ℂ :=
  Matrix.of fun ((i, j), k) l => if i = l ∧ j = k then 1 else 0

theorem map_to_tensor_MES_prop (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (map_to_tensor_MES d₁ d₂).conjTranspose * (Matrix.kronecker A (1 : Matrix d₂ d₂ ℂ)) * (map_to_tensor_MES d₁ d₂) =
    A.traceRight := by
  ext i j; simp [map_to_tensor_MES, Matrix.mul_apply]
  simp [ Finset.sum_ite, Matrix.one_apply]
  rw [ Finset.sum_sigma' ];
  rw [ Finset.sum_congr rfl (g := fun x => A ( i, x.1.2 ) ( j, x.1.2 ))]
  · apply Finset.sum_bij (fun x _ => x.1.2)
    · simp
    · aesop
    · simp
    · simp
  · aesop

/-- The isometry V_rho from the paper. -/
noncomputable def V_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix ((dA × dB) × dB) dA ℂ :=
  let ρA_inv_sqrt := ρAB.traceRight⁻¹.sqrt
  let ρAB_sqrt := ρAB.sqrt
  let I_B := (1 : Matrix dB dB ℂ)
  let term1 := ρAB_sqrt.mat ⊗ₖ I_B
  let term2 := map_to_tensor_MES dA dB
  term1 * term2 * ρA_inv_sqrt.mat

open scoped MatrixOrder ComplexOrder

/-- The isometry V_sigma from the paper. -/
noncomputable def V_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dB × (dB × dC)) dC ℂ :=
  (V_rho (σBC.reindex (Equiv.prodComm dB dC))).reindex
    ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)))
    (Equiv.refl _)

/--
V_rho^H * V_rho simplifies to sandwiching the traceRight by the inverse square root.
-/
lemma V_rho_conj_mul_self_eq (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    let ρA := ρAB.traceRight
    let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
    (V_rho ρAB)ᴴ * (V_rho ρAB) = ρA_inv_sqrt * ρAB.traceRight.mat * ρA_inv_sqrt := by
  -- By definition of $V_rho$, we can write out the product $V_rho^H * V_rho$.
  simp [V_rho];
  simp [ ← Matrix.mul_assoc ];
  have h_simp : (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ))ᴴ * (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ)) = Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ) := by
    have h_simp : (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ)ᴴ * (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) = ρAB := by
      convert ρAB.sqrt_sq ( show 0 ≤ ρAB from ?_ ) using 1;
      · simp [ HermitianMat.sqrt ];
      · have := hρ.2;
        constructor;
        · simp [Matrix.IsHermitian]
        · intro x; by_cases hx : x = 0 <;> simp_all
          exact le_of_lt ( this x hx );
    ext ⟨ i, j ⟩ ⟨ k, l ⟩
    simp [ ← h_simp, Matrix.mul_apply ]
    ring_nf
    by_cases hij : j = l
    · simp [ hij, Matrix.one_apply ]
      simp [← Finset.sum_filter]
      refine' Finset.sum_bij ( fun x _ => x.1 ) _ _ _ _ <;> simp
      intro a b
      exact Or.inl ( by simpa using congr_fun ( congr_fun ( ρAB.sqrt.2 ) i ) ( a, b ) )
    · simp [ hij, Matrix.one_apply ]
      exact Finset.sum_eq_zero (by aesop)
  simp_all [ mul_assoc, Matrix.mul_assoc ];
  simp [ ← Matrix.mul_assoc, ← map_to_tensor_MES_prop ]

/--
The partial trace (left) of a positive definite matrix is positive definite.
-/
lemma PosDef_traceRight [Nonempty dB] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceRight.mat.PosDef := by
  have h_trace_right_pos_def : ∀ (x : EuclideanSpace ℂ dA), x ≠ 0 → 0 < ∑ k : dB, (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) := by
    intro x hx_ne_zero
    have h_inner_pos : ∀ k : dB, 0 ≤ (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) := by
      have := hA.2;
      intro k
      specialize this ( fun i => if h : i.2 = k then x i.1 else 0 )
      simp_all only [ne_eq, dite_eq_ite, dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        HermitianMat.mat_apply, mul_ite, mul_zero, HermitianMat.val_eq_coe, Matrix.submatrix_apply]
      convert this ( show ( fun i : dA × dB => if i.2 = k then x i.1 else 0 ) ≠ 0 from fun h => hx_ne_zero <| by ext i; simpa using congr_fun h ( i, k ) ) |> le_of_lt using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i : dA => ( i, k ) ) Finset.univ ) ) ] <;> simp [ Finset.sum_image, Finset.sum_ite ];
      · refine' Finset.sum_congr rfl fun i hi => _;
        refine' congr_arg _ ( Finset.sum_bij ( fun j _ => ( j, k ) ) _ _ _ _ ) <;> simp
      · exact fun a b hb => Or.inl fun h => False.elim <| hb <| h.symm;
    obtain ⟨k, hk⟩ : ∃ k : dB, (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) > 0 := by
      have := hA.2 ( fun i => x i.1 * ( if i.2 = Classical.arbitrary dB then 1 else 0 ) )
      simp_all only [ne_eq, dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        HermitianMat.val_eq_coe, Matrix.submatrix_apply, HermitianMat.mat_apply, mul_ite, mul_one, mul_zero]
      contrapose! this
      simp_all only [ne_eq, funext_iff, Pi.zero_apply, ite_eq_right_iff, Prod.forall, forall_eq,
        not_forall, Finset.sum_ite, Finset.sum_const_zero, add_zero] ;
      refine' ⟨ Function.ne_iff.mp hx_ne_zero, _ ⟩;
      convert this ( Classical.arbitrary dB ) using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.univ.image fun i : dA => ( i, Classical.arbitrary dB ) ) ) ]
      · simp only [Finset.coe_univ, Prod.mk.injEq, and_true, implies_true, Set.injOn_of_eq_iff_eq,
          Finset.sum_image, ↓reduceIte, gt_iff_lt]
        congr! 3;
        refine' Finset.sum_bij ( fun y hy => y.1 ) _ _ _ _ <;> simp
      · simp only [Finset.mem_univ, Finset.mem_image, true_and, not_exists, ne_eq, mul_eq_zero,
          map_eq_zero, ite_eq_right_iff, forall_const, Prod.forall, Prod.mk.injEq, not_and, forall_eq]
        exact fun a b hb => Or.inl fun h => False.elim <| hb <| h.symm ▸ rfl
    exact lt_of_lt_of_le hk ( Finset.single_le_sum ( fun k _ => h_inner_pos k ) ( Finset.mem_univ k ) );
  refine' ⟨A.traceRight.2, fun x hx => _ ⟩;
  · convert h_trace_right_pos_def x hx using 1;
    unfold HermitianMat.traceRight
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, HermitianMat.mat_mk, HermitianMat.val_eq_coe]
    simp only [Matrix.mulVec, dotProduct, mul_comm, Matrix.submatrix_apply, HermitianMat.mat_apply];
    simp only [Matrix.traceRight, HermitianMat.mat_apply, Matrix.of_apply, mul_comm, Finset.mul_sum]
    rw [Finset.sum_comm_cycle]

lemma PosDef_traceLeft [Nonempty dA] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceLeft.mat.PosDef := by
  exact PosDef_traceRight (A.reindex (Equiv.prodComm _ _)) (hA.reindex _)

/--
V_rho is an isometry.
-/
theorem V_rho_isometry [Nonempty dB] (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    (V_rho ρAB)ᴴ * (V_rho ρAB) = 1 := by
  -- Since ρA is positive definite, we can use the fact that ρA_inv_sqrt * ρA * ρA_inv_sqrt = I.
  have h_pos_def : (ρAB.traceRight⁻¹.sqrt : Matrix dA dA ℂ) * (ρAB.traceRight : Matrix dA dA ℂ) * (ρAB.traceRight⁻¹.sqrt : Matrix dA dA ℂ) = 1 := by
    convert HermitianMat.sqrt_inv_mul_self_mul_sqrt_inv_eq_one _;
    exact PosDef_traceRight _ hρ
  rw [← h_pos_def]
  exact V_rho_conj_mul_self_eq ρAB hρ

/--
V_sigma is an isometry.
-/
theorem V_sigma_isometry [Nonempty dB] (σBC : HermitianMat (dB × dC) ℂ) (hσ : σBC.mat.PosDef) :
    (V_sigma σBC).conjTranspose * (V_sigma σBC) = 1 := by
  simp [V_sigma]
  exact V_rho_isometry _ (hσ.reindex _)

/-
Definition of W_mat with correct reindexing.
-/
open HermitianMat
open scoped MatrixOrder

variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC]

/-- The operator W from the paper, defined as a matrix product. -/
noncomputable def W_mat (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) : Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ :=
  let ρA := ρAB.traceRight
  let σC := σBC.traceLeft
  let ρAB_sqrt := (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ)
  let σC_inv_sqrt := (σC⁻¹.sqrt : Matrix dC dC ℂ)
  let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
  let σBC_sqrt := (σBC.sqrt : Matrix (dB × dC) (dB × dC) ℂ)

  let term1 := ρAB_sqrt ⊗ₖ σC_inv_sqrt
  let term2 := ρA_inv_sqrt ⊗ₖ σBC_sqrt
  let term2_reindexed := term2.reindex (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm

  term1 * term2_reindexed

/--
The operator norm of a matrix product is at most the product of the operator norms.
-/
theorem Matrix.opNorm_mul_le {l m n 𝕜 : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
  have h_opNorm_mul_le : ∀ (A : Matrix l m 𝕜) (B : Matrix m n 𝕜), Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
    intro A B
    have h_comp : Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
      ext; simp [toEuclideanLin]
    convert ContinuousLinearMap.opNorm_comp_le ( Matrix.toEuclideanLin A |> LinearMap.toContinuousLinearMap ) ( Matrix.toEuclideanLin B |> LinearMap.toContinuousLinearMap ) using 1;
    unfold Matrix.opNorm;
    exact congr_arg _ ( by aesop );
  exact h_opNorm_mul_le A B

theorem Matrix.opNorm_reindex_proven {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (e : m ≃ l) (f : n ≃ p) (A : Matrix m n 𝕜) :
    Matrix.opNorm (A.reindex e f) = Matrix.opNorm A := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ 0, fun c hc => hc.1 ⟩;
    · refine' ⟨ norm_nonneg _, fun x => _ ⟩;
      convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( Matrix.toEuclideanLin A ) ) ( fun i => x ( f i ) ) using 1;
      · simp [ Matrix.toEuclideanLin, EuclideanSpace.norm_eq ];
        rw [ ← Equiv.sum_comp e.symm ] ; aesop;
      · simp [ EuclideanSpace.norm_eq, Matrix.opNorm ];
        exact Or.inl ( by rw [ ← Equiv.sum_comp f ] );
  · refine' ContinuousLinearMap.opNorm_le_bound _ _ fun a => _;
    · exact ContinuousLinearMap.opNorm_nonneg _;
    · convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( toEuclideanLin ( Matrix.reindex e f A ) ) ) ( fun i => a ( f.symm i ) ) using 1;
      · simp [ EuclideanSpace.norm_eq, Matrix.toEuclideanLin ];
        rw [ ← Equiv.sum_comp e.symm ] ; simp [ Matrix.mulVec, dotProduct ] ;
        grind;
      · congr! 2;
        simp [ EuclideanSpace.norm_eq]
        conv_lhs => rw [ ← Equiv.sum_comp f.symm ] ;

/--
Define U_rho as the Kronecker product of V_rho and the identity.
-/
noncomputable def U_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix (((dA × dB) × dB) × dC) (dA × dC) ℂ :=
  Matrix.kronecker (V_rho ρAB) (1 : Matrix dC dC ℂ)

/--
Define U_sigma as the Kronecker product of the identity and V_sigma.
-/
noncomputable def U_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dA × (dB × (dB × dC))) (dA × dC) ℂ :=
  Matrix.kronecker (1 : Matrix dA dA ℂ) (V_sigma σBC)

/--
The operator norm of the conjugate transpose is equal to the operator norm.
-/
theorem Matrix.opNorm_conjTranspose_eq_opNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) :
    Matrix.opNorm Aᴴ = Matrix.opNorm A := by
  unfold Matrix.opNorm
  rw [← ContinuousLinearMap.adjoint.norm_map (toEuclideanLin A).toContinuousLinearMap]
  rw [toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

theorem isometry_mul_conjTranspose_le_one {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.conjTranspose * V = 1) :
    V * V.conjTranspose ≤ 1 := by
  have h_pos : (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    simp [ sub_mul, mul_sub, ← Matrix.mul_assoc ];
    simp [ Matrix.mul_assoc, hV ];
  have h_pos : (1 - V * Vᴴ) = (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) := by
    simp_all [ Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul ];
  have h_pos : Matrix.PosSemidef (1 - V * Vᴴ) := by
    rw [ h_pos ] at *; apply Matrix.posSemidef_conjTranspose_mul_self;
  grind

/-
If `A†A = I` and `B†B = I` (both isometries into the same space), then `||(A†B)|| ≤ 1`,
  equivalently `(A†B)†(A†B) ≤ I`.
-/
theorem conjTranspose_isometry_mul_isometry_le_one {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (A : Matrix k m ℂ) (B : Matrix k n ℂ)
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (A.conjTranspose * B).conjTranspose * (A.conjTranspose * B) ≤ 1 := by
  have h_le : (Bᴴ * A) * (Bᴴ * A)ᴴ ≤ 1 := by
    have h_le : (Bᴴ * A) * (Bᴴ * A)ᴴ ≤ (Bᴴ * B) := by
      have h_le : (A * Aᴴ) ≤ 1 := by
        apply isometry_mul_conjTranspose_le_one A hA;
      -- Apply the fact that if $X \leq Y$, then $CXC^* \leq CYC^*$ for any matrix $C$.
      have h_conj : ∀ (C : Matrix n k ℂ) (X Y : Matrix k k ℂ), X ≤ Y → C * X * Cᴴ ≤ C * Y * Cᴴ :=
        fun C X Y a => Matrix.PosSemidef.mul_mul_conjTranspose_mono C a
      simpa [ Matrix.mul_assoc ] using h_conj Bᴴ ( A * Aᴴ ) 1 h_le;
    aesop;
  simpa [ Matrix.mul_assoc ] using h_le

/-! ### Helper lemmas for operator_ineq_SSA -/

/- Reindexing preserves the HermitianMat ordering. -/
theorem HermitianMat.reindex_le_reindex_iff {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (e : d ≃ d₂) (A B : HermitianMat d ℂ) :
    A.reindex e ≤ B.reindex e ↔ A ≤ B := by
  constructor <;> intro h <;> rw [HermitianMat.le_iff] at * <;> aesop;

/- Inverse of a Kronecker product of HermitianMat. -/
theorem HermitianMat.inv_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Nonempty m] [Nonempty n]
    (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    [A.NonSingular] [B.NonSingular] :
    (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ := by
  have h_inv : (A ⊗ₖ B).mat * (A⁻¹ ⊗ₖ B⁻¹).mat = 1 := by
    have h_inv : (A ⊗ₖ B).mat * (A⁻¹ ⊗ₖ B⁻¹).mat = (A.mat * A⁻¹.mat) ⊗ₖ (B.mat * B⁻¹.mat) := by
      ext i j; simp +decide [ Matrix.mul_apply, Matrix.kroneckerMap ] ;
      simp +decide only [mul_assoc, Finset.sum_mul _ _ _, Finset.mul_sum];
      rw [ ← Finset.sum_product' ] ; congr ; ext ; ring!;
    aesop;
  refine' Subtype.ext ( Matrix.inv_eq_right_inv h_inv )

/- Inverse of a reindexed HermitianMat. -/
theorem HermitianMat.inv_reindex {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (A : HermitianMat d ℂ) (e : d ≃ d₂) :
    (A.reindex e)⁻¹ = A⁻¹.reindex e := by
  ext1
  simp

/- Kronecker of PosDef matrices is PosDef. -/
theorem HermitianMat.PosDef_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    (A ⊗ₖ B).mat.PosDef := by
  exact Matrix.PosDef.kron hA hB

/- Reindex of PosDef is PosDef. -/
theorem HermitianMat.PosDef_reindex {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (A : HermitianMat d ℂ) (e : d ≃ d₂)
    (hA : A.mat.PosDef) :
    (A.reindex e).mat.PosDef := by
  convert hA.reindex e

/-- The intermediate operator inequality: ρ_AB ⊗ σ_C⁻¹ ≤ (ρ_A ⊗ σ_BC⁻¹).reindex(assoc⁻¹).
  This is derived from W_mat_sq_le_one by algebraic manipulation (conjugation and simplification). -/
theorem intermediate_ineq [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    ρAB ⊗ₖ (σBC.traceLeft)⁻¹ ≤
      (ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm := by
  sorry

open HermitianMat in
/-- **Operator extension of SSA** (Main result of Lin-Kim-Hsieh).
  For positive definite ρ_AB and σ_BC:
  `ρ_A⁻¹ ⊗ σ_BC ≤ ρ_AB⁻¹ ⊗ σ_C`
  where ρ_A = Tr_B(ρ_AB) and σ_C = Tr_B(σ_BC), and the RHS is reindexed
  via the associator `(dA × dB) × dC ≃ dA × (dB × dC)`. -/
theorem operator_ineq_SSA [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    ρAB.traceRight⁻¹ ⊗ₖ σBC ≤
      (ρAB⁻¹ ⊗ₖ σBC.traceLeft).reindex (Equiv.prodAssoc dA dB dC) := by
  have h_inv_symm : ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm)⁻¹ ≤ (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ := by
    apply HermitianMat.inv_antitone;
    · apply HermitianMat.PosDef_kronecker ρAB (σBC.traceLeft)⁻¹ hρ (PosDef_traceLeft σBC hσ).inv;
    · exact intermediate_ineq ρAB σBC hρ hσ;
  have h_inv_symm : ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm)⁻¹ = (ρAB.traceRight⁻¹ ⊗ₖ σBC).reindex (Equiv.prodAssoc dA dB dC).symm := by
    have h_inv_symm : (ρAB.traceRight ⊗ₖ σBC⁻¹)⁻¹ = ρAB.traceRight⁻¹ ⊗ₖ (σBC⁻¹)⁻¹ := by
      convert HermitianMat.inv_kronecker _ _ using 1;
      · infer_instance;
      · exact ⟨ ⟨ Classical.arbitrary dB, Classical.arbitrary dC ⟩ ⟩;
      · have h_trace_right_pos_def : (ρAB.traceRight).mat.PosDef := by
          exact PosDef_traceRight ρAB hρ
        exact ⟨by exact PosDef_traceRight ρAB hρ |>.isUnit⟩
      · have h_inv_symm : σBC⁻¹.NonSingular := by
          have h_inv_symm : σBC.NonSingular := by
            exact nonSingular_of_posDef hσ
          exact nonSingular_iff_inv.mpr h_inv_symm;
        exact h_inv_symm;
    convert congr_arg ( fun x : HermitianMat _ _ => x.reindex ( Equiv.prodAssoc dA dB dC ).symm ) h_inv_symm using 1;
    · apply HermitianMat.inv_reindex
    · convert rfl;
      apply HermitianMat.ext;
      convert Matrix.nonsing_inv_nonsing_inv _ _;
      exact isUnit_iff_ne_zero.mpr ( hσ.det_pos.ne' );
  have h_inv_symm : (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ = ρAB⁻¹ ⊗ₖ σBC.traceLeft := by
    have h_inv_symm : (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ = ρAB⁻¹ ⊗ₖ (σBC.traceLeft⁻¹)⁻¹ := by
      convert HermitianMat.inv_kronecker ρAB ( σBC.traceLeft⁻¹ ) using 1;
      · exact nonSingular_of_posDef hρ;
      · have h_inv_symm : σBC.traceLeft.mat.PosDef := by
          exact PosDef_traceLeft σBC hσ;
        -- Since σBC.traceLeft is positive definite, its inverse is also positive definite, and hence non-singular.
        have h_inv_pos_def : (σBC.traceLeft⁻¹).mat.PosDef := by
          convert h_inv_symm.inv using 1;
        exact nonSingular_of_posDef h_inv_pos_def;
    convert h_inv_symm using 1;
    have h_inv_symm : (σBC.traceLeft⁻¹)⁻¹ = σBC.traceLeft := by
      have h_inv_symm : (σBC.traceLeft⁻¹).mat * σBC.traceLeft.mat = 1 := by
        have h_inv_symm : (σBC.traceLeft⁻¹).mat * σBC.traceLeft.mat = 1 := by
          have h_inv_symm : σBC.traceLeft.mat.PosDef := by
            exact PosDef_traceLeft σBC hσ
          convert Matrix.nonsing_inv_mul _ _;
          exact isUnit_iff_ne_zero.mpr h_inv_symm.det_pos.ne';
        exact h_inv_symm
      have h_inv_symm : (σBC.traceLeft⁻¹ : HermitianMat dC ℂ).mat⁻¹ = σBC.traceLeft.mat := by
        rw [ Matrix.inv_eq_right_inv h_inv_symm ];
      exact Eq.symm (HermitianMat.ext (id (Eq.symm h_inv_symm)));
    rw [h_inv_symm];
  have h_inv_symm : (ρAB.traceRight⁻¹ ⊗ₖ σBC).reindex (Equiv.prodAssoc dA dB dC).symm ≤ ρAB⁻¹ ⊗ₖ σBC.traceLeft := by
    aesop;
  convert HermitianMat.reindex_le_reindex_iff ( Equiv.prodAssoc dA dB dC ) _ _ |>.2 h_inv_symm using 1

open scoped InnerProductSpace RealInnerProductSpace

/-- Strong subadditivity on a tripartite system -/
theorem Sᵥₙ_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.traceRight;
    let ρ₂₃ := ρ₁₂₃.traceLeft;
    let ρ₂ := ρ₁₂₃.traceLeft.traceRight;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ := by
  sorry

/-- "Ordinary" subadditivity of von Neumann entropy -/
theorem Sᵥₙ_subadditivity (ρ : MState (d₁ × d₂)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft := by
  have := Sᵥₙ_strong_subadditivity (ρ.relabel (d₂ := d₁ × Unit × d₂)
    ⟨fun x ↦ (x.1, x.2.2), fun x ↦ (x.1, ⟨(), x.2⟩), fun x ↦ by simp, fun x ↦ by simp⟩)
  simp [Sᵥₙ_relabel] at this
  convert this using 1
  congr 1
  · convert Sᵥₙ_relabel _ (Equiv.prodPUnit _).symm
    exact rfl
  · convert Sᵥₙ_relabel _ (Equiv.punitProd _).symm
    exact rfl

/-- Triangle inequality for pure tripartite states: S(A) ≤ S(B) + S(C). -/
theorem Sᵥₙ_pure_tripartite_triangle (ψ : Ket ((d₁ × d₂) × d₃)) :
    Sᵥₙ (MState.pure ψ).traceRight.traceRight ≤
    Sᵥₙ (MState.pure ψ).traceRight.traceLeft + Sᵥₙ (MState.pure ψ).traceLeft := by
  have h_subadd := Sᵥₙ_subadditivity (MState.pure ψ).assoc.traceLeft
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', (MState.pure ψ).assoc = _ :=
    MState.relabel_pure_exists ψ _
  grind [Sᵥₙ_of_partial_eq, MState.traceLeft_left_assoc,
    MState.traceLeft_right_assoc, MState.traceRight_assoc]

/-- One direction of the Araki-Lieb triangle inequality: S(A) ≤ S(B) + S(AB). -/
theorem Sᵥₙ_triangle_ineq_one_way (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.traceRight ≤ Sᵥₙ ρ.traceLeft + Sᵥₙ ρ := by
  have := Sᵥₙ_pure_tripartite_triangle ρ.purify
  have := Sᵥₙ_of_partial_eq ρ.purify
  aesop

/-- Araki-Lieb triangle inequality on von Neumann entropy -/
theorem Sᵥₙ_triangle_subaddivity (ρ : MState (d₁ × d₂)) :
    abs (Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft) ≤ Sᵥₙ ρ := by
  rw [abs_sub_le_iff]
  constructor
  · have := Sᵥₙ_triangle_ineq_one_way ρ
    grind only
  · have := Sᵥₙ_triangle_ineq_one_way ρ.SWAP
    grind only [Sᵥₙ_triangle_ineq_one_way, Sᵥₙ_of_SWAP_eq, MState.traceRight_SWAP,
      MState.traceLeft_SWAP]

section weak_monotonicity
--TODO Cleanup

variable (ρ : MState (dA × dB × dC))

/-
Permutations of the purification system for use in the proof of weak monotonicity.
-/
private def perm_B_ACR : (dA × dB × dC) × (dA × dB × dC) ≃ dB × (dA × dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (b, (a,c,r))
  invFun x := let (b, (a,c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_C_ABR : (dA × dB × dC) × (dA × dB × dC) ≃ dC × (dA × dB × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (c, (a,b,r))
  invFun x := let (c, (a,b,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_AC_BR : (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dC) × (dB × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,c), (b,r))
  invFun x := let ((a,c), (b,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_AB_CR : (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dB) × (dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,b), (c,r))
  invFun x := let ((a,b), (c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The state on systems A, B, and R, obtained by purifying ρ and tracing out C. -/
private def ρABR (ρ : MState (dA × dB × dC)) : MState (dA × dB × (dA × dB × dC)) :=
  ((MState.pure ρ.purify).relabel perm_C_ABR.symm).traceLeft

private lemma traceRight_relabel_perm_C_ABR
    (ρ : MState ((dA × dB × dC) × (dA × dB × dC))) :
    (ρ.relabel perm_C_ABR.symm).traceRight = ρ.traceRight.traceLeft.traceLeft := by
  ext i j;
  simp [ HermitianMat.traceRight, HermitianMat.traceLeft, perm_C_ABR ];
  simp [ Matrix.traceRight, Matrix.traceLeft ];
  simp [ Fintype.sum_prod_type ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ac_rfl )

private lemma trace_relabel_purify_eq_rho_C :
    ((MState.pure ρ.purify).relabel perm_C_ABR.symm).traceRight = ρ.traceLeft.traceLeft := by
  have := MState.purify_spec ρ;
  convert traceRight_relabel_perm_C_ABR _ using 1;
  rw [ this ]

private theorem S_B_eq_S_ACR (ρ : MState (dA × dB × dC)) :
    Sᵥₙ ((MState.pure ρ.purify).relabel perm_B_ACR.symm).traceRight = Sᵥₙ ρ.traceLeft.traceRight := by
  have := @MState.purify_spec;
  convert congr_arg Sᵥₙ ( this ρ |> congr_arg ( fun ρ => ρ.traceLeft.traceRight ) ) using 1;
  convert Sᵥₙ_relabel _ _ using 2;
  swap;
  exact Equiv.refl dB;
  ext; simp [ MState.traceRight, MState.traceLeft ] ;
  simp [HermitianMat.traceLeft, HermitianMat.traceRight ];
  simp [ Matrix.traceRight, Matrix.traceLeft ];
  simp [ Fintype.sum_prod_type ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ac_rfl )

/-
The entropy of the B marginal of the purification is equal to the entropy of the B marginal of the original state.
-/
private lemma S_B_eq_S_B :
    Sᵥₙ (ρABR ρ).traceLeft.traceRight = Sᵥₙ ρ.assoc'.traceRight.traceLeft := by
  convert S_B_eq_S_ACR ρ using 1;
  · congr 1
    ext1
    unfold ρABR;
    ext
    simp [MState.traceLeft, MState.traceRight]
    unfold perm_C_ABR perm_B_ACR
    simp [HermitianMat.traceLeft, HermitianMat.traceRight]
    simp [Matrix.traceLeft, Matrix.traceRight]
    simp [ ← Finset.sum_product']
    exact Finset.sum_bij ( fun x _ => ( x.2.1, x.2.2, x.1 ) ) ( by aesop ) ( by aesop ) ( by aesop ) ( by aesop );
  · simp

/-
The entropy of the ABR state is equal to the entropy of C, since ABCR is pure.
-/
private theorem S_ABR_eq_S_C : Sᵥₙ (ρABR ρ) = Sᵥₙ ρ.traceLeft.traceLeft := by
  rw [ρABR, Sᵥₙ_pure_complement, trace_relabel_purify_eq_rho_C]

/-
The BR marginal of ρABR is equal to the BR marginal of the purification relabeled.
-/
private lemma traceLeft_ρABR_eq_traceLeft_relabel :
    (ρABR ρ).traceLeft = ((MState.pure ρ.purify).relabel perm_AC_BR.symm).traceLeft := by
  unfold ρABR;
  unfold MState.traceLeft;
  congr;
  ext i j
  simp [ HermitianMat.traceLeft];
  simp [ Matrix.traceLeft];
  simp [ perm_C_ABR, perm_AC_BR ];
  simp [ Fintype.sum_prod_type ]

/-
Tracing out B and R from the relabeled state is equivalent to tracing out R, then B from the original state (with appropriate permutations).
-/
private lemma traceRight_relabel_perm_AC_BR (ρ : MState ((dA × dB × dC) × (dA × dB × dC))) :
    (ρ.relabel perm_AC_BR.symm).traceRight = ρ.traceRight.SWAP.assoc.traceLeft.SWAP := by
  unfold MState.traceRight MState.SWAP MState.assoc MState.relabel
  simp [ HermitianMat.traceRight, HermitianMat.traceLeft ];
  simp [ Matrix.traceLeft, Matrix.traceRight, HermitianMat.reindex, Matrix.submatrix ];
  simp [ perm_AC_BR ];
  simp [ Fintype.sum_prod_type ]

/-
Tracing out B and R from the purification gives the marginal state on A and C.
-/
private lemma traceRight_relabel_perm_AC_BR_eq_rho_AC :
    ((MState.pure ρ.purify).relabel perm_AC_BR.symm).traceRight = ρ.SWAP.assoc.traceLeft.SWAP := by
  rw [traceRight_relabel_perm_AC_BR]
  rw [MState.purify_spec]

/-
The entropy of the BR marginal of the purification is equal to the entropy of the AC marginal of the original state.
-/
private lemma S_BR_eq_S_AC :
    Sᵥₙ (ρABR ρ).traceLeft = Sᵥₙ ρ.SWAP.assoc.traceLeft.SWAP := by
  rw [traceLeft_ρABR_eq_traceLeft_relabel]
  rw [Sᵥₙ_pure_complement, traceRight_relabel_perm_AC_BR_eq_rho_AC]

private theorem S_AB_purify_eq_S_AB_rho :
    Sᵥₙ ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = Sᵥₙ ρ.assoc'.traceRight := by
  have h_trace : ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = ((MState.pure ρ.purify).traceRight).assoc'.traceRight := by
    ext; simp [MState.traceRight, MState.assoc'];
    simp [HermitianMat.traceRight]
    simp [ Matrix.submatrix, Matrix.traceRight ];
    congr! 2;
    ext i j; simp [ perm_AB_CR ] ;
    exact
      Fintype.sum_prod_type fun x =>
        ρ.purify ((i.1, i.2, x.1), x.2) * (starRingEnd ℂ) (ρ.purify ((j.1, j.2, x.1), x.2));
  aesop

/-
The entropy of the AB marginal of the purification is equal to the entropy of the AB marginal of the original state.
-/
private lemma S_AB_eq_S_AB :
    Sᵥₙ (ρABR ρ).assoc'.traceRight = Sᵥₙ ρ.assoc'.traceRight := by
  have h_marginal : Sᵥₙ ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = Sᵥₙ ρ.assoc'.traceRight := by
    exact S_AB_purify_eq_S_AB_rho ρ
  convert h_marginal using 2;
  convert MState.ext ?_;
  ext i j; simp [ ρABR ] ;
  simp [ MState.traceLeft, MState.relabel, MState.assoc', perm_AB_CR, perm_C_ABR ];
  simp [ MState.SWAP, MState.assoc]
  simp [ MState.pure ];
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, HermitianMat.reindex ];
  simp [ Matrix.traceLeft, Matrix.traceRight, Matrix.submatrix, Matrix.vecMulVec ];
  simp [ Fintype.sum_prod_type ];
  simp only [Finset.sum_sigma'];
  refine' Finset.sum_bij ( fun x _ => ⟨ x.snd.snd.snd, x.fst, x.snd.fst, x.snd.snd.fst ⟩ ) _ _ _ _ <;> simp
  · aesop;
  · exact fun b => ⟨ b.2.1, b.2.2.1, b.2.2.2, b.1, rfl ⟩

/-- Weak monotonicity of quantum conditional entropy: S(A|B) + S(A|C) ≥ 0. -/
theorem Sᵥₙ_weak_monotonicity :
    let ρAB := ρ.assoc'.traceRight
    let ρAC := ρ.SWAP.assoc.traceLeft.SWAP
    0 ≤ qConditionalEnt ρAB + qConditionalEnt ρAC := by
  -- Apply strong subadditivity to the state ρABR.
  have h_strong_subadditivity := Sᵥₙ_strong_subadditivity (ρABR ρ)
  -- Substitute the equalities for the entropies of the purifications.
  have _ := S_ABR_eq_S_C ρ
  have _ := S_B_eq_S_B ρ
  have _ := S_AB_eq_S_AB ρ
  have _ := S_BR_eq_S_AC ρ
  grind [qConditionalEnt, MState.traceRight_left_assoc', Sᵥₙ_of_SWAP_eq,
    MState.traceLeft_SWAP, MState.traceLeft_right_assoc, MState.traceRight_SWAP]

end weak_monotonicity

/-- Strong subadditivity, stated in terms of conditional entropies.
  Also called the data processing inequality. H(A|BC) ≤ H(A|B). -/
theorem qConditionalEnt_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qConditionalEnt ρ₁₂₃ ≤ qConditionalEnt ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qConditionalEnt, MState.traceRight_left_assoc']
  linarith

/-- Strong subadditivity, stated in terms of quantum mutual information.
  I(A;BC) ≥ I(A;B). -/
theorem qMutualInfo_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qMutualInfo ρ₁₂₃ ≥ qMutualInfo ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qMutualInfo, MState.traceRight_left_assoc', MState.traceRight_right_assoc']
  linarith

/-- The quantum conditional mutual information `QCMI` is nonnegative. -/
theorem qcmi_nonneg (ρ : MState (dA × dB × dC)) :
    0 ≤ qcmi ρ := by
  simp [qcmi, qConditionalEnt]
  have := Sᵥₙ_strong_subadditivity ρ
  linarith

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dA. -/
theorem qcmi_le_2_log_dim (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dA) := by
  have := Sᵥₙ_subadditivity ρ.assoc'.traceRight
  have := abs_le.mp (Sᵥₙ_triangle_subaddivity ρ)
  grind [qcmi, qConditionalEnt, Sᵥₙ_nonneg, Sᵥₙ_le_log_d]

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dC. -/
theorem qcmi_le_2_log_dim' (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dC) := by
  have h_araki_lieb_assoc' : Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft ≤ Sᵥₙ ρ := by
    apply le_of_abs_le
    rw [← ρ.traceLeft_assoc', ← Sᵥₙ_of_assoc'_eq ρ]
    exact Sᵥₙ_triangle_subaddivity ρ.assoc'
  have := Sᵥₙ_subadditivity ρ.traceLeft
  grind [qcmi, qConditionalEnt, Sᵥₙ_le_log_d, MState.traceRight_left_assoc']

/- The chain rule for quantum conditional mutual information:
`I(A₁A₂ : C | B) = I(A₁:C|B) + I(A₂:C|BA₁)`.

It should be something like this, but it's hard to track the indices correctly:
theorem qcmi_chain_rule (ρ : MState ((dA₁ × dA₂) × dB × dC)) :
    let ρA₁BC := ρ.assoc.SWAP.assoc.traceLeft.SWAP;
    let ρA₂BA₁C : MState (dA₂ × (dA₁ × dB) × dC) :=
      ((CPTPMap.id ⊗ₖ CPTPMap.assoc').compose (CPTPMap.assoc.compose (CPTPMap.SWAP ⊗ₖ CPTPMap.id))) ρ;
    qcmi ρ = qcmi ρA₁BC + qcmi ρA₂BA₁C
     := by
  admit
-/
