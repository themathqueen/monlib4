/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import QuantumGraph.Nontracial
import LinearAlgebra.MyIps.MinimalProj
import QuantumGraph.Iso

#align_import quantum_graph.to_projections

/-!

# Quantum graphs as projections

This file contains the definition of a quantum graph as a projection, and the proof that the 

-/


variable {p : Type _} [Fintype p] [DecidableEq p] {n : p → Type _} [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)]

open scoped TensorProduct BigOperators Kronecker Functional

-- local notation `ℍ` := matrix (n i) (n i) ℂ
local notation "ℍ" => Matrix p p ℂ

local notation "ℍ_" i => Matrix (n i) (n i) ℂ

-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "L(" x ")" => x →L[ℂ] x

local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable
  --{φ : Π i, module.dual ℂ (ℍ_ i)}
  --[hφ : ∀ i, fact (φ i).is_faithful_pos_map]
  {φ : Module.Dual ℂ ℍ}
  [hφ : Fact φ.IsFaithfulPosMap]

open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" => (TensorProduct.assoc ℂ ℍ ℍ ℍ : (ℍ ⊗[ℂ] ℍ) ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ)

local notation "υ⁻¹" =>
  ((TensorProduct.assoc ℂ ℍ ℍ ℍ).symm : ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ) ⊗[ℂ] ℍ)

local notation "ϰ" => (↑(TensorProduct.comm ℂ ℍ ℂ) : ℍ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] ℍ)

local notation "ϰ⁻¹" => ((TensorProduct.comm ℂ ℍ ℂ).symm : ℂ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℂ)

local notation "τ" => (TensorProduct.lid ℂ ℍ : ℂ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ)

local notation "τ⁻¹" => ((TensorProduct.lid ℂ ℍ).symm : ℍ →ₗ[ℂ] ℂ ⊗[ℂ] ℍ)

local notation "id" => (1 : ℍ →ₗ[ℂ] ℍ)

noncomputable def blockDiag'KroneckerEquiv {φ : ∀ i, Module.Dual ℂ (ℍ_ i)}
    (hφ : ∀ i, Fact (φ i).IsFaithfulPosMap) :
    Matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ ≃ₗ[ℂ]
      { x : Matrix (Σ i, n i) (Σ i, n i) ℂ // x.IsBlockDiagonal } ⊗[ℂ]
        { x : Matrix (Σ i, n i) (Σ i, n i) ℂ // x.IsBlockDiagonal } :=
  ((Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hφ i).elim).symm.toLinearEquiv.trans
        ((Module.Dual.pi.IsFaithfulPosMap.psi hφ 0 0).trans
          (LinearEquiv.TensorProduct.map (1 : (∀ i, Matrix (n i) (n i) ℂ) ≃ₗ[ℂ] _)
            (Pi.transposeAlgEquiv p n : _ ≃ₐ[ℂ] _ᵐᵒᵖ).symm.toLinearEquiv))).trans
    (LinearEquiv.TensorProduct.map isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv
      isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv)

#print LinearEquiv.coe_one /-
theorem LinearEquiv.coe_one {R : Type _} [Semiring R] (M : Type _) [AddCommMonoid M] [Module R M] :
    ↑(1 : M ≃ₗ[R] M) = (1 : M →ₗ[R] M) :=
  rfl
-/

theorem Matrix.conj_conj_transpose' {R n₁ n₂ : Type _} [InvolutiveStar R] (A : Matrix n₁ n₂ R) :
    Aᴴᵀᴴ = Aᵀ := by rw [← conj_conj_transpose A] <;> rfl

theorem toMatrix_mulLeft_mulRight_adjoint {φ : ∀ i, Module.Dual ℂ (Matrix (n i) (n i) ℂ)}
    (hφ : ∀ i, Fact (φ i).IsFaithfulPosMap) (x y : ∀ i, ℍ_ i) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hφ i).elim)
        (LinearMap.mulLeft ℂ x * ((LinearMap.mulRight ℂ y).adjoint : l(∀ i, ℍ_ i))) =
      blockDiagonal' fun i => x i ⊗ₖ ((hφ i).elim.sig (1 / 2) (y i))ᴴᵀ :=
  by
  have : (1 / 2 : ℝ) + (-1 : ℝ) = -(1 / 2) := by norm_num
  simp_rw [_root_.map_mul, ← lmul_eq_mul, ← rmul_eq_mul, rmul_adjoint, pi_lmul_toMatrix,
    pi_rmul_toMatrix, mul_eq_mul, ← block_diagonal'_mul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks, Pi.star_apply,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, star_eq_conj_transpose, this, ←
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose]
  rfl

@[instance]
private def smul_comm_class_aux {ι₂ : Type _} {E₂ : ι₂ → Type _} [∀ i, AddCommMonoid (E₂ i)]
    [∀ i, Module ℂ (E₂ i)] : ∀ i : ι₂, SMulCommClass ℂ ℂ (E₂ i) := fun i => by infer_instance

@[simps]
def Pi.LinearMap.apply {ι₁ ι₂ : Type _} {E₁ : ι₁ → Type _} [DecidableEq ι₁] [Fintype ι₁]
    [∀ i, AddCommMonoid (E₁ i)] [∀ i, Module ℂ (E₁ i)] {E₂ : ι₂ → Type _}
    [∀ i, AddCommMonoid (E₂ i)] [∀ i, Module ℂ (E₂ i)] (i : ι₁) (j : ι₂) :
    ((∀ a, E₁ a) →ₗ[ℂ] ∀ a, E₂ a) →ₗ[ℂ] E₁ i →ₗ[ℂ] E₂ j
    where
  toFun x :=
    { toFun := fun a => (x ((LinearMap.single i : E₁ i →ₗ[ℂ] ∀ b, E₁ b) a)) j
      map_add' := fun a b => by simp only [LinearMap.add_apply, map_add, Pi.add_apply]
      map_smul' := fun c a => by
        simp only [LinearMap.smul_apply, LinearMap.map_smul, Pi.smul_apply, RingHom.id_apply] }
  map_add' x y := by
    ext a
    simp only [LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk]
  map_smul' c x := by
    ext a
    simp only [LinearMap.smul_apply, Pi.smul_apply, LinearMap.map_smul, RingHom.id_apply,
      LinearMap.coe_mk]

theorem rankOne_psi_transpose_to_lin {n : Type _} [DecidableEq n] [Fintype n]
    {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : Fact φ.IsFaithfulPosMap] (x y : Matrix n n ℂ) :
    hφ.elim.toMatrix.symm
        ((TensorProduct.map (1 : l(Matrix n n ℂ)) (transposeAlgEquiv n ℂ ℂ).symm.toLinearMap)
            ((hφ.elim.psi 0 (1 / 2)) |x⟩⟨y|)).toKronecker =
      LinearMap.mulLeft ℂ x * ((LinearMap.mulRight ℂ y).adjoint : l(Matrix n n ℂ)) :=
  by
  let b := @Module.Dual.IsFaithfulPosMap.orthonormalBasis n _ _ φ _
  rw [← Function.Injective.eq_iff hφ.elim.to_matrix.injective]
  simp_rw [_root_.map_mul, LinearMap.Matrix.mulRight_adjoint, LinearMap.mulRight_toMatrix,
    LinearMap.mulLeft_toMatrix, Matrix.hMul_eq_hMul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Module.Dual.IsFaithfulPosMap.sig_apply_sig]
  have : (1 / 2 : ℝ) + -1 = -(1 / 2) := by norm_num
  rw [this, ← Module.Dual.IsFaithfulPosMap.sig_conjTranspose, AlgEquiv.apply_symm_apply,
    Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, TensorProduct.map_tmul,
    TensorProduct.toKronecker_apply, Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.one_apply,
    AlgEquiv.toLinearMap_apply, op, LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv,
    transpose_alg_equiv_symm_op_apply]

private theorem matrix.std_basis_matrix.transpose' {R n p : Type _} [DecidableEq n] [DecidableEq p]
    [Semiring R] (i : n) (j : p) : (stdBasisMatrix i j (1 : R))ᵀ = stdBasisMatrix j i (1 : R) :=
  by
  ext1
  simp_rw [transpose_apply, std_basis_matrix, and_comm']

-- example :
--   -- { x : matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ // x.is_block_diagonal }
--   matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ
--     ≃ₐ[ℂ]
--   { x : matrix (Σ i : p × p, n i.1 × n i.2) (Σ i : p × p, n i.1 × n i.2) ℂ // x.is_block_diagonal }
--   -- {x : (matrix (Σ i, n i) (Σ i, n i) ℂ) ⊗[ℂ] (matrix (Σ i, n i) (Σ i, n i) ℂ) // x.is_block_diagonal}
--   -- {x : matrix (Σ i, n i) (Σ i, n i) ℂ // x.is_block_diagonal} :=
--   -- (Π i, matrix (n i) (n i) ℂ) ⊗[ℂ] (Π i, matrix (n i) (n i) ℂ)
--   :=
-- { to_fun := λ x, by {  },
--   -- dite (a.1.1 = b.1.1)
--   -- (λ h1,
--   --   dite (a.1.1 = a.2.1 ∧ b.1.1 = b.2.1) (
--   --   λ h : a.1.1 = a.2.1 ∧ b.1.1 = b.2.1,
--   --   let a' : n a.1.1 := by rw [h.1]; exact a.2.2 in
--   --   let b' : n b.1.1 := by rw [h.2]; exact b.2.2 in
--   --   x (⟨a.1.1, a.1.2, a'⟩) (⟨b.1.1, b.1.2, b'⟩))
--   -- (λ h, 0),
--   inv_fun := λ x a b, x (⟨a.1, a.2.1⟩, ⟨a.1, a.2.2⟩) (⟨b.1, b.2.1⟩, ⟨b.1, b.2.2⟩),
--   left_inv := λ x, by
--   { ext1,
--     simp only [],
--     split_ifs,
--     tidy, },
--   right_inv := λ x, by
--   { ext1,
--     simp only [],
--     split_ifs,
--     tidy, },
--      }
theorem rankOne_toMatrix_transpose_psi_symm (x y : ℍ) :
    (hφ.elim.psi 0 (1 / 2)).symm
        ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).toLinearMap)
          (hφ.elim.toMatrix |x⟩⟨y|).kroneckerToTensorProduct) =
      LinearMap.mulLeft ℂ (x ⬝ φ.Matrix) * ((LinearMap.mulRight ℂ (φ.Matrix ⬝ y)).adjoint : l(ℍ)) :=
  by
  rw [kmul_representation (hφ.elim.to_matrix |x⟩⟨y|)]
  simp_rw [map_sum, SMulHomClass.map_smul, kronecker_to_tensor_product_apply,
    TensorProduct.map_tmul, LinearMap.one_apply, AlgEquiv.toLinearMap_apply,
    transpose_alg_equiv_apply, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_symm_mk,
    Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, unop, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv_symm, MulOpposite.unop_op, matrix.std_basis_matrix.transpose',
    std_basis_matrix_conj_transpose, neg_zero, Module.Dual.IsFaithfulPosMap.sig_zero, star_one,
    LinearMap.Matrix.mulRight_adjoint, LinearMap.ext_iff, LinearMap.sum_apply, LinearMap.mul_apply,
    LinearMap.smul_apply, ContinuousLinearMap.coe_coe, rankOne_apply, rankOne_toMatrix,
    conj_transpose_col, ← vec_mul_vec_eq, vec_mul_vec_apply, Pi.star_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, reshape_apply]
  have :
    ∀ (i j : p) (a : ℍ),
      ⟪hφ.elim.sig (-(1 / 2)) e_{i,j}, a⟫_ℂ =
        ⟪e_{i,j} ⬝ hφ.elim.matrix_is_pos_def.rpow (-(1 / 2)),
          hφ.elim.matrix_is_pos_def.rpow (1 / 2) ⬝ a⟫_ℂ :=
    by
    intro i j a
    simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, neg_neg, ←
      Module.Dual.IsFaithfulPosMap.basis_apply hφ.elim (i, j),
      Module.Dual.IsFaithfulPosMap.inner_left_hMul, Module.Dual.IsFaithfulPosMap.inner_coord',
      (pos_def.rpow.is_hermitian _ _).Eq]
  intro a
  simp_rw [this, ← hφ.elim.basis_apply (_, _), Module.Dual.IsFaithfulPosMap.inner_coord', ←
    conj_transpose_apply, smul_smul, mul_assoc, ← Finset.sum_smul, ← Finset.mul_sum,
    mul_comm _ ((_ ⬝ a ⬝ _) _ _), ← mul_apply, ← smul_std_basis_matrix', conj_transpose_mul,
    (pos_def.rpow.is_hermitian _ _).Eq, Matrix.mul_assoc, ←
    Matrix.mul_assoc (hφ.elim.matrix_is_pos_def.rpow _) (hφ.elim.matrix_is_pos_def.rpow _),
    pos_def.rpow_mul_rpow, add_halves, pos_def.rpow_one_eq_self, hφ.elim.matrix_is_pos_def.1.Eq,
    sig_apply_matrix_hMul_pos_def', ← mul_eq_mul, ← mul_assoc]
  nth_rw_lhs 1 [← matrix_eq_sum_std_basis]

@[instance]
private def hmm {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (U : Submodule ℂ H) : CompleteSpace U :=
  FiniteDimensional.complete ℂ U

private theorem lm_to_clm_comp {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p q : E →ₗ[𝕜] E} :
    p.toContinuousLinearMap * q.toContinuousLinearMap = (p * q).toContinuousLinearMap :=
  rfl

private theorem is_idempotent_elem_to_clm {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    IsIdempotentElem p ↔ IsIdempotentElem p.toContinuousLinearMap := by
  simp_rw [IsIdempotentElem, lm_to_clm_comp, Function.Injective.eq_iff (LinearEquiv.injective _),
    iff_self_iff]

private theorem is_self_adjoint_to_clm {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    IsSelfAdjoint p ↔ IsSelfAdjoint p.toContinuousLinearMap := by
  simp_rw [_root_.is_self_adjoint, ContinuousLinearMap.star_eq_adjoint, ←
    LinearMap.adjoint_toContinuousLinearMap, Function.Injective.eq_iff (LinearEquiv.injective _),
    LinearMap.star_eq_adjoint, iff_self_iff]

theorem orthogonal_projection_iff_lm {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    (∃ U : Submodule 𝕜 E, (orthogonalProjection' U : E →ₗ[𝕜] E) = p) ↔
      IsSelfAdjoint p ∧ IsIdempotentElem p :=
  by
  have := @orthogonal_projection_iff 𝕜 E _ _ _ _ _ p.to_continuous_linear_map
  simp_rw [is_idempotent_elem_to_clm, is_self_adjoint_to_clm] at this ⊢
  rw [← this]
  constructor
  all_goals
    rintro ⟨U, hU⟩
    use U
  · rw [← hU]
    rfl
  · rw [hU]
    rfl

theorem Matrix.conj_eq_transpose_conjTranspose {R n₁ n₂ : Type _} [Star R] (A : Matrix n₁ n₂ R) :
    Aᴴᵀ = Aᵀᴴ :=
  rfl

theorem Matrix.conj_eq_conjTranspose_transpose {R n₁ n₂ : Type _} [Star R] (A : Matrix n₁ n₂ R) :
    Aᴴᵀ = Aᴴᵀ :=
  rfl

noncomputable def oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ :=
  StarAlgEquiv.ofAlgEquiv
    ((AlgEquiv.TensorProduct.map (1 : ℍ ≃ₐ[ℂ] ℍ) (transposeAlgEquiv p ℂ ℂ).symm).trans
      tensorToKronecker)
    (by
      intro x
      simp only [AlgEquiv.trans_apply]
      apply x.induction_on
      · simp only [star_zero, map_zero]
      · intro x₁ x₂
        let x₂' : ℍ := MulOpposite.unop x₂
        have : x₂ = MulOpposite.op x₂' := rfl
        simp only [TensorProduct.star_tmul, AlgEquiv.TensorProduct.map, AlgEquiv.coe_mk,
          Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
          AlgEquiv.one_apply]
        simp_rw [this, ← MulOpposite.op_star, transpose_alg_equiv_symm_op_apply, tensorToKronecker,
          AlgEquiv.coe_mk, TensorProduct.toKronecker_star, TensorProduct.star_tmul,
          star_eq_conj_transpose, ← Matrix.conj_eq_transpose_conjTranspose, ←
          Matrix.conj_eq_conjTranspose_transpose]
      · intro a b ha hb
        simp only [map_add, star_add, ha, hb])

theorem oneMapTranspose_eq (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
    (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _) x =
      ((TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap) x).toKronecker :=
  rfl

theorem oneMapTranspose_symm_eq (x : Matrix (p × p) (p × p) ℂ) :
    (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm x =
      (TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv p ℂ ℂ).toLinearMap)
        x.kroneckerToTensorProduct :=
  rfl

theorem oneMapTranspose_apply (x y : ℍ) :
    (oneMapTranspose : _ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ) (x ⊗ₜ MulOpposite.op y) = x ⊗ₖ yᵀ :=
  by
  rw [oneMapTranspose_eq, TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
    TensorProduct.toKronecker_apply, transpose_alg_equiv_symm_op_apply]
  rfl

theorem to_matrix''_map_star (x : l(ℍ)) :
    hφ.elim.toMatrix (x : l(ℍ)).adjoint = star (hφ.elim.toMatrix x) :=
  by
  ext1
  simp only [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply, Pi.star_apply,
    star_apply, star_eq_conj_transpose, conj_transpose_apply, LinearMap.star_eq_adjoint,
    LinearMap.adjoint_inner_right, IsROrC.star_def, inner_conj_symm,
    Module.Dual.IsFaithfulPosMap.basis_repr_apply]

private theorem ffsugh {x : Matrix (p × p) (p × p) ℂ} {y : l(ℍ)} :
    hφ.elim.toMatrix.symm x = y ↔ x = hφ.elim.toMatrix y :=
  Equiv.symm_apply_eq _

theorem to_matrix''_symm_map_star (x : Matrix (p × p) (p × p) ℂ) :
    hφ.elim.toMatrix.symm (star x) = (hφ.elim.toMatrix.symm x).adjoint := by
  rw [ffsugh, to_matrix''_map_star, AlgEquiv.apply_symm_apply]

theorem Qam.idempotent_and_real_iff_exists_ortho_proj (A : l(ℍ)) :
    Qam.reflIdempotent hφ.elim A A = A ∧ A.IsReal ↔
      ∃ U : Submodule ℂ ℍ,
        (orthogonalProjection' U : l(ℍ)) =
          hφ.elim.toMatrix.symm
            ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
                ((hφ.elim.psi 0 (1 / 2)) A)).toKronecker :=
  by
  rw [Qam.isReal_and_idempotent_iff_psi_orthogonal_projection, orthogonal_projection_iff_lm, ←
    oneMapTranspose_eq, IsIdempotentElem.algEquiv, IsIdempotentElem.starAlgEquiv, and_comm']
  simp_rw [_root_.is_self_adjoint, LinearMap.star_eq_adjoint, ← to_matrix''_symm_map_star, ←
    map_star, Function.Injective.eq_iff (AlgEquiv.injective _),
    Function.Injective.eq_iff (StarAlgEquiv.injective _), iff_self_iff]

noncomputable def Qam.submoduleOfIdempotentAndReal {A : l(ℍ)}
    (hA1 : Qam.reflIdempotent hφ.elim A A = A) (hA2 : A.IsReal) : Submodule ℂ ℍ :=
  by
  choose U hU using (Qam.idempotent_and_real_iff_exists_ortho_proj A).mp ⟨hA1, hA2⟩
  exact U

theorem Qam.orthogonalProjection'_eq {A : l(ℍ)} (hA1 : Qam.reflIdempotent hφ.elim A A = A)
    (hA2 : A.IsReal) :
    (orthogonalProjection' (Qam.submoduleOfIdempotentAndReal hA1 hA2) : l(ℍ)) =
      hφ.elim.toMatrix.symm
        ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
            ((hφ.elim.psi 0 (1 / 2)) A)).toKronecker :=
  Qam.SubmoduleOfIdempotentAndReal._proof_8 hA1 hA2

noncomputable def Qam.onbOfIdempotentAndReal {A : l(ℍ)} (hA1 : Qam.reflIdempotent hφ.elim A A = A)
    (hA2 : A.IsReal) :
    OrthonormalBasis (Fin (FiniteDimensional.finrank ℂ (Qam.submoduleOfIdempotentAndReal hA1 hA2)))
      ℂ (Qam.submoduleOfIdempotentAndReal hA1 hA2) :=
  stdOrthonormalBasis ℂ _

theorem Qam.IdempotentAndReal.eq {A : l(ℍ)} (hA1 : Qam.reflIdempotent hφ.elim A A = A)
    (hA2 : A.IsReal) :
    A =
      ∑ i,
        LinearMap.mulLeft ℂ ((Qam.onbOfIdempotentAndReal hA1 hA2 i : ℍ) ⬝ φ.Matrix) *
          (LinearMap.mulRight ℂ (φ.Matrix ⬝ (Qam.onbOfIdempotentAndReal hA1 hA2 i : ℍ))).adjoint :=
  by
  let U := Qam.submoduleOfIdempotentAndReal hA1 hA2
  simp_rw [← rankOne_toMatrix_transpose_psi_symm, ← map_sum, ← ContinuousLinearMap.coe_sum, ←
    OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne (Qam.onbOfIdempotentAndReal hA1 hA2),
    Qam.orthogonalProjection'_eq, AlgEquiv.apply_symm_apply]
  simp_rw [← oneMapTranspose_symm_eq, ← oneMapTranspose_eq, StarAlgEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

def RealQam (hφ : φ.IsFaithfulPosMap) (A : l(ℍ)) :=
  Qam.reflIdempotent hφ A A = A ∧ A.IsReal

theorem RealQam.add_iff {A B : ℍ →ₗ[ℂ] ℍ} (hA : RealQam hφ.elim A) (hB : RealQam hφ.elim B) :
    RealQam hφ.elim (A + B) ↔ Qam.reflIdempotent hφ.elim A B + Qam.reflIdempotent hφ.elim B A = 0 :=
  by
  simp only [RealQam] at hA hB ⊢
  simp_rw [map_add, LinearMap.add_apply, hA, hB, add_assoc, add_left_cancel_iff, ← add_assoc,
    add_left_eq_self, add_comm, LinearMap.isReal_iff, LinearMap.real_add,
    (LinearMap.isReal_iff _).mp hA.2, (LinearMap.isReal_iff _).mp hB.2, eq_self_iff_true,
    and_true_iff, iff_self_iff]

def RealQam.zero : RealQam hφ.elim (0 : l(ℍ)) :=
  by
  simp_rw [RealQam, map_zero, eq_self_iff_true, true_and_iff]
  intro
  simp only [LinearMap.zero_apply, star_zero]

@[instance]
noncomputable def RealQam.hasZero : Zero { x // RealQam hφ.elim x } where zero := ⟨0, RealQam.zero⟩

theorem Qam.reflIdempotent_zero (a : l(ℍ)) : Qam.reflIdempotent hφ.elim a 0 = 0 :=
  map_zero _

theorem Qam.zero_reflIdempotent (a : l(ℍ)) : Qam.reflIdempotent hφ.elim 0 a = 0 := by
  simp_rw [map_zero, LinearMap.zero_apply]

noncomputable def RealQam.edges {x : l(ℍ)} (hx : RealQam hφ.elim x) : ℕ :=
  FiniteDimensional.finrank ℂ (Qam.submoduleOfIdempotentAndReal hx.1 hx.2)

noncomputable def RealQam.edges' : { x : ℍ →ₗ[ℂ] ℍ // RealQam hφ.elim x } → ℕ := fun x =>
  FiniteDimensional.finrank ℂ
    (Qam.submoduleOfIdempotentAndReal (Set.mem_setOf.mp (Subtype.mem x)).1
      (Set.mem_setOf.mp (Subtype.mem x)).2)

theorem RealQam.edges_eq {A : l(ℍ)} (hA : RealQam hφ.elim A) :
    (hA.edges : ℂ) = (A φ.Matrix⁻¹).trace :=
  by
  obtain ⟨hA1, hA2⟩ := hA
  nth_rw_rhs 1 [Qam.IdempotentAndReal.eq hA1 hA2]
  let U := Qam.submoduleOfIdempotentAndReal hA1 hA2
  simp_rw [LinearMap.sum_apply, LinearMap.Matrix.mulRight_adjoint, LinearMap.mul_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, conj_transpose_mul,
    hφ.elim.matrix_is_pos_def.1.Eq, mul_eq_mul, ← Matrix.mul_assoc, sig_apply_matrix_hMul_pos_def']
  have :
    ∀ x : Fin (FiniteDimensional.finrank ℂ ↥U),
      (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) ⬝ φ.matrix ⬝ φ.matrix⁻¹ ⬝ φ.matrix ⬝
            ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace =
        1 :=
    by
    intro x
    calc
      (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) ⬝ φ.matrix ⬝ φ.matrix⁻¹ ⬝ φ.matrix ⬝
              ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace =
          (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) ⬝ hφ.elim.matrix_is_pos_def.rpow 1 ⬝
                  hφ.elim.matrix_is_pos_def.rpow (-1) ⬝
                φ.matrix ⬝
              ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace :=
        by simp_rw [pos_def.rpow_one_eq_self, pos_def.rpow_neg_one_eq_inv_self]
      _ =
          (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) ⬝
                  (hφ.elim.matrix_is_pos_def.rpow 1 ⬝ hφ.elim.matrix_is_pos_def.rpow (-1)) ⬝
                φ.matrix ⬝
              ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace :=
        by simp_rw [Matrix.mul_assoc]
      _ =
          (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) ⬝ φ.matrix ⬝
              ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace :=
        by simp_rw [pos_def.rpow_mul_rpow, add_neg_self, pos_def.rpow_zero, Matrix.mul_one]
      _ = ⟪↑(Qam.onbOfIdempotentAndReal hA1 hA2 x), ↑(Qam.onbOfIdempotentAndReal hA1 hA2 x)⟫_ℂ :=
        by
        simp_rw [Module.Dual.IsFaithfulPosMap.inner_eq']
        rw [← trace_mul_cycle]
      _ = ⟪Qam.onbOfIdempotentAndReal hA1 hA2 x, Qam.onbOfIdempotentAndReal hA1 hA2 x⟫_ℂ := rfl
      _ = 1 := _
    · rw [← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_self,
        EuclideanSpace.single_apply]
      simp_rw [eq_self_iff_true, if_true]
  simp_rw [trace_sum, ← Matrix.mul_assoc, this, Finset.sum_const, Finset.card_fin,
    Nat.smul_one_eq_coe, Nat.cast_inj]
  rfl

theorem completeGraphRealQam : RealQam hφ.elim (Qam.completeGraph ℍ) :=
  ⟨Qam.Nontracial.CompleteGraph.qam, Qam.Nontracial.CompleteGraph.isReal⟩

theorem Qam.completeGraph_edges :
    (@completeGraphRealQam p _ _ φ hφ).edges = FiniteDimensional.finrank ℂ (⊤ : Submodule ℂ ℍ) :=
  by
  have :=
    calc
      (RealQam.edges completeGraphRealQam : ℂ) = (Qam.completeGraph ℍ φ.matrix⁻¹).trace :=
        RealQam.edges_eq _
  haveI ig := hφ.elim.matrix_is_pos_def.invertible
  simp_rw [Qam.completeGraph, ContinuousLinearMap.coe_coe, rankOne_apply,
    Module.Dual.IsFaithfulPosMap.inner_eq', conj_transpose_one, Matrix.mul_one,
    mul_inv_of_invertible, trace_smul, smul_eq_mul, trace_one] at this
  norm_cast at this
  simp_rw [Qam.completeGraph, this, finrank_top, FiniteDimensional.finrank_matrix]

theorem Qam.trivialGraphRealQam [Nontrivial p] : RealQam hφ.elim (Qam.trivialGraph hφ rfl) :=
  ⟨Qam.Nontracial.TrivialGraph.qam rfl, Qam.Nontracial.trivialGraph.isReal rfl⟩

theorem Qam.trivialGraph_edges [Nontrivial p] : (@Qam.trivialGraphRealQam p _ _ φ hφ _).edges = 1 :=
  by
  have := RealQam.edges_eq (@Qam.trivialGraphRealQam p _ _ φ _ _)
  haveI ig := hφ.elim.matrix_is_pos_def.invertible
  simp_rw [Qam.trivialGraph_eq, LinearMap.smul_apply, LinearMap.one_apply, trace_smul, smul_eq_mul,
    inv_mul_cancel hφ.elim.matrix_is_pos_def.inv.trace_ne_zero] at this
  norm_cast at this
  simp_rw [Qam.trivialGraph_eq, this]

theorem RealQam.edges_eq_zero_iff {A : l(ℍ)} (hA : RealQam hφ.elim A) : hA.edges = 0 ↔ A = 0 :=
  by
  have : ∀ α β : ℕ, α = β ↔ (α : ℂ) = (β : ℂ) :=
    by
    intro α β
    simp only [Nat.cast_inj, iff_self_iff]
  refine'
    ⟨fun h => _, fun h => by
      rw [this, RealQam.edges_eq, h, LinearMap.zero_apply, trace_zero] <;> norm_cast⟩
  rw [RealQam.edges] at h
  have h' := h
  simp only [Submodule.finrank_eq_zero] at h
  rw [Qam.IdempotentAndReal.eq hA.1 hA.2]
  let u := Qam.onbOfIdempotentAndReal hA.1 hA.2
  apply Finset.sum_eq_zero
  intro i hi
  rw [finrank_zero_iff_forall_zero.mp h' (u i)]
  norm_cast
  simp_rw [Matrix.zero_mul, LinearMap.mulLeft_zero_eq_zero, MulZeroClass.zero_mul]

theorem orthogonal_projection_of_top {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace ↥(⊤ : Submodule 𝕜 E)] :
    orthogonalProjection' (⊤ : Submodule 𝕜 E) = 1 :=
  by
  ext1
  simp_rw [ContinuousLinearMap.one_apply, orthogonalProjection'_apply]
  rw [orthogonalProjection_eq_self_iff]
  simp only [Submodule.mem_top]

theorem psi_apply_complete_graph {t s : ℝ} : hφ.elim.psi t s |(1 : ℍ)⟩⟨(1 : ℍ)| = 1 :=
  by
  simp only [Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, _root_.map_one, conj_transpose_one]
  rfl

theorem RealQam.edges_eq_dim_iff {A : l(ℍ)} (hA : RealQam hφ.elim A) :
    hA.edges = FiniteDimensional.finrank ℂ (⊤ : Submodule ℂ ℍ) ↔ A = |(1 : ℍ)⟩⟨(1 : ℍ)| :=
  by
  refine'
    ⟨fun h => _, fun h => by
      rw [← @Qam.completeGraph_edges p _ _ φ]
      simp only [h] at hA
      simp only [h, hA]
      rfl⟩
  rw [RealQam.edges] at h
  simp only [finrank_top] at h
  let U := Qam.submoduleOfIdempotentAndReal hA.1 hA.2
  have hU : U = (⊤ : Submodule ℂ ℍ) := Submodule.eq_top_of_finrank_eq h
  rw [← Function.Injective.eq_iff (hφ.elim.Psi 0 (1 / 2)).Injective]
  have t1 := Qam.orthogonalProjection'_eq hA.1 hA.2
  have : (orthogonalProjection' U : l(ℍ)) = 1 :=
    by
    rw [hU, orthogonal_projection_of_top]
    rfl
  rw [this] at t1
  apply_fun (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ) using
    StarAlgEquiv.injective _
  simp_rw [psi_apply_complete_graph, _root_.map_one, oneMapTranspose_eq]
  rw [← Function.Injective.eq_iff hφ.elim.to_matrix.symm.injective, ← t1, _root_.map_one]

private theorem orthogonal_projection_of_dim_one {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {U : Submodule 𝕜 E}
    (hU : FiniteDimensional.finrank 𝕜 U = 1) :
    ∃ v : { x : E // (x : E) ≠ 0 },
      orthogonalProjection' U = (1 / (‖(v : E)‖ ^ 2 : 𝕜)) • rankOne (v : E) (v : E) :=
  by
  let u : OrthonormalBasis (Fin 1) 𝕜 U := by
    rw [← hU]
    exact stdOrthonormalBasis 𝕜 U
  rw [OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne u, Fin.sum_univ_one]
  have hcc : (u 0 : E) ≠ 0 := by
    have := Basis.ne_zero u.to_basis 0
    simp_rw [OrthonormalBasis.coe_toBasis] at this
    simp only [Ne.def, Submodule.coe_eq_zero]
    exact this
  have : ‖(u 0 : E)‖ = 1 := by
    rw [@norm_eq_sqrt_inner 𝕜, Real.sqrt_eq_one]
    simp_rw [← Submodule.coe_inner, orthonormal_iff_ite.mp u.orthonormal, eq_self_iff_true, if_true,
      IsROrC.one_re]
  refine' ⟨⟨u 0, hcc⟩, _⟩
  simp only [Subtype.coe_mk, this, IsROrC.ofReal_one, one_div_one, one_smul, one_pow]

theorem RealQam.edges_eq_one_iff {A : l(ℍ)} (hA : RealQam hφ.elim A) :
    hA.edges = 1 ↔
      ∃ x : { x : ℍ // x ≠ 0 },
        A =
          (1 / (‖(x : ℍ)‖ ^ 2 : ℂ)) •
            (LinearMap.mulLeft ℂ ((x : ℍ) ⬝ φ.Matrix) *
              (LinearMap.mulRight ℂ (φ.Matrix ⬝ (x : ℍ))).adjoint) :=
  by
  constructor
  · intro h
    rw [RealQam.edges] at h
    obtain ⟨u, hu⟩ := orthogonal_projection_of_dim_one h
    have hu' : (u : ℍ) ≠ 0 := by
      simp only [Ne.def, Submodule.coe_eq_zero]
      exact set.mem_set_of.mp (Subtype.mem u)
    use⟨u, hu'⟩
    have t1 := Qam.orthogonalProjection'_eq hA.1 hA.2
    simp_rw [← rankOne_toMatrix_transpose_psi_symm, ← SMulHomClass.map_smul, Subtype.coe_mk, ←
      rankOneLm_eq_rankOne, ← smul_rankOneLm, rankOneLm_eq_rankOne, rankOne.apply_smul, ← hu,
      LinearEquiv.eq_symm_apply, ← oneMapTranspose_symm_eq, StarAlgEquiv.eq_apply_iff_symm_eq,
      StarAlgEquiv.symm_symm, AlgEquiv.eq_apply_iff_symm_eq]
    exact t1.symm
  · rintro ⟨x, rfl⟩
    letI := hφ.elim.matrix_is_pos_def.invertible
    have ugh : ((x : ℍ) ⬝ φ.matrix ⬝ (x : ℍ)ᴴ).trace = ‖(x : ℍ)‖ ^ 2 := by
      rw [← trace_mul_cycle, ← Module.Dual.IsFaithfulPosMap.inner_eq', inner_self_eq_norm_sq_to_K]
    have := RealQam.edges_eq hA
    simp only [LinearMap.smul_apply, trace_smul, LinearMap.mul_apply,
      LinearMap.Matrix.mulRight_adjoint, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.Eq, sig_apply_matrix_hMul_pos_def',
      mul_eq_mul, inv_mul_cancel_left_of_invertible, ugh, smul_eq_mul, one_div] at this ⊢
    have this' : ((‖(x : ℍ)‖ : ℝ) ^ 2 : ℂ) ≠ (0 : ℂ) :=
      by
      simp_rw [Ne.def, sq_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero']
      exact Subtype.mem x
    -- exact set.mem_set_of.mp (subtype.mem x),
    --},
    rw [inv_mul_cancel this'] at this
    norm_cast at this ⊢
    -- exact this,
    rw [this]

-- },
