/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.QuantumGraph.Nontracial
import Monlib.LinearAlgebra.Ips.MinimalProj
import Monlib.QuantumGraph.Iso

#align_import quantum_graph.to_projections

/-!

# Quantum graphs as projections

This file contains the definition of a quantum graph as a projection, and the proof that the

-/


variable {p : Type _} [Fintype p] [DecidableEq p] {n : p → Type _} [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)]

open scoped TensorProduct BigOperators Kronecker Functional

-- local notation `ℍ` := matrix (n i) (n i) ℂ
@[reducible]
local notation "ℍ" => Matrix p p ℂ
@[reducible]
local notation "ℍ_" i => Matrix (n i) (n i) ℂ

-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
@[reducible]
local notation "l(" x ")" => x →ₗ[ℂ] x
@[reducible]
local notation "L(" x ")" => x →L[ℂ] x
@[reducible]
local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable {φ : Module.Dual ℂ (Matrix p p ℂ)}
  --{φ : Π i, module.dual ℂ (ℍ_ i)}
  --[hφ : ∀ i, fact (φ i).is_faithful_pos_map]

open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" => (TensorProduct.assoc ℂ ℍ ℍ ℍ : (ℍ ⊗[ℂ] ℍ) ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ)

local notation "υ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.assoc ℂ ℍ ℍ ℍ) : ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ) ⊗[ℂ] ℍ)

local notation "ϰ" => ((TensorProduct.comm ℂ ℍ ℂ) : ℍ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] ℍ)

local notation "ϰ⁻¹" => (LinearEquiv.symm (TensorProduct.comm ℂ ℍ ℂ) : ℂ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℂ)

local notation "τ" => (TensorProduct.lid ℂ ℍ : ℂ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ)

local notation "τ⁻¹" => (LinearEquiv.symm (TensorProduct.lid ℂ ℍ) : ℍ →ₗ[ℂ] ℂ ⊗[ℂ] ℍ)

local notation "id" => (1 : ℍ →ₗ[ℂ] ℍ)

noncomputable def blockDiag'KroneckerEquiv {φ : ∀ i, Module.Dual ℂ (ℍ_ i)}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) :
    Matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ ≃ₗ[ℂ]
      { x : Matrix (Σ i, n i) (Σ i, n i) ℂ // x.IsBlockDiagonal } ⊗[ℂ]
        { x : Matrix (Σ i, n i) (Σ i, n i) ℂ // x.IsBlockDiagonal } :=
  ((Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hφ i)).symm.toLinearEquiv.trans
        ((Module.Dual.pi.IsFaithfulPosMap.psi hφ hφ 0 0).trans
          (LinearEquiv.TensorProduct.map (1 : (∀ i, Matrix (n i) (n i) ℂ) ≃ₗ[ℂ] _)
            (Pi.transposeAlgEquiv p n : _ ≃ₐ[ℂ] _ᵐᵒᵖ).symm.toLinearEquiv))).trans
    (LinearEquiv.TensorProduct.map isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv
      isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv)

theorem Matrix.conj_conjTranspose' {R n₁ n₂ : Type _} [InvolutiveStar R] (A : Matrix n₁ n₂ R) :
    (Aᴴᵀ)ᴴ = Aᵀ := by rw [← conj_conjTranspose A]

theorem toMatrix_mulLeft_mulRight_adjoint {φ : ∀ i, Module.Dual ℂ (Matrix (n i) (n i) ℂ)}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) (x y : ∀ i, ℍ_ i) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hφ i))
        (LinearMap.mulLeft ℂ x * (LinearMap.adjoint (LinearMap.mulRight ℂ y) : l(∀ i, ℍ_ i))) =
      blockDiagonal' fun i => x i ⊗ₖ ((hφ i).sig (1 / 2) (y i))ᴴᵀ :=
  by
  have : (1 / 2 : ℝ) + (-1 : ℝ) = -(1 / 2) := by norm_num
  simp_rw [_root_.map_mul, ← lmul_eq_mul, ← rmul_eq_mul, rmul_adjoint, pi_lmul_toMatrix,
    pi_rmul_toMatrix, ← blockDiagonal'_mul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks, Pi.star_apply,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, star_eq_conjTranspose, this, ←
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose]
  rfl

-- @[instance]
-- private def smul_comm_class_aux {ι₂ : Type _} {E₂ : ι₂ → Type _} [∀ i, AddCommMonoid (E₂ i)]
--     [∀ i, Module ℂ (E₂ i)] : ∀ i : ι₂, SMulCommClass ℂ ℂ (E₂ i) := fun i => by infer_instance

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
    rfl
  map_smul' c x := by
    ext a
    simp only [LinearMap.smul_apply, Pi.smul_apply, LinearMap.map_smul, RingHom.id_apply,
      LinearMap.coe_mk]
    rfl

theorem rankOne_psi_transpose_to_lin {n : Type _} [DecidableEq n] [Fintype n]
    {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap] (x y : Matrix n n ℂ) :
    hφ.toMatrix.symm
        (TensorProduct.toKronecker
          ((TensorProduct.map (1 : l(Matrix n n ℂ)) (AlgEquiv.toLinearMap (transposeAlgEquiv n ℂ ℂ).symm))
            ((hφ.psi 0 (1 / 2)) |x⟩⟨y|))) =
      LinearMap.mulLeft ℂ x * (LinearMap.adjoint (LinearMap.mulRight ℂ y) : l(Matrix n n ℂ)) :=
  by
  rw [← Function.Injective.eq_iff hφ.toMatrix.injective]
  simp_rw [_root_.map_mul, LinearMap.matrix.mulRight_adjoint, LinearMap.mulRight_toMatrix,
    LinearMap.mulLeft_toMatrix, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Module.Dual.IsFaithfulPosMap.sig_apply_sig]
  have : (1 / 2 : ℝ) + -1 = -(1 / 2) := by norm_num
  rw [this, ← Module.Dual.IsFaithfulPosMap.sig_conjTranspose, AlgEquiv.apply_symm_apply,
    Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, TensorProduct.map_tmul,
    TensorProduct.toKronecker_apply, Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.one_apply,
    AlgEquiv.toLinearMap_apply, op, LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv,
    transposeAlgEquiv_symm_op_apply]

private theorem matrix.stdBasisMatrix.transpose' {R n p : Type _} [DecidableEq n] [DecidableEq p]
    [Semiring R] {i : n} {j : p} {α : R} :
    (stdBasisMatrix i j α)ᵀ = stdBasisMatrix j i α :=
  by
  ext
  simp_rw [transpose_apply, stdBasisMatrix, and_comm]

-- example :
--   -- { x : matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ // x.is_blockDiagonal }
--   matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ
--     ≃ₐ[ℂ]
--   { x : matrix (Σ i : p × p, n i.1 × n i.2) (Σ i : p × p, n i.1 × n i.2) ℂ // x.is_blockDiagonal }
--   -- {x : (matrix (Σ i, n i) (Σ i, n i) ℂ) ⊗[ℂ] (matrix (Σ i, n i) (Σ i, n i) ℂ) // x.is_blockDiagonal}
--   -- {x : matrix (Σ i, n i) (Σ i, n i) ℂ // x.is_blockDiagonal} :=
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

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 0 in
theorem rankOne_toMatrix_transpose_psi_symm [hφ : φ.IsFaithfulPosMap]
  (x y : ℍ) :
    (hφ.psi 0 (1 / 2)).symm
        ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).toLinearMap)
          (kroneckerToTensorProduct (hφ.toMatrix |x⟩⟨y|))) =
      LinearMap.mulLeft ℂ (x * φ.matrix) * (LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * y)) : l(ℍ)) :=
  by
  rw [kmul_representation (hφ.toMatrix |x⟩⟨y|)]
  simp_rw [map_sum, LinearMap.map_smul, LinearEquiv.map_smul, kroneckerToTensorProduct_apply,
    TensorProduct.map_tmul, LinearMap.one_apply, AlgEquiv.toLinearMap_apply,
    transposeAlgEquiv_apply, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_symm_mk,
    Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, unop, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv_symm, MulOpposite.unop_op, matrix.stdBasisMatrix.transpose',
    stdBasisMatrix_conjTranspose, neg_zero, Module.Dual.IsFaithfulPosMap.sig_zero, star_one,
    LinearMap.matrix.mulRight_adjoint, LinearMap.ext_iff, LinearMap.sum_apply, LinearMap.mul_apply,
    LinearMap.smul_apply, ContinuousLinearMap.coe_coe, rankOne_apply, rankOne_toMatrix,
    conjTranspose_col, ← vecMulVec_eq, vecMulVec_apply, Pi.star_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, reshape_apply]
  have :
    ∀ (i j : p) (a : ℍ),
      ⟪hφ.sig (-(1 / 2)) e_{i,j}, a⟫_ℂ =
        ⟪e_{i,j} * hφ.matrixIsPosDef.rpow (-(1 / 2)),
          hφ.matrixIsPosDef.rpow (1 / 2) * a⟫_ℂ :=
    by
    intro i j a
    simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, neg_neg, ←
      Module.Dual.IsFaithfulPosMap.basis_apply hφ (i, j),
      Module.Dual.IsFaithfulPosMap.inner_left_hMul, Module.Dual.IsFaithfulPosMap.inner_coord',
      (PosDef.rpow.isHermitian _ _).eq]
  intro a
  simp_rw [this, ← hφ.basis_apply (_, _), Module.Dual.IsFaithfulPosMap.inner_coord', ←
    conjTranspose_apply, smul_smul, mul_assoc, ← Finset.sum_smul, ← Finset.mul_sum,
    mul_comm ((y * _)ᴴ _ _), ← mul_apply, ← smul_stdBasisMatrix', conjTranspose_mul,
    (PosDef.rpow.isHermitian _ _).eq, Matrix.mul_assoc, ←
    Matrix.mul_assoc (hφ.matrixIsPosDef.rpow _) (hφ.matrixIsPosDef.rpow _),
    PosDef.rpow_mul_rpow, add_halves, PosDef.rpow_one_eq_self, hφ.matrixIsPosDef.1.eq,
    sig_apply_matrix_hMul_posDef', ← mul_assoc]
  nth_rw 1 [← matrix_eq_sum_std_basis]

-- @[instance]
-- private def hmm {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
--     (U : Submodule ℂ H) : CompleteSpace U :=
--   FiniteDimensional.complete ℂ U

open LinearMap in
private theorem lm_to_clm_comp {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p q : E →ₗ[𝕜] E} :
    toContinuousLinearMap p * toContinuousLinearMap q = toContinuousLinearMap (p * q) :=
  rfl

open LinearMap in
private theorem is_idempotent_elem_to_clm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    IsIdempotentElem p ↔ IsIdempotentElem (toContinuousLinearMap p) := by
  simp_rw [IsIdempotentElem, lm_to_clm_comp, Function.Injective.eq_iff (LinearEquiv.injective _)]

open scoped FiniteDimensional
open LinearMap in
private theorem is_self_adjoint_to_clm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    IsSelfAdjoint p ↔ IsSelfAdjoint (toContinuousLinearMap p) := by
  simp_rw [_root_.IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ←
    LinearMap.adjoint_toContinuousLinearMap, Function.Injective.eq_iff (LinearEquiv.injective _),
    LinearMap.star_eq_adjoint]

open LinearMap in
set_option synthInstance.maxHeartbeats 300000 in
theorem orthogonal_projection_iff_lm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    (∃ U : Submodule 𝕜 E, (orthogonalProjection' U : E →ₗ[𝕜] E) = p) ↔
      IsSelfAdjoint p ∧ IsIdempotentElem p :=
  by
  have := @orthogonal_projection_iff 𝕜 E _ _ _ _ (toContinuousLinearMap p)
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
    Aᴴᵀ = (Aᵀ)ᴴ :=
  rfl

theorem Matrix.conj_eq_conjTranspose_transpose {R n₁ n₂ : Type _} [Star R] (A : Matrix n₁ n₂ R) :
    Aᴴᵀ = (Aᴴ)ᵀ :=
  rfl

set_option synthInstance.maxHeartbeats 50000 in
noncomputable def oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ :=
  StarAlgEquiv.ofAlgEquiv
    ((AlgEquiv.TensorProduct.map (1 : ℍ ≃ₐ[ℂ] ℍ) (transposeAlgEquiv p ℂ ℂ).symm).trans
      tensorToKronecker)
    (by
      intro x
      simp only [AlgEquiv.trans_apply]
      exact
      x.induction_on
        (by simp only [star_zero, map_zero])
        (fun x₁ x₂ => by
          let x₂' : ℍ := MulOpposite.unop x₂
          have : x₂ = MulOpposite.op x₂' := rfl
          simp only [TensorProduct.star_tmul, AlgEquiv.TensorProduct.map, AlgEquiv.coe_mk,
            Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
            AlgEquiv.one_apply]
          simp only [AlgHom.coe_coe, AlgEquiv.one_apply, transposeAlgEquiv_symm_apply,
            AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
            AddEquiv.symm_trans_apply, transposeAddEquiv_symm, MulOpposite.opAddEquiv_symm_apply,
            MulOpposite.unop_star, transposeAddEquiv_apply, tensorToKronecker_apply]
          simp_rw [this, TensorProduct.toKronecker_star, TensorProduct.star_tmul]
          rfl)
        (fun a b ha hb => by simp only [map_add, star_add, ha, hb]))

theorem oneMapTranspose_eq (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
    (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _) x =
      TensorProduct.toKronecker
        ((TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap) x) :=
  rfl

theorem oneMapTranspose_symm_eq (x : Matrix (p × p) (p × p) ℂ) :
    (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm x =
      (TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv p ℂ ℂ).toLinearMap)
        (Matrix.kroneckerToTensorProduct x) :=
  rfl

theorem oneMapTranspose_apply (x y : ℍ) :
    (oneMapTranspose : _ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ) (x ⊗ₜ MulOpposite.op y) = x ⊗ₖ yᵀ :=
  by
  rw [oneMapTranspose_eq, TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
    TensorProduct.toKronecker_apply, transposeAlgEquiv_symm_op_apply]
  rfl

theorem toMatrix''_map_star [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    hφ.toMatrix (LinearMap.adjoint (x : l(ℍ))) = star (hφ.toMatrix x) :=
  by
  ext
  simp only [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply, Pi.star_apply,
    star_apply, star_eq_conjTranspose, conjTranspose_apply, LinearMap.star_eq_adjoint,
    LinearMap.adjoint_inner_right, RCLike.star_def, inner_conj_symm,
    Module.Dual.IsFaithfulPosMap.basis_repr_apply]

private theorem ffsugh [hφ : φ.IsFaithfulPosMap] {x : Matrix (p × p) (p × p) ℂ} {y : l(ℍ)} :
    hφ.toMatrix.symm x = y ↔ x = hφ.toMatrix y :=
  Equiv.symm_apply_eq _

theorem toMatrix''_symm_map_star [hφ : φ.IsFaithfulPosMap] (x : Matrix (p × p) (p × p) ℂ) :
    hφ.toMatrix.symm (star x) = LinearMap.adjoint (hφ.toMatrix.symm x) := by
  rw [ffsugh, toMatrix''_map_star, AlgEquiv.apply_symm_apply]

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 0 in
theorem Qam.idempotent_and_real_iff_exists_ortho_proj [hφ : φ.IsFaithfulPosMap] (A : l(ℍ)) :
    Qam.reflIdempotent hφ A A = A ∧ A.IsReal ↔
      ∃ U : Submodule ℂ ℍ,
        (orthogonalProjection' U : l(ℍ)) =
          hφ.toMatrix.symm
            (TensorProduct.toKronecker
              ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
                ((hφ.psi 0 (1 / 2)) A))) :=
  by
  rw [Qam.isReal_and_idempotent_iff_psi_orthogonal_projection, orthogonal_projection_iff_lm, ←
    oneMapTranspose_eq, IsIdempotentElem.algEquiv, IsIdempotentElem.starAlgEquiv, and_comm]
  simp_rw [_root_.IsSelfAdjoint, LinearMap.star_eq_adjoint, ← toMatrix''_symm_map_star, ←
    map_star, Function.Injective.eq_iff (AlgEquiv.injective _),
    Function.Injective.eq_iff (StarAlgEquiv.injective _)]

noncomputable def Qam.submoduleOfIdempotentAndReal [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)}
    (hA1 : Qam.reflIdempotent hφ A A = A) (hA2 : A.IsReal) : Submodule ℂ ℍ :=
  by
  choose U _ using (Qam.idempotent_and_real_iff_exists_ortho_proj A).mp ⟨hA1, hA2⟩
  exact U

theorem Qam.orthogonalProjection'_eq [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)}
  (hA1 : Qam.reflIdempotent hφ A A = A) (hA2 : A.IsReal) :
  (orthogonalProjection' (Qam.submoduleOfIdempotentAndReal hA1 hA2) : l(ℍ)) =
    hφ.toMatrix.symm
      (TensorProduct.toKronecker
        ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
          ((hφ.psi 0 (1 / 2)) A))) :=
Qam.submoduleOfIdempotentAndReal.proof_7 hA1 hA2

noncomputable def Qam.onbOfIdempotentAndReal [hφ : φ.IsFaithfulPosMap]
  {A : l(ℍ)} (hA1 : Qam.reflIdempotent hφ A A = A) (hA2 : A.IsReal) :
  OrthonormalBasis (Fin (FiniteDimensional.finrank ℂ (Qam.submoduleOfIdempotentAndReal hA1 hA2)))
    ℂ (Qam.submoduleOfIdempotentAndReal hA1 hA2) :=
stdOrthonormalBasis ℂ _

set_option synthInstance.maxHeartbeats 80000 in
theorem Qam.IdempotentAndReal.eq [hφ : φ.IsFaithfulPosMap]
  {A : l(ℍ)} (hA1 : Qam.reflIdempotent hφ A A = A)
  (hA2 : A.IsReal) :
  A =
    ∑ i,
      LinearMap.mulLeft ℂ ((Qam.onbOfIdempotentAndReal hA1 hA2 i : ℍ) * φ.matrix) *
        (LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * (Qam.onbOfIdempotentAndReal hA1 hA2 i : ℍ)))) :=
by
  simp_rw [← rankOne_toMatrix_transpose_psi_symm, ← map_sum, ← ContinuousLinearMap.coe_sum, ←
    OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne (Qam.onbOfIdempotentAndReal hA1 hA2),
    Qam.orthogonalProjection'_eq, AlgEquiv.apply_symm_apply]
  simp_rw [← oneMapTranspose_symm_eq, ← oneMapTranspose_eq, StarAlgEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

@[class, reducible]
structure RealQam (hφ : φ.IsFaithfulPosMap) (A : l(ℍ)) : Prop :=
toIdempotent : Qam.reflIdempotent hφ A A = A
toIsReal : A.IsReal

lemma RealQam_iff [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} :
  RealQam hφ A ↔ Qam.reflIdempotent hφ A A = A ∧ A.IsReal :=
⟨λ h => ⟨h.toIdempotent, h.toIsReal⟩, λ h => ⟨h.1, h.2⟩⟩

theorem RealQam.add_iff [hφ : φ.IsFaithfulPosMap] {A B : ℍ →ₗ[ℂ] ℍ} (hA : RealQam hφ A) (hB : RealQam hφ B) :
    RealQam hφ (A + B) ↔ Qam.reflIdempotent hφ A B + Qam.reflIdempotent hφ B A = 0 :=
  by
  simp only [RealQam_iff] at hA hB ⊢
  simp_rw [map_add, LinearMap.add_apply, hA, hB, add_assoc, add_left_cancel_iff, ← add_assoc,
    add_left_eq_self, add_comm, LinearMap.isReal_iff, LinearMap.real_add,
    (LinearMap.isReal_iff _).mp hA.2, (LinearMap.isReal_iff _).mp hB.2,
    and_true_iff]

def RealQam.zero [hφ : φ.IsFaithfulPosMap] : RealQam hφ (0 : l(ℍ)) :=
  by
  simp_rw [RealQam_iff, LinearMap.map_zero, true_and_iff]
  intro
  simp only [LinearMap.zero_apply, star_zero]

@[instance]
noncomputable def RealQam.hasZero [hφ : φ.IsFaithfulPosMap] : Zero { x // RealQam hφ x } where zero := ⟨0, RealQam.zero⟩

theorem Qam.reflIdempotent_zero [hφ : φ.IsFaithfulPosMap] (a : l(ℍ)) : Qam.reflIdempotent hφ a 0 = 0 :=
  map_zero _

theorem Qam.zero_reflIdempotent [hφ : φ.IsFaithfulPosMap] (a : l(ℍ)) : Qam.reflIdempotent hφ 0 a = 0 := by
  simp_rw [LinearMap.map_zero, LinearMap.zero_apply]

@[reducible]
noncomputable def RealQam.edges [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx : RealQam hφ x) : ℕ :=
  FiniteDimensional.finrank ℂ (Qam.submoduleOfIdempotentAndReal hx.1 hx.2)

@[reducible]
noncomputable def RealQam.edges' [hφ : φ.IsFaithfulPosMap] : { x : ℍ →ₗ[ℂ] ℍ // RealQam hφ x } → ℕ := fun x =>
  FiniteDimensional.finrank ℂ
    (Qam.submoduleOfIdempotentAndReal (Set.mem_setOf.mp (Subtype.mem x)).1
      (Set.mem_setOf.mp (Subtype.mem x)).2)

theorem RealQam.edges_eq [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} (hA : RealQam hφ A) :
    (hA.edges : ℂ) = (A φ.matrix⁻¹).trace :=
  by
  obtain ⟨hA1, hA2⟩ := hA
  symm
  nth_rw 1 [Qam.IdempotentAndReal.eq hA1 hA2]
  let U := Qam.submoduleOfIdempotentAndReal hA1 hA2
  simp_rw [LinearMap.sum_apply, LinearMap.matrix.mulRight_adjoint, LinearMap.mul_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, conjTranspose_mul,
    hφ.matrixIsPosDef.1.eq, ← Matrix.mul_assoc, sig_apply_matrix_hMul_posDef']
  have :
    ∀ x : Fin (FiniteDimensional.finrank ℂ ↥U),
      (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) * φ.matrix * φ.matrix⁻¹ * φ.matrix *
            ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace =
        1 :=
    by
    intro x
    calc
      (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) * φ.matrix * φ.matrix⁻¹ * φ.matrix *
              ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace =
          (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) * hφ.matrixIsPosDef.rpow 1 *
                  hφ.matrixIsPosDef.rpow (-1) *
                φ.matrix *
              ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace :=
        by simp_rw [PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self]
      _ =
          (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) *
                  (hφ.matrixIsPosDef.rpow 1 * hφ.matrixIsPosDef.rpow (-1)) *
                φ.matrix *
              ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace :=
        by simp_rw [Matrix.mul_assoc]
      _ =
          (((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ) * φ.matrix *
              ((Qam.onbOfIdempotentAndReal hA1 hA2) x : ℍ)ᴴ).trace :=
        by simp_rw [PosDef.rpow_mul_rpow, add_neg_self, PosDef.rpow_zero, Matrix.mul_one]
      _ = ⟪(Qam.onbOfIdempotentAndReal hA1 hA2 x : ℍ), (Qam.onbOfIdempotentAndReal hA1 hA2 x : ℍ)⟫_ℂ :=
        by
          rw [Module.Dual.IsFaithfulPosMap.inner_eq' hφ]
          rw [← trace_mul_cycle]
      _ = ⟪Qam.onbOfIdempotentAndReal hA1 hA2 x, Qam.onbOfIdempotentAndReal hA1 hA2 x⟫_ℂ := rfl
      _ = 1 := ?_
    · rw [← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_self,
        EuclideanSpace.single_apply]
      simp_rw [if_true]
  simp_rw [trace_sum, ← Matrix.mul_assoc, this, Finset.sum_const, Finset.card_fin,
    Nat.smul_one_eq_coe]

theorem completeGraphRealQam [hφ : φ.IsFaithfulPosMap] : RealQam hφ (Qam.completeGraph ℍ ℍ) :=
⟨Qam.Nontracial.CompleteGraph.qam, Qam.Nontracial.CompleteGraph.isReal⟩

theorem Qam.completeGraph_edges [hφ : φ.IsFaithfulPosMap] :
  (@completeGraphRealQam p _ _ φ hφ).edges = FiniteDimensional.finrank ℂ (⊤ : Submodule ℂ ℍ) :=
by
  have this : (RealQam.edges completeGraphRealQam : ℂ) = (Qam.completeGraph ℍ ℍ φ.matrix⁻¹).trace := RealQam.edges_eq _
  haveI ig := hφ.matrixIsPosDef.invertible
  simp_rw [Qam.completeGraph, ContinuousLinearMap.coe_coe, rankOne_apply,
    Module.Dual.IsFaithfulPosMap.inner_eq', conjTranspose_one, Matrix.mul_one,
    mul_inv_of_invertible, trace_smul, smul_eq_mul, trace_one,
    ← Nat.cast_mul, Nat.cast_inj] at this
  simp_rw [Qam.completeGraph, finrank_top, FiniteDimensional.finrank_matrix]
  exact this

theorem Qam.trivialGraphRealQam [hφ : φ.IsFaithfulPosMap] [Nontrivial p] : RealQam hφ (Qam.trivialGraph hφ rfl) :=
⟨Qam.Nontracial.TrivialGraph.qam rfl, Qam.Nontracial.trivialGraph.isReal rfl⟩

theorem Qam.trivialGraph_edges [hφ : φ.IsFaithfulPosMap] [Nontrivial p] : (@Qam.trivialGraphRealQam p _ _ φ hφ _).edges = 1 :=
by
  have := RealQam.edges_eq (@Qam.trivialGraphRealQam p _ _ φ hφ _)
  nth_rw 2 [Qam.trivialGraph_eq] at this
  simp_rw [LinearMap.smul_apply, LinearMap.one_apply, trace_smul, smul_eq_mul,
    inv_mul_cancel hφ.matrixIsPosDef.inv.trace_ne_zero,
    ← @Nat.cast_one ℂ, Nat.cast_inj] at this
  exact this

theorem RealQam.edges_eq_zero_iff [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} (hA : RealQam hφ A) : hA.edges = 0 ↔ A = 0 :=
  by
  have : ∀ α β : ℕ, α = β ↔ (α : ℂ) = (β : ℂ) :=
    by
    intro α β
    simp only [Nat.cast_inj, iff_self_iff]
  refine'
    ⟨fun h => _, fun h => by
      rw [this, RealQam.edges_eq, h, LinearMap.zero_apply, trace_zero]; norm_cast⟩
  rw [RealQam.edges] at h
  have h' := h
  simp only [Submodule.finrank_eq_zero] at h
  rw [Qam.IdempotentAndReal.eq hA.1 hA.2]
  let u := Qam.onbOfIdempotentAndReal hA.1 hA.2
  apply Finset.sum_eq_zero
  intro i _
  rw [finrank_zero_iff_forall_zero.mp h' (u i)]
  norm_cast
  simp_rw [Matrix.zero_mul, LinearMap.mulLeft_zero_eq_zero, MulZeroClass.zero_mul]

theorem psi_apply_complete_graph [hφ : φ.IsFaithfulPosMap] {t s : ℝ} : hφ.psi t s |(1 : ℍ)⟩⟨(1 : ℍ)| = 1 :=
  by
  simp only [Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, _root_.map_one, conjTranspose_one]
  rfl

lemma AlgEquiv.TensorProduct.map_toLinearMap {R S T U V : Type _} [CommSemiring R]
  [Semiring S] [Semiring T] [Semiring U] [Semiring V]
  [Algebra R S] [Algebra R T] [Algebra R U] [Algebra R V]
  (f : S ≃ₐ[R] T) (g : U ≃ₐ[R] V) :
  (AlgEquiv.TensorProduct.map f g).toLinearMap = _root_.TensorProduct.map f.toLinearMap g.toLinearMap :=
rfl

lemma AlgEquiv.toLinearMap_one {R S : Type _} [CommSemiring R] [Semiring S] [Algebra R S] :
  (AlgEquiv.toLinearMap (1 : S ≃ₐ[R] S)) = 1 :=
rfl

theorem RealQam.edges_eq_dim_iff [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} (hA : RealQam hφ A) :
    hA.edges = FiniteDimensional.finrank ℂ (⊤ : Submodule ℂ ℍ) ↔ A = |(1 : ℍ)⟩⟨(1 : ℍ)| :=
  by
  refine'
    ⟨fun h => _, fun h => by
      rw [← @Qam.completeGraph_edges p _ _ φ]
      simp_rw [← @Nat.cast_inj ℂ, RealQam.edges_eq, h]; rfl⟩
  rw [RealQam.edges] at h
  simp only [finrank_top] at h
  let U := Qam.submoduleOfIdempotentAndReal hA.1 hA.2
  have hU : U = (⊤ : Submodule ℂ ℍ) := Submodule.eq_top_of_finrank_eq h
  rw [← Function.Injective.eq_iff (LinearEquiv.injective (hφ.psi 0 (1 / 2))), psi_apply_complete_graph]
  have t1 := Qam.orthogonalProjection'_eq hA.1 hA.2
  have : (orthogonalProjection' U : l(ℍ)) = 1 :=
    by
    rw [hU, orthogonal_projection_of_top]
    rfl
  simp_rw [this] at t1
  have this' := (AlgEquiv.eq_apply_iff_symm_eq _).mpr t1.symm
  simp_rw [_root_.map_one, ← tensorToKronecker_apply, MulEquivClass.map_eq_one_iff] at this'
  have this'' := AlgEquiv.TensorProduct.map_toLinearMap (1 : ℍ ≃ₐ[ℂ] ℍ) (transposeAlgEquiv p ℂ ℂ).symm
  rw [AlgEquiv.toLinearMap_one] at this''
  rw [← this'', AlgEquiv.toLinearMap_apply, MulEquivClass.map_eq_one_iff] at this'
  exact this'

set_option synthInstance.maxHeartbeats 300000 in
private theorem orthogonal_projection_of_dim_one {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
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
    have := Basis.ne_zero u.toBasis 0
    simp_rw [OrthonormalBasis.coe_toBasis] at this
    simp only [ne_eq, Submodule.coe_eq_zero]
    exact this
  have : ‖(u 0 : E)‖ = 1 := by
    rw [@norm_eq_sqrt_inner 𝕜, Real.sqrt_eq_one]
    simp_rw [← Submodule.coe_inner, orthonormal_iff_ite.mp u.orthonormal, if_true,
      RCLike.one_re]
  refine' ⟨⟨u 0, hcc⟩, _⟩
  simp only [Subtype.coe_mk, this, RCLike.ofReal_one, one_div_one, one_smul, one_pow]

lemma Complex.ofReal'_eq_isROrC_ofReal (a : ℝ) :
  Complex.ofReal' a = RCLike.ofReal a :=
rfl

-- set_option pp.explicit true in
theorem RealQam.edges_eq_one_iff [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} (hA : RealQam hφ A) :
    hA.edges = 1 ↔
      ∃ x : { x : ℍ // x ≠ 0 },
        A =
          (1 / (‖(x : ℍ)‖ ^ 2 : ℂ)) •
            (LinearMap.mulLeft ℂ ((x : ℍ) * φ.matrix) *
              LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * (x : ℍ)))) :=
  by
  constructor
  · intro h
    let h' := h
    rw [← @Nat.cast_inj ℂ, RealQam.edges_eq hA] at h'
    rw [RealQam.edges] at h
    let this : (hA.toIdempotent : ((Qam.reflIdempotent hφ) A) A = A) = hA.toIdempotent := rfl
    rw [this] at h
    obtain ⟨u, hu⟩ := orthogonal_projection_of_dim_one h
    let hu' : (u : ℍ) ≠ 0 := by
      exact u.property
      -- simp_rw [Ne.def, Submodule.coe_eq_zero]
    use⟨u, hu'⟩
    let t1 := Qam.orthogonalProjection'_eq hA.toIdempotent hA.toIsReal
    simp_rw [← rankOne_toMatrix_transpose_psi_symm, ← LinearEquiv.map_smul,
      ← LinearMap.map_smul, ← _root_.map_smul,
      ← ContinuousLinearMap.coe_smul,
      Complex.ofReal'_eq_isROrC_ofReal, ← hu]
    simp_rw [LinearEquiv.eq_symm_apply, ← oneMapTranspose_symm_eq, StarAlgEquiv.eq_apply_iff_symm_eq,
      StarAlgEquiv.symm_symm, AlgEquiv.eq_apply_iff_symm_eq, oneMapTranspose_eq]
    rw [← t1]
  · rintro ⟨x, rfl⟩
    letI := hφ.matrixIsPosDef.invertible
    have ugh : ((x : ℍ) * φ.matrix * (x : ℍ)ᴴ).trace = ‖(x : ℍ)‖ ^ 2 := by
      rw [← trace_mul_cycle, ← Module.Dual.IsFaithfulPosMap.inner_eq', inner_self_eq_norm_sq_to_K]; rfl
    have := RealQam.edges_eq hA
    rw [← @Nat.cast_inj ℂ, this]
    simp only [LinearMap.smul_apply, trace_smul, LinearMap.mul_apply,
      LinearMap.matrix.mulRight_adjoint, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      conjTranspose_mul, hφ.matrixIsPosDef.1.eq, sig_apply_matrix_hMul_posDef',
      inv_mul_cancel_left_of_invertible, ugh, smul_eq_mul, one_div] at this ⊢
    have this' : ((‖(x : ℍ)‖ : ℝ) ^ 2 : ℂ) ≠ (0 : ℂ) :=
      by
      simp_rw [ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero']
      exact x.property
    -- exact set.mem_set_of.mp (subtype.mem x),
    --},
    rw [inv_mul_cancel this', Nat.cast_one]

-- },
