/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.QuantumGraph.ToProjections

#align_import quantum_graph.qam_A

/-!

# Single-edged quantum graphs

This file defines the single-edged quantum graph, and proves that it is a `QAM`.

-/


variable {n : Type _} [Fintype n] [DecidableEq n]

open scoped TensorProduct BigOperators Kronecker Functional
-- local notation `ℍ` := matrix (n i) (n i) ℂ
@[reducible]
local notation "ℍ" => Matrix n n ℂ
@[reducible]
local notation "ℍ_" i => Matrix (n i) (n i) ℂ

-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
@[reducible]
local notation "l(" x ")" => x →ₗ[ℂ] x
@[reducible]
local notation "L(" x ")" => x →L[ℂ] x
@[reducible]
local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable {φ : Module.Dual ℂ (Matrix n n ℂ)}
  --{φ : Π i, module.dual ℂ (ℍ_ i)}
  --[hφ : ∀ i, fact (φ i).is_faithful_pos_map]

open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

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

set_option linter.unusedVariables false in
@[nolint unusedArguments]
noncomputable def qamA (hφ : φ.IsFaithfulPosMap)
    (x : { x : ℍ // x ≠ 0 }) :--(hx : x ≠ 0) :
      ℍ →ₗ[ℂ]
      ℍ :=
  (1 / (‖(x : ℍ)‖ ^ 2 : ℂ)) •
    (LinearMap.mulLeft ℂ ((x : ℍ) * φ.matrix) * LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * (x : ℍ))))

theorem qamA_eq [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
    qamA hφ x =
      (1 / (‖(x : ℍ)‖ ^ 2 : ℂ)) •
        (LinearMap.mulLeft ℂ ((x : ℍ) * φ.matrix) *
          LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * (x : ℍ)))) :=
  rfl

theorem qamA.toMatrix [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
    hφ.toMatrix (qamA hφ x) =
      (1 / ‖(x : ℍ)‖ ^ 2 : ℂ) •
        ((x : ℍ) * φ.matrix) ⊗ₖ
          (hφ.matrixIsPosDef.rpow (1 / 2) * (x : ℍ) * hφ.matrixIsPosDef.rpow (1 / 2))ᴴᵀ :=
  by
  simp only [qamA_eq, _root_.map_smul, AlgEquiv.map_mul, LinearMap.mulLeft_toMatrix,
    LinearMap.matrix.mulRight_adjoint, LinearMap.mulRight_toMatrix,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, Matrix.conjTranspose_mul,
    hφ.matrixIsPosDef.1.eq, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one]
  have :
    (hφ.sig (1 / 2 + -1)) ((x : ℍ)ᴴ * φ.matrix) =
      (hφ.matrixIsPosDef.rpow (1 / 2) * (x : ℍ) *
          hφ.matrixIsPosDef.rpow (1 / 2))ᴴ :=
    calc
      (hφ.sig (1 / 2 + -1)) ((x : ℍ)ᴴ * φ.matrix) =
          hφ.matrixIsPosDef.rpow (1 / 2) * (x : ℍ)ᴴ * φ.matrix *
            hφ.matrixIsPosDef.rpow (-(1 / 2)) :=
        by simp only [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc]; norm_num
      _ =
          hφ.matrixIsPosDef.rpow (1 / 2) * (x : ℍ)ᴴ * hφ.matrixIsPosDef.rpow 1 *
            hφ.matrixIsPosDef.rpow (-(1 / 2)) :=
        by simp only [Matrix.PosDef.rpow_one_eq_self]
      _ =
          (hφ.matrixIsPosDef.rpow (1 / 2) * (x : ℍ) *
              hφ.matrixIsPosDef.rpow (1 / 2))ᴴ :=
        by
          simp only [Matrix.PosDef.rpow_mul_rpow, Matrix.conjTranspose_mul,
            (Matrix.PosDef.rpow.isHermitian _ _).eq, Matrix.mul_assoc]
          norm_num
  rw [Matrix.conj, ← this, ← _root_.map_mul]

@[instance]
private noncomputable def has_smul.units_matrix_ne_zero : SMul ℂˣ { x : Matrix n n ℂ // x ≠ 0 }
    where smul α x :=
    (⟨((α : ℂ) • (x : Matrix n n ℂ) : Matrix n n ℂ),
        smul_ne_zero (Units.ne_zero α) (Set.mem_setOf.mp (Subtype.mem x))⟩ :
      { x : Matrix n n ℂ // x ≠ 0 })

private theorem has_smul.units_matrix_ne_zero_coe (x : { x : Matrix n n ℂ // x ≠ 0 }) (α : ℂˣ) :
    ((α • x : { x : Matrix n n ℂ // x ≠ 0 }) : Matrix n n ℂ) = (α : ℂ) • x :=
  rfl

open Matrix

set_option synthInstance.maxHeartbeats 60000 in
/-- given a non-zero matrix $x$, we always get $A(x)$ is non-zero -/
theorem qamA.ne_zero [hφ : φ.IsFaithfulPosMap] (x : { x : Matrix n n ℂ // x ≠ 0 }) : qamA hφ x ≠ 0 :=
  by
  have hx := x.property
  simp_rw [ne_eq, qamA, smul_eq_zero, div_eq_zero_iff, one_ne_zero, false_or_iff, sq_eq_zero_iff,
    Complex.ofReal_eq_zero, norm_eq_zero', hx, false_or_iff, ← rankOne_toMatrix_transpose_psi_symm,
    ← oneMapTranspose_symm_eq, LinearEquiv.map_eq_zero_iff, StarAlgEquiv.map_eq_zero_iff,
    AlgEquiv.map_eq_zero_iff, ContinuousLinearMap.coe_eq_zero, rankOne.eq_zero_iff, or_self_iff, hx,
    not_false_iff]

/-- Given any non-zero matrix $x$ and non-zero $\alpha\in\mathbb{C}$ we have
  $$A(\alpha x)=A(x),$$
  in other words, it is not injective. However, it `is_almost_injective` (see `qam_A.is_almost_injective`). -/
theorem qamA.smul [hφ : φ.IsFaithfulPosMap] (x : { x : Matrix n n ℂ // x ≠ 0 }) (α : ℂˣ) :
    qamA hφ (α • x) = qamA hφ x :=
  by
  simp_rw [qamA, has_smul.units_matrix_ne_zero_coe, norm_smul, smul_mul, Matrix.mul_smul,
    LinearMap.mulRight_smul, LinearMap.adjoint_smul, LinearMap.mulLeft_smul, smul_mul_smul,
    smul_smul, Complex.mul_conj, Complex.ofReal_mul, mul_pow, ← one_div_mul_one_div_rev, mul_assoc,
    ← Complex.ofReal_pow, Complex.normSq_eq_abs, ← Complex.norm_eq_abs]
  rw [one_div_mul_cancel, mul_one]
  · simp_rw [ne_eq, Complex.ofReal_eq_zero, sq_eq_zero_iff, norm_eq_zero]
    exact Units.ne_zero _

private theorem kronecker_to_tensor_product_mul' (x y : Matrix (n × n) (n × n) ℂ) :
    kroneckerToTensorProduct (x * y) = kroneckerToTensorProduct x * kroneckerToTensorProduct y :=
  calc
    kroneckerToTensorProduct (x * y) = kroneckerToTensor (x * y) := rfl
    _ = kroneckerToTensor x * kroneckerToTensor y := (map_mul _ _ _)
    _ = kroneckerToTensorProduct x * kroneckerToTensorProduct y := rfl

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 0 in
theorem qamA.is_idempotent [hφ : φ.IsFaithfulPosMap] (x : { x : Matrix n n ℂ // x ≠ 0 }) :
    Qam.reflIdempotent hφ (qamA hφ x) (qamA hφ x) = qamA hφ x :=
  by
  rw [← Function.Injective.eq_iff (hφ.psi 0 (1 / 2)).injective, Psi.reflIdempotent, qamA]
  simp only [← rankOne_toMatrix_transpose_psi_symm]
  simp_rw [_root_.map_smul, LinearEquiv.apply_symm_apply, smul_mul_smul, ←
    oneMapTranspose_symm_eq, ← _root_.map_mul, ← rankOneLm_eq_rankOne, LinearMap.mul_eq_comp,
    rankOneLm_comp_rankOneLm, _root_.map_smul, inner_self_eq_norm_sq_to_K, smul_smul,
    mul_assoc]
  have : (‖(x : ℍ)‖ ^ 2 : ℂ) ≠ 0 :=
  by simp_rw [ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero]; exact x.property
  have this' := one_div_mul_cancel this
  simp_rw [Complex.ofReal'_eq_isROrC_ofReal] at this' ⊢
  simp_rw [this', mul_one]
  -- rw [this', mul_one]

set_option synthInstance.maxHeartbeats 90000 in
theorem Psi.one [hφ : φ.IsFaithfulPosMap] :
    hφ.psi 0 (1 / 2) 1 =
      (TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv n ℂ ℂ).toLinearMap)
        (Matrix.kroneckerToTensorProduct (hφ.toMatrix |φ.matrix⁻¹⟩⟨φ.matrix⁻¹|)) :=
  by
  nth_rw 1 [←
    rankOne.sum_orthonormalBasis_eq_id_lm
      (@Module.Dual.IsFaithfulPosMap.orthonormalBasis n _ _ φ _)]
  apply_fun (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _) using StarAlgEquiv.injective _
  ext
  simp_rw [← oneMapTranspose_symm_eq, StarAlgEquiv.apply_symm_apply, map_sum,
    Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, op, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv, oneMapTranspose_apply, rankOne_toMatrix, conjTranspose_col, ←
    vecMulVec_eq, vecMulVec_apply, Matrix.sum_apply, kroneckerMap, of_apply,
    Module.Dual.IsFaithfulPosMap.sig_zero, Pi.star_apply, transpose_apply, conjTranspose_apply,
    reshape_apply, Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply,
    sig_apply_matrix_hMul_posDef, ← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef,
    PosDef.rpow_mul_rpow, mul_apply, stdBasisMatrix, boole_mul, mul_boole, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  simp only [star_ite, star_zero, mul_ite, ite_mul, MulZeroClass.zero_mul, MulZeroClass.mul_zero]
  have : ∀ a b c d : n, (a, b) = (c, d) ↔ a = c ∧ b = d := fun _ _ _ _ => Prod.eq_iff_fst_eq_snd_eq
  simp_rw [← ite_and, and_comm, ← this, Prod.mk.eta, Finset.sum_ite_eq', Finset.mem_univ, if_true, ←
    conjTranspose_apply, (PosDef.rpow.isHermitian _ _).eq]
  rw [mul_comm]
  norm_num

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k l) -/
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 70000 in
theorem one_map_transpose_psi_eq [hφ : φ.IsFaithfulPosMap] (A : l(ℍ)) :
    (TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv n ℂ ℂ).symm.toLinearMap)
        (hφ.psi 0 (1 / 2) A) =
      (TensorProduct.map A (1 : l(ℍ)))
        (kroneckerToTensorProduct (hφ.toMatrix |φ.matrix⁻¹⟩⟨φ.matrix⁻¹|)) :=
  by
  have :=
    calc
      ∑ k, ∑ l,
            (|A
                  (e_{k,l} *
                    hφ.matrixIsPosDef.rpow
                      (-(1 / 2)))⟩⟨e_{k,l} * hφ.matrixIsPosDef.rpow (-(1 / 2))| :
              l(ℍ)) =
          A ∘ₗ
            ∑ k, ∑ l,
              (|e_{k,l} *
                    hφ.matrixIsPosDef.rpow
                      (-(1 / 2))⟩⟨e_{k,l} * hφ.matrixIsPosDef.rpow (-(1 / 2))| :
                l(ℍ)) :=
        by simp_rw [← LinearMap.comp_rankOne, ← LinearMap.comp_sum]
      _ = A ∘ₗ 1 := by
        simp_rw [← Finset.sum_product', ← Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply,
          Finset.univ_product_univ, rankOne.sum_orthonormalBasis_eq_id_lm]
      _ = A := by rw [LinearMap.comp_one]
  nth_rw 1 [← this]
  simp_rw [map_sum, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply]
  have :
    ∀ x x_1,
      (hφ.sig 0) (A (stdBasisMatrix x x_1 1 * hφ.matrixIsPosDef.rpow (-(1 / 2)))) =
        A
          ((hφ.sig 0)
            (stdBasisMatrix x x_1 1 * hφ.matrixIsPosDef.rpow (-(1 / 2)))) :=
    by
    intro x x_1
    simp_rw [hφ.sig_zero]
  simp_rw [this, TensorProduct.map_tmul, LinearMap.one_apply, ← TensorProduct.map_tmul A, ←
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, ← map_sum, ← Finset.sum_product', ←
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, Finset.univ_product_univ,
    rankOne.sum_orthonormalBasis_eq_id_lm]
  have := @Psi.one n _ _ φ hφ
  rw [Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk] at this
  simp_rw [this, ← oneMapTranspose_symm_eq]
  have :
    ∀ x,
      (TensorProduct.map A (transposeAlgEquiv n ℂ ℂ).symm.toLinearMap)
          (StarAlgEquiv.symm (oneMapTranspose : (ℍ ⊗[ℂ] ℍᵐᵒᵖ) ≃⋆ₐ[ℂ] _) x) =
        (TensorProduct.map A (1 : l(ℍ))) (kroneckerToTensorProduct x) :=
    by
    intro x
    rw [kmul_representation x]
    simp_rw [map_sum, _root_.map_smul, oneMapTranspose_symm_eq,
      kroneckerToTensorProduct_apply, TensorProduct.map_tmul, LinearMap.one_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]
  simp_rw [this]

theorem qamA.isReal [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) : (qamA hφ x).IsReal := by
  simp_rw [LinearMap.isReal_iff, qamA, LinearMap.real_smul, LinearMap.mul_eq_comp,
    LinearMap.real_comp, LinearMap.matrix.mulRight_adjoint, LinearMap.mulRight_real,
    LinearMap.mulLeft_real, ← LinearMap.mul_eq_comp, ← (LinearMap.commute_mulLeft_right _ _).eq,
    conjTranspose_mul, hφ.matrixIsPosDef.1.eq, sig_apply_matrix_hMul_posDef',
    star_eq_conjTranspose, conjTranspose_mul, hφ.matrixIsPosDef.1.eq,
    conjTranspose_conjTranspose, starRingEnd_apply, star_div', star_one, Complex.star_def, ←
    Complex.ofReal_pow, Complex.conj_ofReal]

private theorem qam_A_is_sa_iff_aux [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    (|φ.matrix * x⟩⟨φ.matrix * x| : l(ℍ)) =
      LinearMap.mulLeft ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.mulLeft ℂ φ.matrix :=
  by
  calc
    (|φ.matrix * x⟩⟨φ.matrix * x| : l(ℍ)) =
        LinearMap.mulLeft ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.adjoint (LinearMap.mulLeft ℂ φ.matrix) :=
      by
      simp only [LinearMap.comp_rankOne, LinearMap.rankOne_comp', LinearMap.mulLeft_apply]
    _ = LinearMap.mulLeft ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.mulLeft ℂ φ.matrix := by
      simp_rw [LinearMap.matrix.mulLeft_adjoint, hφ.matrixIsPosDef.1.eq]

private theorem qam_A_is_sa_iff_aux2 [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    (|x * φ.matrix⟩⟨φ.matrix * x| : l(ℍ)) =
      LinearMap.mulRight ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.mulLeft ℂ φ.matrix :=
  by
  calc
    (|x * φ.matrix⟩⟨φ.matrix * x| : l(ℍ)) =
        LinearMap.mulRight ℂ φ.matrix ∘ₗ
          (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.adjoint (LinearMap.mulLeft ℂ φ.matrix) :=
      by
      simp only [LinearMap.comp_rankOne, LinearMap.rankOne_comp', LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply]
    _ = LinearMap.mulRight ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.mulLeft ℂ φ.matrix := by
      simp_rw [LinearMap.matrix.mulLeft_adjoint, hφ.matrixIsPosDef.1.eq]

private theorem qam_A_is_sa_iff_aux3 [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 })
    (h : ⟪(x : ℍ)ᴴ, (x : ℍ)ᴴ⟫_ℂ • (φ.matrix * (x : ℍ)ᴴ) = ⟪↑x, (x : ℍ)ᴴ⟫_ℂ • ((x : ℍ) * φ.matrix)) :
    ⟪↑x, (x : ℍ)ᴴ⟫_ℂ / ⟪(x : ℍ)ᴴ, (x : ℍ)ᴴ⟫_ℂ ≠ 0 :=
  by
  simp_rw [ne_eq, div_eq_zero_iff, inner_self_eq_zero, ← star_eq_conjTranspose, star_eq_zero,
    x.property, or_false_iff, star_eq_conjTranspose]
  intro h'
  simp_rw [h', zero_smul, smul_eq_zero, inner_self_eq_zero, ← star_eq_conjTranspose, star_eq_zero,
    x.property, false_or_iff] at h
  letI := hφ.matrixIsPosDef.invertible
  have : LinearMap.mulLeft ℂ φ.matrix (star (x : ℍ)) = LinearMap.mulLeft ℂ φ.matrix 0 := by
    simp_rw [LinearMap.mulLeft_apply, h, MulZeroClass.mul_zero]
  simp_rw [LinearMap.mulLeft_inj φ.matrix, star_eq_zero, x.property] at this

private theorem qam_A_is_sa_iff_aux4 [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 })
    (h : ⟪(x : ℍ)ᴴ, (x : ℍ)ᴴ⟫_ℂ • (φ.matrix * (x : ℍ)ᴴ) = ⟪↑x, (x : ℍ)ᴴ⟫_ℂ • ((x : ℍ) * φ.matrix)) :
    (⟪↑x, (x : ℍ)ᴴ⟫_ℂ / ⟪(x : ℍ)ᴴ, (x : ℍ)ᴴ⟫_ℂ) • hφ.sig 1 (x : ℍ) = (x : ℍ)ᴴ :=
  by
  letI := hφ.matrixIsPosDef.invertible
  calc
    (⟪↑x, (x : ℍ)ᴴ⟫_ℂ / ⟪(x : ℍ)ᴴ, (↑x)ᴴ⟫_ℂ) • hφ.sig 1 (x : ℍ) =
        (⟪↑x, (x : ℍ)ᴴ⟫_ℂ / ⟪(↑x)ᴴ, (x : ℍ)ᴴ⟫_ℂ) • φ.matrix⁻¹ * (x : ℍ) * φ.matrix :=
      by simp_rw [hφ.sig_apply, PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self,
        smul_mul_assoc]
    _ = ((1 / ⟪(↑x)ᴴ, (x : ℍ)ᴴ⟫_ℂ) • φ.matrix⁻¹) * (⟪↑x, (x : ℍ)ᴴ⟫_ℂ • ↑x * φ.matrix) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc,
        mul_comm (1 / _ : ℂ), mul_one_div]
    _ = ((1 / ⟪(x : ℍ)ᴴ, (↑x)ᴴ⟫_ℂ) • φ.matrix⁻¹) * (⟪(↑x)ᴴ, (x : ℍ)ᴴ⟫_ℂ • φ.matrix * (↑x)ᴴ) := by
      simp_rw [smul_mul_assoc, ← h]
    _ = (⟪(↑x)ᴴ, (x : ℍ)ᴴ⟫_ℂ / ⟪(x : ℍ)ᴴ, (↑x)ᴴ⟫_ℂ) • φ.matrix⁻¹ * φ.matrix * (↑x)ᴴ := by
      simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_assoc, mul_comm (1 / _ : ℂ), mul_one_div]
    _ = (x : ℍ)ᴴ :=
      by
      rw [div_self, one_smul, Matrix.mul_assoc, inv_mul_cancel_left_of_invertible]
      simp_rw [ne_eq, inner_self_eq_zero, ← star_eq_conjTranspose, star_eq_zero]
      exact Subtype.mem x

theorem sig_eq_lmul_rmul [hφ : φ.IsFaithfulPosMap] (t : ℝ) :
    (hφ.sig t).toLinearMap =
      LinearMap.mulLeft ℂ (hφ.matrixIsPosDef.rpow (-t)) ∘ₗ
        LinearMap.mulRight ℂ (hφ.matrixIsPosDef.rpow t) :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [AlgEquiv.toLinearMap_apply, hφ.sig_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← mul_assoc]

private theorem qam_A_is_sa_iff_aux5 [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 })
    (h :
      (LinearMap.mulLeft ℂ φ.matrix).comp (|(x : ℍ)ᴴ⟩⟨(x : ℍ)ᴴ| : l(ℍ)) =
        (LinearMap.mulRight ℂ φ.matrix).comp (|(x : ℍ)⟩⟨(x : ℍ)| : l(ℍ))) :
    LinearEquiv.symmMap ℂ ℍ ℍ |(x : ℍ)⟩⟨(x : ℍ)| = |(x : ℍ)⟩⟨(x : ℍ)| :=
  by
  haveI := hφ.matrixIsPosDef.invertible
  calc
    LinearEquiv.symmMap ℂ ℍ ℍ |(x : ℍ)⟩⟨(x : ℍ)| =
        (hφ.sig (-1)).toLinearMap ∘ₗ (|(x : ℍ)ᴴ⟩⟨(x : ℍ)ᴴ| : l(ℍ)) :=
      ?_
    _ =
        LinearMap.mulLeft ℂ φ.matrix ∘ₗ
          LinearMap.mulRight ℂ φ.matrix⁻¹ ∘ₗ (|(x : ℍ)ᴴ⟩⟨(x : ℍ)ᴴ| : l(ℍ)) :=
      ?_
    _ =
        LinearMap.mulRight ℂ (φ.matrix⁻¹ : ℍ) ∘ₗ
          LinearMap.mulRight ℂ φ.matrix ∘ₗ (|(x : ℍ)⟩⟨(x : ℍ)| : l(ℍ)) :=
      ?_
    _ = (|(x : ℍ)⟩⟨(x : ℍ)| : l(ℍ)) := ?_
  · simp_rw [Qam.RankOne.symmetric_eq, LinearMap.comp_rankOne, AlgEquiv.toLinearMap_apply]
  ·
    simp_rw [sig_eq_lmul_rmul, neg_neg, PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self,
      LinearMap.comp_assoc]
  ·
    simp_rw [← LinearMap.mul_eq_comp, ← mul_assoc, (LinearMap.commute_mulLeft_right _ _).eq,
      mul_assoc, LinearMap.mul_eq_comp, h]
  ·
    rw [← LinearMap.comp_assoc, ← LinearMap.mulRight_mul, mul_inv_of_invertible,
      LinearMap.mulRight_one, LinearMap.id_comp]

theorem sig_comp_eq_iff_eq_sig_inv_comp [hφ : φ.IsFaithfulPosMap] (r : ℝ) (a b : l(ℍ)) :
    (hφ.sig r).toLinearMap.comp a = b ↔ a = (hφ.sig (-r)).toLinearMap.comp b :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply]
  constructor <;> intro h x
  · simp_rw [← h, AlgEquiv.toLinearMap_apply, hφ.sig_apply_sig, neg_add_self, hφ.sig_zero]
  · simp_rw [h, AlgEquiv.toLinearMap_apply, hφ.sig_apply_sig, add_neg_self, hφ.sig_zero]

theorem sig_eq_iff_eq_sig_inv [hφ : φ.IsFaithfulPosMap] (r : ℝ) (a b : ℍ) : hφ.sig r a = b ↔ a = hφ.sig (-r) b := by
  constructor <;> rintro rfl <;>
    simp only [hφ.sig_apply_sig, neg_add_self, add_neg_self, hφ.sig_zero]

theorem comp_sig_eq_iff_eq_comp_sig_inv [hφ : φ.IsFaithfulPosMap] (r : ℝ) (a b : l(ℍ)) :
    a.comp (hφ.sig r).toLinearMap = b ↔ a = b.comp (hφ.sig (-r)).toLinearMap :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply]
  constructor <;> intro h x
  ·
    simp only [← h, AlgEquiv.toLinearMap_apply, hφ.sig_apply_sig, add_neg_self,
      hφ.sig_zero]
  · simp only [h, hφ.sig_apply_sig, neg_add_self, hφ.sig_zero, AlgEquiv.toLinearMap_apply]

private theorem qam_A_is_sa_iff_aux_aux6 [hφ : φ.IsFaithfulPosMap] (r : ℝ) (a b : ℍ) :
    ⟪hφ.sig r a, b⟫_ℂ = ⟪hφ.sig (r / 2) a, hφ.sig (r / 2) b⟫_ℂ :=
  by
  simp_rw [← AlgEquiv.toLinearMap_apply]
  symm
  nth_rw 2 [← Module.Dual.IsFaithfulPosMap.sig_adjoint]
  simp_rw [LinearMap.adjoint_inner_right, AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig hφ, add_halves]

private theorem qam_A_is_sa_iff_aux2_aux6 [hφ : φ.IsFaithfulPosMap] (x : ℍ) (α : NNRealˣ)
    (h : hφ.sig 1 x = (((α : NNReal) : ℝ) : ℂ) • x) :
    x * φ.matrix = (((α : NNReal) : ℝ) : ℂ) • φ.matrix * x :=
  by
  have hα : (((α : NNReal) : ℝ) : ℂ) ≠ 0 := by norm_cast; exact Units.ne_zero α
  letI gg : NoZeroSMulDivisors ℂ ℍ := Module.Free.noZeroSMulDivisors ℂ ℍ
  have h' := h
  rw [sig_eq_iff_eq_sig_inv, _root_.map_smul] at h
  symm
  calc
    (((α : NNReal) : ℝ) : ℂ) • φ.matrix * x = φ.matrix * ((((α : NNReal) : ℝ) : ℂ) • x) := by
      simp_rw [Matrix.mul_smul, smul_mul_assoc]
    _ = φ.matrix * hφ.sig 1 x := by rw [← h']
    _ = x * φ.matrix := ?_
  haveI := hφ.matrixIsPosDef.invertible
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply hφ, PosDef.rpow_one_eq_self,
    PosDef.rpow_neg_one_eq_inv_self, Matrix.mul_assoc, mul_inv_cancel_left_of_invertible]

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 0 in
private theorem qam_A_is_sa_iff_aux3_aux6 [hφ : φ.IsFaithfulPosMap] (x : ℍ) (α : NNRealˣ)
    (H : (|xᴴ⟩⟨xᴴ|) = (|hφ.sig 1 x⟩⟨x|))
    (h : hφ.sig 1 x = (((α : NNReal) : ℝ) : ℂ) • x) :
    |(Real.sqrt ((α : NNReal) : ℝ) : ℂ) • x⟩⟨(Real.sqrt ((α : NNReal) : ℝ) : ℂ) • x| = |xᴴ⟩⟨xᴴ| :=
  by
  have : 0 ≤ ((α : NNReal) : ℝ) := NNReal.coe_nonneg _
  rw [Complex.ofReal'_eq_isROrC_ofReal, rankOne.smul_real_apply, rankOne.apply_smul, smul_smul, ←
    RCLike.ofReal_mul, ← Real.sqrt_mul this, Real.sqrt_mul_self this, ← rankOne.apply_smul, ← Complex.ofReal'_eq_isROrC_ofReal,
    ← h, ← H]

private theorem qam_A_is_sa_iff_aux4_aux6 [hφ : φ.IsFaithfulPosMap] (x' : { x : ℍ // x ≠ 0 })
    (this :
      ⟪(x' : ℍ), (x' : ℍ)⟫_ℂ • hφ.sig 1 (x' : ℍ) =
        ⟪hφ.sig 1 (x' : ℍ), (x' : ℍ)⟫_ℂ • (x' : ℍ)) :
    ∃ α : NNRealˣ, hφ.sig 1 (x' : ℍ) = (((α : NNReal) : ℝ) : ℂ) • (x' : ℍ) :=
  by
  let x : ℍ := (x' : ℍ)
  have hx : x ≠ 0 := x'.property
  let α : ℝ := ‖hφ.sig (1 / 2) x‖ ^ 2 / ‖x‖ ^ 2
  have hα' : 0 ≤ α := by
    simp_rw [α]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  let α' : NNReal := ⟨α, hα'⟩
  have hα : α' ≠ 0 :=
    by
    simp_rw [α', ← NNReal.coe_ne_zero, ne_eq, NNReal.coe_mk, α, div_eq_zero_iff, sq_eq_zero_iff,
      norm_eq_zero, sig_eq_iff_eq_sig_inv, map_zero, or_self_iff]
    exact hx
  exists Units.mk0 α' hα
  simp_rw [Units.val_mk0, α', NNReal.coe_mk, α, Complex.ofReal_div]
  symm
  calc
    (((‖(hφ.sig (1 / 2)) x‖ ^ 2 : ℝ) : ℂ) / ((‖x‖ ^ 2 : ℝ) : ℂ)) • x =
        (1 / (‖x‖ ^ 2 : ℂ)) • (‖hφ.sig (1 / 2) x‖ ^ 2 : ℂ) • x :=
      by simp_rw [smul_smul, mul_comm (1 / _ : ℂ), mul_one_div, Complex.ofReal_pow]
    _ = (1 / ⟪x, x⟫_ℂ) • ⟪hφ.sig (1 / 2) x, hφ.sig (1 / 2) x⟫_ℂ • x := by
      simp_rw [inner_self_eq_norm_sq_to_K]; rfl
    _ = (1 / ⟪x, x⟫_ℂ) • ⟪hφ.sig 1 x, x⟫_ℂ • x := by rw [← qam_A_is_sa_iff_aux_aux6]
    _ = (1 / ⟪x, x⟫_ℂ) • ⟪x, x⟫_ℂ • hφ.sig 1 x := by rw [← this]
    _ = hφ.sig 1 x := ?_
  rw [smul_smul, one_div, inv_mul_cancel, one_smul]
  exact inner_self_ne_zero.mpr hx

theorem sig_eq_self_iff_commute [hφ : φ.IsFaithfulPosMap] (x : ℍ) : hφ.sig 1 x = x ↔ Commute φ.matrix x :=
  by
  simp_rw [hφ.sig_apply, Commute, SemiconjBy, PosDef.rpow_one_eq_self,
    PosDef.rpow_neg_one_eq_inv_self]
  haveI := hφ.matrixIsPosDef.invertible
  constructor <;> intro h
  · nth_rw 1 [← h]
    rw [Matrix.mul_assoc, mul_inv_cancel_left_of_invertible]
  · rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, inv_mul_of_invertible, Matrix.one_mul]

private theorem qam_A_is_sa_iff_aux7 (x : { x : ℍ // x ≠ 0 }) (α : NNRealˣ) (β : ℂˣ)
    (hx : (x : ℍ) = (star (β : ℂ) * (Real.sqrt ((α : NNReal) : ℝ) : ℂ)) • (x : ℍ)ᴴ)
    (hx2 : (x : ℍ) = ((β⁻¹ : ℂ) * (((Real.sqrt ((α : NNReal) : ℝ))⁻¹ : ℝ) : ℂ)) • (x : ℍ)ᴴ) :
    ‖(β : ℂ)‖ ^ 2 * ((α : NNReal) : ℝ) = 1 :=
  by
  have : (x : ℍ) - (x : ℍ) = 0 := sub_self _
  nth_rw 1 [hx] at this
  nth_rw 2 [hx2] at this
  simp_rw [← sub_smul, smul_eq_zero, ← star_eq_conjTranspose, star_eq_zero,
    x.property, or_false_iff, sub_eq_zero, Complex.ofReal_inv, ← mul_inv] at this
  have hi : 0 ≤ ((α : NNReal) : ℝ) := NNReal.coe_nonneg _
  rw [← mul_inv_eq_one₀, inv_inv, mul_mul_mul_comm, Complex.star_def, ←
    Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_abs, ← Complex.norm_eq_abs, ←
    Complex.ofReal_mul, ← Real.sqrt_mul hi, Real.sqrt_mul_self hi, ← Complex.ofReal_mul,
    Complex.ofReal_eq_one] at this
  exact this
  simp_rw [ne_eq, inv_eq_zero, mul_eq_zero, Complex.ofReal_eq_zero, Real.sqrt_eq_zero hi,
    NNReal.coe_eq_zero, Units.ne_zero, or_false_iff, not_false_iff]

private theorem qam_A_is_sa_iff_aux8 (α : NNRealˣ) (β : ℂˣ)
    (h : ‖(β : ℂ)‖ ^ 2 * ((α : NNReal) : ℝ) = 1) :
    ∃ γ : ℂˣ,
      (γ : ℂ) ^ 2 = (β : ℂ) * (((α : NNReal) : ℝ).sqrt : ℂ) ∧
        ‖(γ : ℂ)‖ ^ 2 = 1 ∧ star (γ : ℂ) = (γ : ℂ)⁻¹ :=
  by
  let γ : ℂ := ((β : ℂ) * (((α : NNReal) : ℝ).sqrt : ℂ)) ^ ((2 : ℕ) : ℂ)⁻¹
  have hγ : γ ≠ 0 := by
    simp only [ne_eq, γ, Complex.cpow_eq_zero_iff, ne_eq, inv_eq_zero, Units.mul_right_eq_zero,
      Complex.ofReal_eq_zero, Real.sqrt_eq_zero, NNReal.zero_le_coe, NNReal.coe_eq_zero,
      Units.ne_zero, not_false_iff, false_and_iff]
  have : γ ^ 2 = (β : ℂ) * (((α : NNReal) : ℝ).sqrt : ℂ) := by
    simp_rw [γ, Complex.cpow_nat_inv_pow _ two_ne_zero]
  have this1 : ‖γ‖ ^ 2 = 1 := by
    rw [← sq_eq_sq (sq_nonneg ‖γ‖) (zero_le_one' ℝ), ← norm_pow, this, norm_mul, mul_pow,
      Complex.ofReal'_eq_isROrC_ofReal,
      RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (NNReal.coe_nonneg _), h,
      one_pow]
  refine' ⟨Units.mk0 γ hγ, this, this1, _⟩
  rw [Complex.norm_eq_abs, ← Complex.ofReal_inj, ← Complex.normSq_eq_abs, ← Complex.mul_conj,
    Complex.ofReal_one, starRingEnd_apply, mul_comm, mul_eq_one_iff_eq_inv₀ hγ] at this1
  exact this1

private theorem qam_A_is_sa_iff_aux9 (x : ℍ) (α : NNRealˣ) (β γ : ℂˣ)
    (h : (γ : ℂ) ^ 2 = (β : ℂ) * (((α : NNReal) : ℝ).sqrt : ℂ)) (h2 : star (γ : ℂ) = (γ : ℂ)⁻¹)
    (hx : xᴴ = ((β : ℂ) * (Real.sqrt ((α : NNReal) : ℝ) : ℂ)) • x) : x.IsAlmostHermitian :=
  by
  refine' ⟨Units.mk0 (star (γ : ℂ)) (star_ne_zero.mpr (Units.ne_zero _)), (γ : ℂ) • x, _⟩
  simp_rw [IsHermitian, conjTranspose_smul, h2, Units.val_mk0, smul_smul,
    inv_mul_cancel (Units.ne_zero γ), one_smul, true_and_iff]
  rw [eq_comm, eq_inv_smul_iff₀ (Units.ne_zero γ), smul_smul, ← sq, h]
  exact hx.symm

set_option synthInstance.maxHeartbeats 70000 in
private theorem qam_A_is_sa_iff_aux5_aux6 [hφ : φ.IsFaithfulPosMap] (x' : { x : ℍ // x ≠ 0 })
    (this :
      ⟪(x' : ℍ), (x' : ℍ)⟫_ℂ • hφ.sig 1 (x' : ℍ) =
        ⟪hφ.sig 1 (x' : ℍ), (x' : ℍ)⟫_ℂ • (x' : ℍ))
    (h : LinearEquiv.symmMap ℂ ℍ ℍ |(x' : ℍ)⟩⟨(x' : ℍ)| = |(x' : ℍ)⟩⟨(x' : ℍ)|)
    (hh : (x' : ℍ).IsAlmostHermitian) : Commute φ.matrix x' :=
  by
  obtain ⟨α, hα⟩ := qam_A_is_sa_iff_aux4_aux6 x' this
  have : hφ.sig (-1) (x' : ℍ)ᴴ = (((α : NNReal) : ℝ) : ℂ) • (x' : ℍ)ᴴ := by
    rw [← Module.Dual.IsFaithfulPosMap.sig_conjTranspose, hα, conjTranspose_smul, Complex.star_def,
      Complex.conj_ofReal]
  rw [Qam.RankOne.symmetric_eq, this] at h
  obtain ⟨β, y, hβy, hy⟩ := hh
  have this1 : y ≠ 0 := by
    intro H
    rw [H, smul_zero, eq_comm] at hβy
    exact x'.property hβy
  have Hβ : β ≠ 0 := by
    intro hβ
    rw [hβ, zero_smul, eq_comm] at hβy
    exact x'.property hβy
  simp_rw [← hβy, conjTranspose_smul, hy.eq, ← rankOneLm_eq_rankOne, smul_smul, rankOneLm_smul,
    smul_rankOneLm, smul_smul] at h
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, rankOneLm_eq_rankOne,
    ContinuousLinearMap.coe_eq_zero, rankOne.eq_zero_iff, or_self_iff, Complex.star_def,
    starRingEnd_self_apply, ← Complex.normSq_eq_conj_mul_self, mul_rotate', ←
    Complex.normSq_eq_conj_mul_self, mul_comm, ← mul_sub_one, mul_eq_zero, Complex.ofReal_eq_zero,
    Complex.normSq_eq_zero] at h
  simp_rw [this1, Hβ, false_or_iff, or_false_iff, sub_eq_zero] at h
  rw [h, one_smul, sig_eq_self_iff_commute] at hα
  exact hα

private theorem qam_A_is_sa_iff_aux6 [hφ : φ.IsFaithfulPosMap] (x' : { x : ℍ // x ≠ 0 })
    (h : LinearEquiv.symmMap ℂ ℍ ℍ |(x' : ℍ)⟩⟨(x' : ℍ)| = |(x' : ℍ)⟩⟨(x' : ℍ)|) :
    (x' : ℍ).IsAlmostHermitian ∧ Commute φ.matrix x' :=
  by
  let x : ℍ := (x' : ℍ)
  have hx : x ≠ 0 := x'.property
  have h' := h
  rw [← LinearEquiv.eq_symm_apply] at h'
  have H : (|xᴴ⟩⟨xᴴ| : l(ℍ)) = (|hφ.sig 1 x⟩⟨x| : l(ℍ)) :=
    by
    rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.comp_rankOne, ← neg_neg (1 : ℝ), ←
      sig_comp_eq_iff_eq_sig_inv_comp, LinearMap.comp_rankOne]
    rw [Qam.RankOne.symmetric_eq] at h
    exact h
  have H' : (|xᴴ⟩⟨xᴴ| : l(ℍ)) = (|x⟩⟨hφ.sig 1 x| : l(ℍ)) :=
    by
    simp_rw [← AlgEquiv.toLinearMap_apply]
    rw [← Module.Dual.IsFaithfulPosMap.sig_adjoint, ← LinearMap.rankOne_comp, ← neg_neg (1 : ℝ), ←
      comp_sig_eq_iff_eq_comp_sig_inv]
    have :
      (|xᴴ⟩⟨xᴴ| : l(ℍ)) ∘ₗ (hφ.sig (-1)).toLinearMap =
        |xᴴ⟩⟨LinearMap.adjoint (hφ.sig (-1)).toLinearMap xᴴ| :=
      LinearMap.rankOne_comp _ _ _
    rw [this, Module.Dual.IsFaithfulPosMap.sig_adjoint]
    rw [Qam.RankOne.symmetric'_eq] at h'
    exact h'.symm
  have : (|hφ.sig 1 x⟩⟨x| : l(ℍ)) = |x⟩⟨hφ.sig 1 x| := by rw [← H, ← H']
  -- have this' : |hφ.sig 1 x⟩⟨x| = |x⟩⟨hφ.sig 1 x| :=
    -- by rw [ContinuousLinearMap.coe_inj] at this; exact this
  simp_rw [ContinuousLinearMap.coe_inj] at H this
  simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply] at this
  specialize this x
  obtain ⟨α, hα⟩ := qam_A_is_sa_iff_aux4_aux6 x' this
  have hα' := (qam_A_is_sa_iff_aux3_aux6 _ α H hα).symm
  -- have hα'' := qam_A_is_sa_iff_aux2_aux6 _ _ hα
  obtain ⟨β, hβ⟩ := rankOne.ext_iff _ _ hα'
  rw [smul_smul] at hβ
  have hβ' : (x : ℍ) = (star (β : ℂ) * (Real.sqrt ((α : NNReal) : ℝ) : ℂ)) • (x : ℍ)ᴴ :=
    by
    rw [← Function.Injective.eq_iff (conjTransposeAddEquiv n n ℂ).injective]
    simp_rw [conjTransposeAddEquiv_apply, conjTranspose_smul, star_mul', star_star,
      Complex.star_def, Complex.conj_ofReal, conjTranspose_conjTranspose]
    exact hβ
  have hβ'' : (x : ℍ) = ((β⁻¹ : ℂ) * (((Real.sqrt ((α : NNReal) : ℝ))⁻¹ : ℝ) : ℂ)) • (x : ℍ)ᴴ :=
    by
    rw [hβ, smul_smul, mul_mul_mul_comm, inv_mul_cancel (Units.ne_zero β), one_mul, ←
      Complex.ofReal_mul, inv_mul_cancel, Complex.ofReal_one, one_smul]
    simp_rw [Real.sqrt_ne_zero (NNReal.coe_nonneg _), NNReal.coe_ne_zero]
    exact Units.ne_zero _
  have Hβ := qam_A_is_sa_iff_aux7 x' α β hβ' hβ''
  obtain ⟨γ, hγ, _, Hγ'⟩ := qam_A_is_sa_iff_aux8 α β Hβ
  have Hβ' := qam_A_is_sa_iff_aux9 x α β γ hγ Hγ' hβ
  exact ⟨Hβ', qam_A_is_sa_iff_aux5_aux6 x' this h Hβ'⟩

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 0 in
theorem qamA.of_is_self_adjoint [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 })
    (h : LinearMap.adjoint (qamA hφ x) = qamA hφ x) :
    (x : ℍ).IsAlmostHermitian ∧ Commute φ.matrix (x : ℍ) :=
  by
  simp_rw [qamA, LinearMap.adjoint_smul, LinearMap.mul_eq_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, LinearMap.matrix.mulLeft_adjoint, ← LinearMap.mul_eq_comp, ←
    (LinearMap.commute_mulLeft_right _ _).eq, conjTranspose_mul, hφ.matrixIsPosDef.1.eq] at h
  have :
    LinearMap.mulRight ℂ (φ.matrix * (x : ℍ)) =
      LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * (x : ℍ)ᴴ)) :=
    by
    simp_rw [LinearMap.matrix.mulRight_adjoint, conjTranspose_mul, conjTranspose_conjTranspose,
      hφ.matrixIsPosDef.1.eq, sig_apply_matrix_hMul_posDef']
  nth_rw 1 [this] at h
  simp_rw [← rankOne_psi_transpose_to_lin, ← oneMapTranspose_eq, ← _root_.map_smul] at h
  simp only [(AlgEquiv.injective _).eq_iff, (LinearEquiv.injective _).eq_iff,
    (StarAlgEquiv.injective _).eq_iff] at h
  have thisss : 1 / (‖(x : ℍ)‖ : ℂ) ^ 2 ≠ 0 :=
    by
    simp_rw [ne_eq, div_eq_zero_iff, one_ne_zero, false_or_iff, sq_eq_zero_iff,
      Complex.ofReal_eq_zero, norm_eq_zero]
    exact Subtype.mem x
  -- letI gg : NoZeroSMulDivisors ℂ l(ℍ) := LinearMap.noZeroSMulDivisors
  simp_rw [starRingEnd_apply, star_div', star_one, Complex.star_def, ← Complex.ofReal_pow,
    Complex.conj_ofReal, Complex.ofReal_pow] at h
  simp_rw [← ContinuousLinearMap.coe_smul, ContinuousLinearMap.coe_inj] at h
  letI gg : NoZeroSMulDivisors ℂ (ℍ →ₗ[ℂ] ℍ) := by infer_instance
  -- have h'' := smul_right_inj this
  rw [smul_right_inj thisss] at h
  simp_rw [← ContinuousLinearMap.coe_inj] at h
  rw [qam_A_is_sa_iff_aux, qam_A_is_sa_iff_aux2] at h
  haveI := hφ.matrixIsPosDef.invertible
  simp_rw [← LinearMap.comp_assoc, LinearMap.mulLeft_comp_inj] at h
  have h' := qam_A_is_sa_iff_aux5 x h
  exact qam_A_is_sa_iff_aux6 x h'

set_option synthInstance.maxHeartbeats 0 in
theorem qamA.is_self_adjoint_of [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) (hx₁ : IsAlmostHermitian (x : ℍ))
    (hx₂ : Commute φ.matrix x) : LinearMap.adjoint (qamA hφ x) = qamA hφ x :=
  by
  simp_rw [qamA, LinearMap.adjoint_smul, LinearMap.mul_eq_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, LinearMap.matrix.mulLeft_adjoint, ← LinearMap.mul_eq_comp, ←
    (LinearMap.commute_mulLeft_right _ _).eq, conjTranspose_mul, hφ.matrixIsPosDef.1.eq]
  obtain ⟨α, y, ⟨hxy, hy⟩⟩ := hx₁
  have : 1 / (‖(x : ℍ)‖ : ℂ) ^ 2 ≠ 0 :=
    by
    simp_rw [ne_eq, div_eq_zero_iff, one_ne_zero, false_or_iff, sq_eq_zero_iff,
      Complex.ofReal_eq_zero, norm_eq_zero]
    exact Subtype.mem x
  -- letI gg : NoZeroSMulDivisors ℂ l(ℍ) := LinearMap.noZeroSMulDivisors
  simp_rw [starRingEnd_apply, star_div', star_one, Complex.star_def, ← Complex.ofReal_pow,
    Complex.conj_ofReal, Complex.ofReal_pow, smul_right_inj this]
  simp_rw [← hx₂.eq, ← hxy, conjTranspose_smul, mul_smul_comm,
    LinearMap.mulLeft_smul, LinearMap.mulRight_smul, LinearMap.adjoint_smul, smul_mul_smul,
    starRingEnd_apply, mul_comm, LinearMap.matrix.mulRight_adjoint, conjTranspose_mul,
    hφ.matrixIsPosDef.1.eq, hy.eq, sig_apply_matrix_hMul_posDef']

theorem qamA.is_self_adjoint_iff [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
  LinearMap.adjoint (qamA hφ x) = qamA hφ x ↔ IsAlmostHermitian (x : ℍ) ∧ Commute φ.matrix x :=
⟨fun h => qamA.of_is_self_adjoint x h, fun h => qamA.is_self_adjoint_of x h.1 h.2⟩

theorem qamA.isRealQam [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) : RealQam hφ (qamA hφ x) :=
  ⟨qamA.is_idempotent _, qamA.isReal _⟩

open scoped ComplexOrder
theorem Matrix.PosDef.ne_zero [Nontrivial n] {Q : ℍ} (hQ : Q.PosDef) : Q ≠ 0 :=
  by
  have := PosDef.trace_ne_zero hQ
  intro h
  rw [h, trace_zero] at this
  contradiction

theorem qamA.edges [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) : (@qamA.isRealQam n _ _ φ hφ x).edges = 1 :=
  by
  rw [RealQam.edges_eq_one_iff]
  exact ⟨x, rfl⟩

set_option synthInstance.maxHeartbeats 0 in
theorem qamA.is_irreflexive_iff [hφ : φ.IsFaithfulPosMap]  [Nontrivial n] (x : { x : ℍ // x ≠ 0 }) :
    Qam.reflIdempotent hφ (qamA hφ x) 1 = 0 ↔ (x : ℍ).trace = 0 :=
  by
  simp_rw [qamA, ← rankOne_toMatrix_transpose_psi_symm, ←
    Function.Injective.eq_iff (hφ.psi 0 (1 / 2)).injective, Psi.reflIdempotent,
    _root_.map_smul, LinearEquiv.apply_symm_apply, Psi.one, smul_mul_assoc, ←
    oneMapTranspose_symm_eq, ← _root_.map_mul, LinearEquiv.map_zero, smul_eq_zero, StarAlgEquiv.map_eq_zero_iff,
    AlgEquiv.map_eq_zero_iff, ← rankOneLm_eq_rankOne, one_div, inv_eq_zero, sq_eq_zero_iff,
    Complex.ofReal_eq_zero, norm_eq_zero, x.property, false_or_iff,
    LinearMap.mul_eq_comp, rankOneLm_comp_rankOneLm, smul_eq_zero, rankOneLm_eq_rankOne,
    ContinuousLinearMap.coe_eq_zero, rankOne.eq_zero_iff,
    Matrix.PosDef.ne_zero hφ.matrixIsPosDef.inv, or_false_iff,
    x.property, or_false_iff, Module.Dual.IsFaithfulPosMap.inner_eq']
  haveI := hφ.matrixIsPosDef.invertible
  rw [trace_mul_cycle, Matrix.mul_assoc, inv_mul_cancel_left_of_invertible, ← trace_star,
    star_eq_zero]

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 0 in
theorem qamA.is_almost_injective [hφ : φ.IsFaithfulPosMap] (x y : { x : ℍ // x ≠ 0 }) :
    qamA hφ x = qamA hφ y ↔ ∃ α : ℂˣ, (x : ℍ) = (α : ℂ) • (y : ℍ) :=
  by
  simp_rw [qamA, ← rankOne_toMatrix_transpose_psi_symm, ← _root_.map_smul, ←
    oneMapTranspose_symm_eq]
  rw [Function.Injective.eq_iff (hφ.psi _ _).symm.injective,
    Function.Injective.eq_iff (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm.injective,
    Function.Injective.eq_iff hφ.toMatrix.injective]
  have :
    ∀ x : { x : ℍ // x ≠ 0 },
      (1 / (‖(x : ℍ)‖ : ℂ) ^ 2) • (|(x : ℍ)⟩⟨(x : ℍ)| : l(ℍ)) =
        |(1 / (‖(x : ℍ)‖ : ℂ)) • (x : ℍ)⟩⟨(1 / (‖(x : ℍ)‖ : ℂ)) • (x : ℍ)| :=
    by
    intro y
    simp_rw [← rankOneLm_eq_rankOne, rankOneLm_smul, smul_rankOneLm, smul_smul, starRingEnd_apply,
      star_div', star_one, Complex.star_def, Complex.conj_ofReal, ← div_mul_eq_div_mul_one_div, ←
      sq]
  simp_rw [this, ContinuousLinearMap.coe_inj]
  constructor
  · intro h
    obtain ⟨α, hα⟩ := rankOne.ext_iff _ _ h
    let β := (‖(x : ℍ)‖ : ℂ) * (α : ℂ) * (1 / (‖(y : ℍ)‖ : ℂ))
    have : β ≠ 0 := by
      simp_rw [β, one_div]
      apply mul_ne_zero
      apply mul_ne_zero
      on_goal 2 => exact Units.ne_zero _
      on_goal 2 => apply inv_ne_zero
      all_goals
        simp only [Complex.ofReal_ne_zero, norm_ne_zero_iff]
        simp only [ne_eq, x.property, y.property, not_false_iff]
    use Units.mk0 β this
    simp_rw [Units.val_mk0, β, mul_assoc]
    rw [← smul_smul]
    rw [smul_smul] at hα
    rw [← hα, smul_smul, one_div, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      mul_inv_cancel (norm_ne_zero_iff.mpr (x.property)), Complex.ofReal_one,
      one_smul]
  · rintro ⟨α, hα⟩
    simp_rw [← ContinuousLinearMap.coe_inj, ← this, hα, ← rankOneLm_eq_rankOne, rankOneLm_smul,
      smul_rankOneLm, smul_smul, norm_smul, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_abs, ← Complex.norm_eq_abs]
    simp only [Complex.ofReal_mul, one_div, mul_pow, _root_.mul_inv_rev, mul_assoc]
    rw [Complex.ofReal_pow, inv_mul_cancel, mul_one]
    · simp only [ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero]
      exact Units.ne_zero _

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 0 in
theorem qamA.is_reflexive_iff [hφ : φ.IsFaithfulPosMap]  [Nontrivial n] (x : { x : ℍ // x ≠ 0 }) :
    Qam.reflIdempotent hφ (qamA hφ x) 1 = 1 ↔ ∃ α : ℂˣ, (x : ℍ) = (α : ℂ) • φ.matrix⁻¹ :=
  by
  simp_rw [qamA, ← rankOne_toMatrix_transpose_psi_symm, ←
    Function.Injective.eq_iff (hφ.psi 0 (1 / 2)).injective, Psi.reflIdempotent,
    _root_.map_smul, LinearEquiv.apply_symm_apply, Psi.one, smul_mul_assoc, ←
    oneMapTranspose_symm_eq, ← _root_.map_mul, ← _root_.map_smul]
  rw [Function.Injective.eq_iff (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm.injective,
    Function.Injective.eq_iff hφ.toMatrix.injective]
  simp_rw [← rankOneLm_eq_rankOne, LinearMap.mul_eq_comp, rankOneLm_comp_rankOneLm, ←
    smul_rankOneLm, rankOneLm_eq_rankOne, ContinuousLinearMap.coe_inj]
  rw [← sub_eq_zero, ← rankOne.left_sub, rankOne.eq_zero_iff]
  haveI := hφ.matrixIsPosDef.invertible
  simp only [sub_eq_zero, smul_smul, Module.Dual.IsFaithfulPosMap.inner_eq']
  rw [trace_mul_cycle, inv_mul_of_invertible, Matrix.one_mul, ← trace_star]
  simp only [hφ.matrixIsPosDef.inv.ne_zero, or_false_iff]
  constructor
  · intro h
    simp_rw [← h, smul_smul]
    have : (x : ℍ).trace ≠ 0 := by
      intro h'
      rw [h', star_zero, MulZeroClass.mul_zero, zero_smul] at h
      exact hφ.matrixIsPosDef.inv.ne_zero h.symm
    have : 1 / ↑‖(x : ℍ)‖ ^ 2 * star (x : ℍ).trace ≠ 0 :=
      by
      apply mul_ne_zero
      · simp only [one_div, inv_eq_zero, ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero,
          norm_eq_zero]
        exact Subtype.mem x
      · simp only [ne_eq, star_eq_zero]
        exact this
    use Units.mk0 _ (inv_ne_zero this)
    rw [Units.val_mk0, inv_mul_cancel this, one_smul]
  · rintro ⟨α, hx⟩
    simp_rw [hx, trace_smul, star_smul, norm_smul, trace_star, hφ.matrixIsPosDef.inv.1.eq]
    have : (‖φ.matrix⁻¹‖ : ℂ) ^ 2 = φ.matrix⁻¹.trace := by
      simp_rw [Complex.ofReal'_eq_isROrC_ofReal, ← inner_self_eq_norm_sq_to_K, Module.Dual.IsFaithfulPosMap.inner_eq',
        hφ.matrixIsPosDef.inv.1.eq, Matrix.mul_assoc, mul_inv_cancel_left_of_invertible]
    simp only [Complex.ofReal_mul, mul_pow, one_div, _root_.mul_inv_rev, this, smul_smul,
      smul_eq_mul]
    rw [mul_rotate, mul_rotate _ _ (α : ℂ), mul_assoc _ _ (star (α : ℂ)), Complex.star_def,
      Complex.mul_conj, mul_mul_mul_comm, Complex.normSq_eq_abs, ← Complex.norm_eq_abs, ←
      Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      mul_inv_cancel (PosDef.trace_ne_zero hφ.matrixIsPosDef.inv), mul_inv_cancel, one_mul,
      Complex.ofReal_one, one_smul]
    simp only [ne_eq, sq_eq_zero_iff, norm_eq_zero, Units.ne_zero, not_false_iff]

theorem qamA.of_trivialGraph [hφ : φ.IsFaithfulPosMap] [Nontrivial n] :
    qamA hφ ⟨φ.matrix⁻¹, hφ.matrixIsPosDef.inv.ne_zero⟩ = Qam.trivialGraph hφ rfl :=
  by
  rw [qamA]
  haveI := hφ.matrixIsPosDef.invertible
  simp only [LinearMap.mulLeft_smul, LinearMap.mulRight_smul, LinearMap.adjoint_smul,
    Subtype.coe_mk, inv_mul_of_invertible, mul_inv_of_invertible, LinearMap.mulLeft_one,
    LinearMap.mulRight_one, ← LinearMap.one_eq_id, LinearMap.adjoint_one, one_mul]
  have : ((‖φ.matrix⁻¹‖ : ℝ) : ℂ) ^ 2 = φ.matrix⁻¹.trace := by
    simp_rw [Complex.ofReal'_eq_isROrC_ofReal, ← inner_self_eq_norm_sq_to_K, Module.Dual.IsFaithfulPosMap.inner_eq',
      hφ.matrixIsPosDef.inv.1.eq, Matrix.mul_assoc, mul_inv_cancel_left_of_invertible]
  rw [this, one_div, Qam.trivialGraph_eq]

theorem Qam.unique_one_edge_and_refl [hφ : φ.IsFaithfulPosMap] [Nontrivial n] {A : l(ℍ)} (hA : RealQam hφ A) :
    hA.edges = 1 ∧ Qam.reflIdempotent hφ A 1 = 1 ↔ A = Qam.trivialGraph hφ rfl :=
  by
  constructor
  · rintro ⟨h1, h2⟩
    rw [RealQam.edges_eq_one_iff] at h1
    rcases h1 with ⟨x, rfl⟩
    rw [← qamA_eq] at h2
    rw [← qamA_eq, ← qamA.of_trivialGraph, qamA.is_almost_injective]
    exact (qamA.is_reflexive_iff x).mp h2
  · rintro rfl
    exact ⟨Qam.trivialGraph_edges, Qam.Nontracial.trivialGraph rfl⟩

private theorem star_alg_equiv.is_isometry_iff [hφ : φ.IsFaithfulPosMap] [Nontrivial n] (f : ℍ ≃⋆ₐ[ℂ] ℍ) :
    StarAlgEquiv.IsIsometry f ↔ f φ.matrix = φ.matrix := by
  simp_rw [List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f)
      0 4,
    StarAlgEquiv.IsIsometry, isometry_iff_norm_aux]

theorem qamA.isometric_starAlgEquiv_conj [hφ : φ.IsFaithfulPosMap] [Nontrivial n] (x : { x : ℍ // x ≠ 0 }) {f : ℍ ≃⋆ₐ[ℂ] ℍ}
    (hf : StarAlgEquiv.IsIsometry f) :
    f.toAlgEquiv.toLinearMap ∘ₗ qamA hφ x ∘ₗ f.symm.toAlgEquiv.toLinearMap =
      qamA hφ
        ⟨f (x : ℍ),
          (LinearEquiv.map_ne_zero_iff f.toAlgEquiv.toLinearEquiv).mpr
            (x.property)⟩ :=
  by
  apply_fun hφ.toMatrix using (AlgEquiv.injective _)
  have hf' := hf
  rw [star_alg_equiv.is_isometry_iff] at hf
  haveI := hφ.matrixIsPosDef.invertible
  have this2 : f φ.matrix⁻¹ = φ.matrix⁻¹ := by
    symm
    apply inv_eq_left_inv
    nth_rw 2 [← hf]
    rw [← _root_.map_mul, inv_mul_of_invertible, _root_.map_one]
  obtain ⟨U, rfl⟩ := f.of_matrix_is_inner
  have hU : Commute φ.matrix (U⁻¹ : unitaryGroup n ℂ) :=
    by
    rw [← innerAut_adjoint_eq_iff, ← innerAutStarAlg_equiv_toLinearMap, ←
      innerAut_inv_eq_star, ← innerAutStarAlg_equiv_symm_toLinearMap]
    have := List.TFAE.out
        (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _
          (innerAutStarAlg U).symm) 0 1
    rw [eq_comm, ← StarAlgEquiv.symm_apply_eq, this,
      StarAlgEquiv.symm_symm, innerAutStarAlg_equiv_symm_toLinearMap,
      innerAutStarAlg_equiv_toLinearMap] at hf
    rw [innerAutStarAlg_equiv_toLinearMap, innerAutStarAlg_equiv_symm_toLinearMap,
      inv_inv, hf]
  simp only [← LinearMap.mul_eq_comp, AlgEquiv.map_mul, innerAutStarAlg_equiv_toLinearMap,
    innerAutStarAlg_equiv_symm_toLinearMap, InnerAut.toMatrix, qamA.toMatrix,
    Matrix.smul_mul, Matrix.mul_smul, ← mul_kronecker_mul, ← Matrix.conj_mul]
  let σ := hφ.sig
  let rpow := hφ.matrixIsPosDef.rpow
  have :=
    calc
      σ (-(1 / 2)) U *
            (rpow (1 / 2) * (x : ℍ) * rpow (1 / 2) * (σ (-(1 / 2))) (U⁻¹ : unitaryGroup n ℂ)) =
          rpow (1 / 2) * U * (rpow (-(1 / 2)) * rpow (1 / 2)) * (x : ℍ) *
                (rpow (1 / 2) * rpow (1 / 2)) *
              (U⁻¹ : unitaryGroup n ℂ) *
            rpow (-(1 / 2)) :=
        by simp only [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, σ, rpow, neg_neg]
      _ = rpow (1 / 2) * U * (x : ℍ) * (φ.matrix * (U⁻¹ : unitaryGroup n ℂ)) * rpow (-(1 / 2)) :=
        by
        rw [PosDef.rpow_mul_rpow, PosDef.rpow_mul_rpow,
          neg_add_self, PosDef.rpow_zero, Matrix.mul_one,
          add_halves, PosDef.rpow_one_eq_self, Matrix.mul_assoc]
        simp_rw [mul_assoc]
      _ = rpow (1 / 2) * U * (x : ℍ) * (U⁻¹ : unitaryGroup n ℂ) * (rpow 1 * rpow (-(1 / 2))) := by
        simp_rw [hU.eq, rpow, PosDef.rpow_one_eq_self, mul_assoc]
      _ = rpow (1 / 2) * U * (x : ℍ) * (U⁻¹ : unitaryGroup n ℂ) * rpow (1 / 2) :=
        by
        simp only [rpow, PosDef.rpow_mul_rpow]
        have : (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2 := by norm_num
        rw [this]
  simp only [this, Subtype.coe_mk]
  rw [StarAlgEquiv.IsIsometry, isometry_iff_norm_aux] at hf'
  simp_rw [hf', innerAutStarAlg_apply, Matrix.mul_assoc, hU.eq,
    UnitaryGroup.inv_apply]
  rfl

theorem qamA.iso_iff [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    {x y : { x : ℍ // x ≠ 0 }} :-- (hx : _root_.is_self_adjoint (qam_A hφ x))
        -- (hy : _root_.is_self_adjoint (qam_A hφ y))
        -- qam.iso (@qam_A.is_idempotent n _ _ φ hφ x) (qam_A.is_idempotent y)
        @Qam.Iso
        n _ _ φ (qamA hφ x) (qamA hφ y) ↔
      ∃ U : unitaryGroup n ℂ,
        (∃ β : ℂˣ, (x : ℍ) = innerAut U ((β : ℂ) • (y : ℍ))) ∧ Commute φ.matrix U :=
  by
  simp_rw [Qam.iso_iff, ← innerAutStarAlg_equiv_toLinearMap, StarAlgEquiv.comp_eq_iff]
  constructor
  · rintro ⟨U, ⟨hU, hUU⟩⟩
    refine' ⟨U, _, hUU⟩
    rw [unitary_commutes_with_hφ_matrix_iff_isIsometry] at hUU
    rw [LinearMap.comp_assoc, qamA.isometric_starAlgEquiv_conj _ hUU, qamA.is_almost_injective,
      Subtype.coe_mk] at hU
    simp_rw [_root_.map_smul, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv]
    exact hU
  · rintro ⟨U, ⟨hU, hUU⟩⟩
    refine' ⟨U, _, hUU⟩
    rw [unitary_commutes_with_hφ_matrix_iff_isIsometry] at hUU
    rw [LinearMap.comp_assoc, qamA.isometric_starAlgEquiv_conj _ hUU, qamA.is_almost_injective,
      Subtype.coe_mk]
    simp_rw [_root_.map_smul, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv] at hU
    exact hU
