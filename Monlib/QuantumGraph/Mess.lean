/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.QuantumGraph.Nontracial
import Monlib.QuantumGraph.ToProjections
import Monlib.QuantumGraph.QamA
import Monlib.LinearAlgebra.MyBimodule
import Monlib.QuantumGraph.Symm
import Monlib.QuantumGraph.SchurIdempotent

#align_import quantum_graph.mess

/-!
 # Some messy stuff

 This file contains some messy stuff that I don't want to put in the main file.

 Will organise this later.
-/


variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

open scoped TensorProduct BigOperators Kronecker Functional

-- local notation `ℍ` := matrix (n i) (n i) ℂ
@[reducible]
local notation "ℍ" => Matrix p p ℂ
-- @[reducible]
-- local notation "ℍ_" i => Matrix (n i) (n i) ℂ

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

set_option synthInstance.maxHeartbeats 0 in
noncomputable def ιMap (hφ : φ.IsFaithfulPosMap) : l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍ :=
{ toFun := fun x => (id ⊗ₘ x) (LinearMap.adjoint m 1)
  map_add' := fun x y =>
    by
    obtain ⟨α, β, h⟩ := TensorProduct.eq_span (LinearMap.adjoint m (1 : ℍ))
    rw [← h]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.add_apply, TensorProduct.tmul_add,
      Finset.sum_add_distrib]
  map_smul' := fun r x => by
    simp_rw [RingHom.id_apply, TensorProduct.map_smul_right, LinearMap.smul_apply] }

theorem sig_neg_one [hφ : φ.IsFaithfulPosMap] (a : ℍ) : hφ.sig (-1) a = φ.matrix * a * φ.matrix⁻¹ := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg, PosDef.rpow_one_eq_self,
    PosDef.rpow_neg_one_eq_inv_self]

theorem sig_one [hφ : φ.IsFaithfulPosMap] (a : ℍ) : hφ.sig 1 a = φ.matrix⁻¹ * a * φ.matrix := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, PosDef.rpow_one_eq_self,
    PosDef.rpow_neg_one_eq_inv_self]

set_option synthInstance.maxHeartbeats 0 in
theorem ιMap_apply_rankOne [hφ : φ.IsFaithfulPosMap] (a b : ℍ) : ιMap hφ |a⟩⟨b| = hφ.sig (-1) bᴴ ⊗ₜ[ℂ] a :=
  by
  simp_rw [ιMap, LinearMap.coe_mk, LinearMap.mul'_adjoint, one_apply, boole_mul, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, _root_.map_smul,
    TensorProduct.map_tmul, LinearMap.one_apply, AddHom.coe_mk, ContinuousLinearMap.coe_coe, rankOne_apply]
  have : ∀ i j, inner b (stdBasisMatrix i j 1) = (φ.matrix * bᴴ) j i :=
    by
    intro i j
    rw [← inner_conj_symm, inner_stdBasisMatrix_left, starRingEnd_apply, ← star_apply,
      star_eq_conjTranspose, conjTranspose_mul, hφ.matrixIsPosDef.1.eq]
  simp_rw [this, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul', smul_smul,
    mul_comm ((φ.matrix)⁻¹ _ _), ← Finset.sum_smul, ← mul_apply, ← sig_neg_one,
    TensorProduct.smul_tmul', ← smul_stdBasisMatrix', ← TensorProduct.sum_tmul]
  rw [← matrix_eq_sum_std_basis]

theorem ιMap_eq_psi [hφ : φ.IsFaithfulPosMap] : ιMap hφ = (id ⊗ₘ unop) ∘ₗ tenSwap ∘ₗ (hφ.psi 0 1).toLinearMap :=
  by
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [ιMap_apply_rankOne, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tenSwap_apply, TensorProduct.map_tmul,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, op_apply, unop_apply, MulOpposite.unop_op,
    Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.one_apply]

theorem ιMap_comp_inv [hφ : φ.IsFaithfulPosMap] :
    (ιMap hφ ∘ₗ (hφ.psi 0 1).symm.toLinearMap ∘ₗ (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ id ⊗ₘ op) =
      1 :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp_rw [ιMap_eq_psi, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, tenSwap_apply_tenSwap, ← LinearMap.comp_apply, ←
    TensorProduct.map_comp, unop_comp_op, LinearMap.one_comp, TensorProduct.map_one]

theorem ι_inv_comp_ιMap [hφ : φ.IsFaithfulPosMap] :
    ((hφ.psi 0 1).symm.toLinearMap ∘ₗ (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ id ⊗ₘ op) ∘ₗ ιMap hφ =
      1 :=
  by
  rw [ιMap_eq_psi]
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Module.Dual.IsFaithfulPosMap.psi,
    LinearEquiv.coe_mk, LinearEquiv.coe_symm_mk, Module.Dual.IsFaithfulPosMap.psiToFun'_apply,
    tenSwap_apply, TensorProduct.map_tmul, tenSwap_apply,
    Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, neg_zero, Module.Dual.IsFaithfulPosMap.sig_zero,
    LinearMap.one_apply, op_unop, MulOpposite.unop_op, MulOpposite.op_unop, unop_op,
    conjTranspose_conjTranspose, Module.Dual.IsFaithfulPosMap.sig_apply_sig, neg_add_self,
    Module.Dual.IsFaithfulPosMap.sig_zero]

noncomputable def ιInvMap (hφ : φ.IsFaithfulPosMap) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] l(ℍ) :=
  ((hφ.psi 0 1).symm : ℍ ⊗[ℂ] ℍᵐᵒᵖ →ₗ[ℂ] l(ℍ)) ∘ₗ (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ id ⊗ₘ op

noncomputable def ιLinearEquiv (hφ : φ.IsFaithfulPosMap) : l(ℍ) ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ :=
  letI := Fact.mk hφ
  LinearEquiv.ofLinear (ιMap hφ) (ιInvMap hφ) ιMap_comp_inv ι_inv_comp_ιMap

set_option linter.unusedVariables false in
@[reducible]
private noncomputable def phi_map_aux (hφ : φ.IsFaithfulPosMap) (x : l(ℍ)) : l(ℍ ⊗[ℂ] ℍ) :=
  (id ⊗ₘ m) ∘ₗ υ ∘ₗ ((id ⊗ₘ x) ⊗ₘ id) ∘ₗ (LinearMap.adjoint m) ⊗ₘ id

private theorem phi_map_aux_add (hφ : φ.IsFaithfulPosMap) (x y : l(ℍ)) :
    phi_map_aux hφ (x + y) = phi_map_aux hφ x + phi_map_aux hφ y := by
  simp_rw [phi_map_aux, TensorProduct.map_add, TensorProduct.add_map, LinearMap.add_comp,
    LinearMap.comp_add]

private theorem phi_map_aux_smul (hφ : φ.IsFaithfulPosMap) (x : ℂ) (y : l(ℍ)) :
    phi_map_aux hφ (x • y) = x • phi_map_aux hφ y :=
  by
  apply TensorProduct.ext'
  intro a b
  rw [phi_map_aux, LinearMap.comp_apply, TensorProduct.map_smul, TensorProduct.smul_map,
    LinearMap.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_apply,
    _root_.map_smul]
  rfl

set_option maxHeartbeats 800000 in
noncomputable def phiMap (hφ : φ.IsFaithfulPosMap) : l(ℍ) →ₗ[ℂ] l(ℍ ⊗[ℂ] ℍ)
    where
  toFun x := (id ⊗ₘ m) ∘ₗ υ ∘ₗ ((id ⊗ₘ x) ⊗ₘ id) ∘ₗ (LinearMap.adjoint m) ⊗ₘ id
  map_add' x y :=
    have := phi_map_aux_add hφ x y
    by simp only [phi_map_aux] at this ⊢; exact this
  map_smul' x y :=
    have := phi_map_aux_smul hφ x y
    by simp only [phi_map_aux] at this ⊢; exact this

theorem Module.Dual.IsFaithfulPosMap.sig_isSymmetric [hφ : φ.IsFaithfulPosMap] {t : ℝ} :
    LinearMap.IsSymmetric (hφ.sig t).toLinearMap :=
  by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, _root_.IsSelfAdjoint]
  exact Module.Dual.IsFaithfulPosMap.sig_adjoint

set_option synthInstance.maxHeartbeats 0 in
theorem ιInvMap_mul_adjoint_eq_rmul [hφ : φ.IsFaithfulPosMap] : ιInvMap hφ ∘ₗ (LinearMap.adjoint m) = rmul :=
  by
  simp_rw [LinearMap.ext_iff, ← Matrix.ext_iff]
  intro x a i j
  simp_rw [LinearMap.comp_apply, LinearMap.mul'_adjoint, map_sum, _root_.map_smul, ιInvMap,
    LinearMap.comp_apply, TensorProduct.map_tmul, tenSwap_apply, Module.Dual.IsFaithfulPosMap.psi,
    LinearEquiv.coe_coe, LinearEquiv.coe_symm_mk, Module.Dual.IsFaithfulPosMap.psiInvFun'_apply,
    unop_apply, op_apply, MulOpposite.unop_op, neg_zero, Module.Dual.IsFaithfulPosMap.sig_zero,
    LinearMap.one_apply, stdBasisMatrix_conjTranspose, star_one, LinearMap.sum_apply,
    LinearMap.smul_apply, Matrix.sum_apply, Matrix.smul_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, Matrix.smul_apply, ← AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.sig_isSymmetric _ a, inner_stdBasisMatrix_left, smul_eq_mul,
    stdBasisMatrix, mul_boole, mul_ite, MulZeroClass.mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← mul_apply, mul_comm (x _ _), ← mul_apply,
    AlgEquiv.toLinearMap_apply, ← Matrix.mul_assoc, ← sig_one, ←
    Module.Dual.IsFaithfulPosMap.sig_symm_eq, AlgEquiv.apply_symm_apply]
  rfl

set_option synthInstance.maxHeartbeats 0 in
theorem psi_inv_0_0_mul_adjoint_eq_lmul [hφ : φ.IsFaithfulPosMap] :
    ((hφ.psi 0 0).symm : ℍ ⊗[ℂ] ℍᵐᵒᵖ →ₗ[ℂ] l(ℍ)) ∘ₗ (id ⊗ₘ op) ∘ₗ LinearMap.adjoint m = lmul :=
  by
  simp_rw [LinearMap.ext_iff, ← Matrix.ext_iff]
  intro x a i j
  simp_rw [LinearMap.comp_apply, LinearMap.mul'_adjoint, map_sum, _root_.map_smul,
    TensorProduct.map_tmul, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_coe,
    LinearEquiv.coe_symm_mk, Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, unop_op, neg_zero,
    Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.one_apply, stdBasisMatrix_conjTranspose,
    star_one, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_apply, Matrix.smul_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, Matrix.smul_apply, inner_stdBasisMatrix_left,
    smul_eq_mul, stdBasisMatrix, mul_boole, mul_ite, MulZeroClass.mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  letI := hφ.matrixIsPosDef.invertible
  simp_rw [mul_comm (x _ _), mul_assoc, ← Finset.mul_sum, ← mul_apply,
    mul_comm (φ.matrix⁻¹ _ _), ←
    mul_apply, Matrix.mul_assoc, mul_inv_of_invertible, Matrix.mul_one]
  rfl

theorem tenSwap_psi_eq_psi_real [hφ : φ.IsFaithfulPosMap] {t s : ℝ} :
    tenSwap ∘ₗ (hφ.psi t s : l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍᵐᵒᵖ) =
      (hφ.psi s t : l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍᵐᵒᵖ).real :=
  by
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [LinearMap.real_apply, LinearMap.star_eq_adjoint, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    rankOneLm_eq_rankOne, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tenSwap_apply, TensorProduct.star_tmul, star,
    op_apply, MulOpposite.unop_op, conjTranspose_conjTranspose]

theorem rankOne_map_rankOne_eq [hφ : φ.IsFaithfulPosMap] (x y z w : ℍ) :
    ((|x⟩⟨y| : l(ℍ)) ⊗ₘ (|z⟩⟨w| : l(ℍ))) = |x ⊗ₜ[ℂ] z⟩⟨y ⊗ₜ[ℂ] w| :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  simp_rw [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, rankOne_apply,
    TensorProduct.inner_tmul, TensorProduct.smul_tmul_smul]

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 0 in
theorem phiMap_eq [hφ : φ.IsFaithfulPosMap] : phiMap hφ = (rmulMapLmul : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] l(ℍ ⊗[ℂ] ℍ)) ∘ₗ ιMap hφ :=
  by
  apply LinearMap.ext_of_rank_one'
  intro x y
  rw [TensorProduct.ext_iff]
  intro a b
  rw [TensorProduct.inner_ext_iff']
  intro c d
  simp_rw [phiMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    TensorProduct.map_tmul]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (LinearMap.adjoint m a)
  rw [← h]
  simp_rw [map_sum, TensorProduct.sum_tmul, map_sum, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    TensorProduct.assoc_tmul, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    LinearMap.one_apply, rankOne_apply, LinearMap.mul'_apply, sum_inner, smul_mul_assoc,
    TensorProduct.tmul_smul, inner_smul_left, inner_conj_symm, TensorProduct.inner_tmul, ←
    mul_assoc, mul_comm (inner (β _) _ : ℂ), ← Finset.sum_mul, ← TensorProduct.inner_tmul, ←
    sum_inner, h, LinearMap.adjoint_inner_left, LinearMap.mul'_apply]
  rw [Module.Dual.IsFaithfulPosMap.inner_left_conj hφ _ _ y, ← TensorProduct.inner_tmul]
  revert c d
  rw [← TensorProduct.inner_ext_iff', ιMap_apply_rankOne, rmulMapLmul_apply]
  simp only [TensorProduct.map_tmul, rmul_apply, lmul_apply, sig_neg_one]

set_option synthInstance.maxHeartbeats 0 in
noncomputable def grad (hφ : φ.IsFaithfulPosMap) : l(ℍ) →+ ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ :=
  { toFun := fun x => ((LinearMap.adjoint x ⊗ₘ id) - id ⊗ₘ x) ∘ₗ LinearMap.adjoint m
    map_add' := fun x y => by
      simp only [map_add, TensorProduct.add_map, TensorProduct.map_add, add_sub_add_comm,
        LinearMap.add_comp]
    map_zero' := by
      simp only [map_zero, TensorProduct.zero_map, TensorProduct.map_zero, sub_zero,
        LinearMap.zero_comp] }

noncomputable def oneTensorMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ :=
  (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹
noncomputable def tensorOneMap :=
  (η ⊗ₘ id) ∘ₗ τ⁻¹

theorem oneTensorMap_apply (x : ℍ) : oneTensorMap x = x ⊗ₜ 1 := by
  simp_rw [oneTensorMap, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.comm_symm_tmul, TensorProduct.map_tmul, LinearMap.one_apply,
    Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, one_smul]

theorem tensorOneMap_apply (x : ℍ) : tensorOneMap x = 1 ⊗ₜ x := by
  simp_rw [tensorOneMap, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.map_tmul, LinearMap.one_apply, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, one_smul]

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
private theorem grad_apply_rank_one [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    grad hφ (|x⟩⟨y|) =
      phiMap hφ (|x⟩⟨y| : l(ℍ)).real ∘ₗ tensorOneMap - phiMap hφ |x⟩⟨y| ∘ₗ oneTensorMap :=
  by
  rw [LinearMap.ext_iff]
  intro a
  rw [TensorProduct.inner_ext_iff']
  intro c d
  simp_rw [LinearMap.sub_apply, inner_sub_left, LinearMap.comp_apply, oneTensorMap_apply,
    tensorOneMap_apply, rankOne_real_apply, grad, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearMap.sub_comp, LinearMap.sub_apply, inner_sub_left, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    LinearMap.comp_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (LinearMap.adjoint m a)
  rw [← h]
  simp_rw [map_sum, sum_inner, TensorProduct.map_tmul, rankOneLm_eq_rankOne, phiMap_eq,
    LinearMap.comp_apply, ιMap_apply_rankOne, rmulMapLmul_apply, TensorProduct.map_tmul,
    TensorProduct.inner_tmul, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
    inner_conj_symm, LinearMap.one_apply, mul_comm (inner (α _) _ : ℂ), mul_assoc, ← Finset.mul_sum,
    ← TensorProduct.inner_tmul, ← sum_inner, h, sum_inner, TensorProduct.inner_tmul,
    mul_comm _ (inner (α _) _ : ℂ), ← mul_assoc, mul_comm _ (inner (α _) _ : ℂ), ← Finset.sum_mul, ←
    TensorProduct.inner_tmul, ← sum_inner, h, TensorProduct.inner_tmul,
    LinearMap.adjoint_inner_left, LinearMap.mul'_apply,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, conjTranspose_conjTranspose, neg_neg,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, neg_add_self, Module.Dual.IsFaithfulPosMap.sig_zero,
    rmul_apply, lmul_apply, one_mul, mul_one, ←
    Module.Dual.IsFaithfulPosMap.inner_right_hMul, sig_neg_one, ←
    Module.Dual.IsFaithfulPosMap.inner_left_conj]

theorem grad_apply [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    grad hφ x = phiMap hφ x.real ∘ₗ tensorOneMap - phiMap hφ x ∘ₗ oneTensorMap :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  rw [map_sum, LinearMap.real_sum]
  simp_rw [map_sum, LinearMap.sum_comp, grad_apply_rank_one]
  let f := fun a => ((phiMap hφ) (|(α a)⟩⟨(β a)|)) ∘ₗ oneTensorMap
  have hf : ∀ a, f a = ((phiMap hφ) (|(α a)⟩⟨(β a)|)) ∘ₗ oneTensorMap := fun a => rfl
  let g := fun a => (phiMap hφ) (LinearMap.real |(α a)⟩⟨(β a)|) ∘ₗ tensorOneMap
  have hg : ∀ a, g a = (phiMap hφ) (LinearMap.real |(α a)⟩⟨(β a)|) ∘ₗ tensorOneMap := fun a => rfl
  simp_rw [← hf, ← hg]
  exact @Finset.sum_sub_distrib _ (ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ)) _ g f (by infer_instance)


theorem oneTensorMap_adjoint [hφ : φ.IsFaithfulPosMap] :
    LinearMap.adjoint (oneTensorMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) = τ ∘ₗ ϰ ∘ₗ id ⊗ₘ (LinearMap.adjoint η) := by
  simp_rw [oneTensorMap, LinearMap.adjoint_comp,
    TensorProduct.lid_symm_adjoint, TensorProduct.comm_symm_adjoint, TensorProduct.map_adjoint,
    LinearMap.adjoint_one, Nontracial.unit_adjoint_eq,
    LinearMap.comp_assoc]

theorem oneTensorMap_adjoint_apply [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    LinearMap.adjoint (oneTensorMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) (x ⊗ₜ[ℂ] y) = φ y • x := by
  simp_rw [oneTensorMap_adjoint, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.lid_tmul, LinearMap.one_apply,
    Nontracial.unit_adjoint_eq]

theorem tensorOneMap_adjoint [hφ : φ.IsFaithfulPosMap] :
    LinearMap.adjoint (tensorOneMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) = τ ∘ₗ (LinearMap.adjoint η) ⊗ₘ id := by
  simp_rw [tensorOneMap, LinearMap.adjoint_comp,
    TensorProduct.lid_symm_adjoint, TensorProduct.map_adjoint, LinearMap.adjoint_one]

theorem tensorOneMap_adjoint_apply [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    LinearMap.adjoint (tensorOneMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) (x ⊗ₜ y) = φ x • y := by
  simp_rw [tensorOneMap_adjoint, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, LinearMap.one_apply, Nontracial.unit_adjoint_eq]

private theorem phi_map_adjoint_rank_one [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    LinearMap.adjoint (phiMap hφ |x⟩⟨y|) = phiMap hφ (|x⟩⟨y| : l(ℍ)).real := by
  simp_rw [phiMap_eq, rankOne_real_apply, LinearMap.comp_apply, ιMap_apply_rankOne,
    rmulMapLmul_apply, TensorProduct.map_adjoint, rmul_eq_mul, lmul_eq_mul,
    LinearMap.matrix.mulLeft_adjoint, ← LinearMap.matrix.mulRight_adjoint]

theorem phiMap_adjoint [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) : LinearMap.adjoint (phiMap hφ x) = phiMap hφ x.real :=
  by
  obtain ⟨α, β, h⟩ := x.exists_sum_rankOne
  rw [h]
  simp_rw [LinearMap.real_sum, map_sum, phi_map_adjoint_rank_one]

private theorem grad_adjoint_rank_one [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    LinearMap.adjoint (grad hφ |x⟩⟨y| : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) =
      τ ∘ₗ (LinearMap.adjoint η ⊗ₘ id) ∘ₗ phiMap hφ |x⟩⟨y| -
        τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ LinearMap.adjoint η) ∘ₗ phiMap hφ (|x⟩⟨y| : l(ℍ)).real :=
  by
  simp_rw [grad_apply_rank_one, map_sub, LinearMap.adjoint_comp, tensorOneMap_adjoint,
    oneTensorMap_adjoint, ← phi_map_adjoint_rank_one, LinearMap.adjoint_adjoint,
    LinearMap.comp_assoc]

theorem grad_adjoint [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    LinearMap.adjoint (grad hφ x) =
      τ ∘ₗ (LinearMap.adjoint η ⊗ₘ id) ∘ₗ phiMap hφ x -
        τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ LinearMap.adjoint η) ∘ₗ phiMap hφ x.real :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  rw [LinearMap.real_sum]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.sum_comp, LinearMap.comp_sum,
    grad_adjoint_rank_one, Finset.sum_sub_distrib]

theorem sig_map_hMul [hφ : φ.IsFaithfulPosMap] (t : ℝ) (x y : ℍ) :
    hφ.sig t (x * y) = hφ.sig t x * hφ.sig t y := by
  simp only [_root_.map_mul]

private theorem phi_map_mul_rank_one [hφ : φ.IsFaithfulPosMap] (x y z w : ℍ) :
    phiMap hφ (Qam.reflIdempotent hφ |x⟩⟨y| |z⟩⟨w|) =
      phiMap hφ |x⟩⟨y| ∘ₗ phiMap hφ |z⟩⟨w| :=
  by
  simp_rw [Qam.RankOne.reflIdempotent_eq, phiMap_eq, LinearMap.comp_apply, ιMap_apply_rankOne,
    rmulMapLmul_apply, ← TensorProduct.map_comp, lmul_eq_mul, rmul_eq_mul, ← LinearMap.mulRight_mul,
    ← LinearMap.mulLeft_mul, ← sig_map_hMul, ← conjTranspose_mul]

theorem phiMap_mul [hφ : φ.IsFaithfulPosMap] (A B : l(ℍ)) :
    phiMap hφ (Qam.reflIdempotent hφ A B) = phiMap hφ A ∘ₗ phiMap hφ B :=
  by
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rankOne
  obtain ⟨γ, ζ, rfl⟩ := B.exists_sum_rankOne
  -- rw [linear_map.eq_rank_one_of_faithful_pos_map hφ A,
  --   B.eq_rank_one_of_faithful_pos_map hφ],
  simp_rw [map_sum, LinearMap.sum_apply, map_sum, phi_map_mul_rank_one, ← LinearMap.sum_comp, ←
    LinearMap.comp_sum]

theorem phiMap_of_real_Schur_idempotent [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ x x = x) :
    LinearMap.adjoint (phiMap hφ x) = phiMap hφ x ∧ IsIdempotentElem (phiMap hφ x) := by
  simp_rw [IsIdempotentElem, phiMap_adjoint, LinearMap.mul_eq_comp, ← phiMap_mul,
    (LinearMap.isReal_iff _).mp hx1, hx2, and_self_iff]

-- @[instance]
-- private def hmm {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
--     (U : Submodule ℂ H) : CompleteSpace U :=
--   FiniteDimensional.complete ℂ U

set_option synthInstance.maxHeartbeats 0 in
lemma phiMap_of_real_Schur_idempotent_orthogonal_projection [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ x x = x) :
    ∃ U : Submodule ℂ (ℍ ⊗[ℂ] ℍ), (orthogonalProjection' U : l(ℍ ⊗[ℂ] ℍ)) = phiMap hφ x :=
  by
  rw [orthogonal_projection_iff_lm, _root_.IsSelfAdjoint, LinearMap.star_eq_adjoint]
  simp_rw [phiMap_of_real_Schur_idempotent hx1 hx2, and_true_iff]

noncomputable def phiMap_of_real_Schur_idempotent.submodule [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx1 : x.IsReal)
  (hx2 : Qam.reflIdempotent hφ x x = x) : Submodule ℂ (ℍ ⊗[ℂ] ℍ) := by
-- (phiMap_of_real_Schur_idempotent_orthogonal_projection hx1 hx2).choose
choose U _ using phiMap_of_real_Schur_idempotent_orthogonal_projection hx1 hx2; exact U

instance phiMap_of_real_Schur_idempotent.submodule.complete
  [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx1 : x.IsReal)
  (hx2 : Qam.reflIdempotent hφ x x = x) :
  CompleteSpace (phiMap_of_real_Schur_idempotent.submodule hx1 hx2) :=
complete_of_proper

-- set_option synthInstance.maxHeartbeats 0 in
theorem phiMap_of_real_Schur_idempotent.orthogonal_projection_eq [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx1 : x.IsReal)
  (hx2 : Qam.reflIdempotent hφ x x = x) :
  (orthogonalProjection' (phiMap_of_real_Schur_idempotent.submodule hx1 hx2) : l(ℍ ⊗[ℂ] ℍ)) =
    phiMap hφ x :=
phiMap_of_real_Schur_idempotent.submodule.proof_6 hx1 hx2

theorem grad_apply_of_real_Schur_idempotent [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ x x = x) :
    phiMap hφ x ∘ₗ grad hφ x = grad hφ x := by
  simp_rw [grad_apply, (LinearMap.isReal_iff _).mp hx1, ← LinearMap.comp_sub, ←
    LinearMap.comp_assoc, ← phiMap_mul, hx2]

theorem grad_of_real_Schur_idempotent_range [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ x x = x) :
    LinearMap.range (grad hφ x) ≤ phiMap_of_real_Schur_idempotent.submodule hx1 hx2 :=
  by
  rw [← grad_apply_of_real_Schur_idempotent hx1 hx2, ←
    phiMap_of_real_Schur_idempotent.orthogonal_projection_eq hx1 hx2]
  nth_rw 2 [← orthogonalProjection.range (phiMap_of_real_Schur_idempotent.submodule hx1 hx2)]
  rw [LinearMap.range_le_iff_comap]
  -- rw [range_le_iff_comap],
  apply Submodule.ext
  simp_rw [Submodule.mem_top, iff_true_iff, Submodule.mem_comap, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, orthogonalProjection.range]
  intro a
  simp only [orthogonalProjection'_eq, ContinuousLinearMap.coe_comp', Submodule.coe_subtypeL',
    Submodule.coeSubtype, Function.comp_apply, SetLike.coe_mem]

noncomputable def dIn : l(ℍ) →ₗ[ℂ] l(ℍ)
    where
  toFun x := m ∘ₗ (x ⊗ₘ id) ∘ₗ tensorOneMap
  map_add' x y := by simp only [TensorProduct.add_map, LinearMap.comp_add, LinearMap.add_comp]
  map_smul' r x := by
    simp only [TensorProduct.smul_map, LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply]

set_option synthInstance.maxHeartbeats 0 in
set_option linter.unusedVariables false in
@[nolint unusedArguments]
noncomputable def dOut (hφ : φ.IsFaithfulPosMap) : l(ℍ) →+ l(ℍ) :=
  letI := Fact.mk hφ
  { toFun := fun x => m ∘ₗ (id ⊗ₘ LinearMap.adjoint x) ∘ₗ oneTensorMap
    map_add' := fun x y => by
      simp only [map_add, TensorProduct.map_add, LinearMap.comp_add, LinearMap.add_comp]
    map_zero' := by
      simp only [map_zero, TensorProduct.map_zero, LinearMap.zero_comp, LinearMap.comp_zero] }

theorem dIn_apply (x : l(ℍ)) : dIn x = lmul (x 1) :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [dIn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, tensorOneMap_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, LinearMap.one_apply, lmul_apply]

theorem dOut_apply [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) : dOut hφ x = rmul (LinearMap.adjoint x 1) :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [dOut, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.comp_apply, oneTensorMap_apply,
    TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.one_apply, rmul_apply]

theorem tensor_one_map_adjoint_comp_phiMap_comp_one_tensor_map_rankOne [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    τ ∘ₗ (LinearMap.adjoint η ⊗ₘ id) ∘ₗ phiMap hφ |x⟩⟨y| ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ = |x⟩⟨y| :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.comm_symm_tmul, TensorProduct.map_tmul, LinearMap.one_apply,
    Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, phiMap_eq, LinearMap.comp_apply,
    ιMap_apply_rankOne, rmulMapLmul_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    lmul_apply, rmul_apply, Nontracial.unit_adjoint_eq]
  have := Module.Dual.IsFaithfulPosMap.hMul_left hφ aᴴ y 1
  rw [Matrix.one_mul, Matrix.mul_one, ← sig_neg_one, conjTranspose_conjTranspose,
    conjTranspose_mul, conjTranspose_conjTranspose] at this
  simp only [LinearMap.one_apply, mul_one, mul_one, ← this, one_smul, Matrix.mul_one]
  rw [← rankOneLm_eq_rankOne, rankOneLm_apply, Module.Dual.IsFaithfulPosMap.inner_eq]

theorem tensor_one_map_adjoint_comp_phiMap_comp_one_tensor_map [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    τ ∘ₗ (LinearMap.adjoint η ⊗ₘ id) ∘ₗ phiMap hφ x ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ = x :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.sum_apply,
    tensor_one_map_adjoint_comp_phiMap_comp_one_tensor_map_rankOne]

private theorem tensor_one_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    τ ∘ₗ (LinearMap.adjoint η ⊗ₘ id) ∘ₗ phiMap hφ |x⟩⟨y| ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ = dIn (|x⟩⟨y| : l(ℍ)) :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.map_tmul, LinearMap.one_apply, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, phiMap_eq, LinearMap.comp_apply, ιMap_apply_rankOne,
    rmulMapLmul_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul, lmul_apply, rmul_apply,
    Nontracial.unit_adjoint_eq, one_smul, one_mul, LinearMap.one_apply, dIn_apply, lmul_eq_mul,
    ContinuousLinearMap.coe_coe, rankOne_apply, LinearMap.mulLeft_apply, ←
    AlgEquiv.toLinearMap_apply, ← LinearMap.comp_apply, linear_functional_comp_sig,
    Module.Dual.IsFaithfulPosMap.inner_eq, Matrix.mul_one, smul_mul_assoc]

theorem tensor_one_map_adjoint_comp_phiMap_comp_tensor_one_map [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    τ ∘ₗ (LinearMap.adjoint η ⊗ₘ id) ∘ₗ phiMap hφ x ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ = dIn x :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.sum_apply,
    tensor_one_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one]

private theorem one_tensor_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ LinearMap.adjoint η) ∘ₗ phiMap hφ |x⟩⟨y| ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ =
      LinearMap.adjoint (|x⟩⟨y| : l(ℍ)).real :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.map_tmul, LinearMap.one_apply, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, phiMap_eq, LinearMap.comp_apply, ιMap_apply_rankOne,
    rmulMapLmul_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul, TensorProduct.lid_tmul,
    lmul_apply, rmul_apply, Nontracial.unit_adjoint_eq, one_smul, one_mul, LinearMap.one_apply,
    rankOne_real_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint, rankOneLm_apply,
    Module.Dual.IsFaithfulPosMap.inner_eq, conjTranspose_conjTranspose]

theorem one_tensor_map_adjoint_comp_phiMap_comp_tensor_one_map [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ LinearMap.adjoint η) ∘ₗ phiMap hφ x ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ = LinearMap.adjoint x.real :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.sum_apply,
    one_tensor_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one, LinearMap.real_sum]

private theorem one_tensor_map_adjoint_comp_phi_map_comp_one_tensor_map_rank_one [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ LinearMap.adjoint η) ∘ₗ phiMap hφ |x⟩⟨y| ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ =
      dOut hφ (|x⟩⟨y| : l(ℍ)).real :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.comm_symm_tmul, TensorProduct.map_tmul, LinearMap.one_apply,
    Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, phiMap_eq, LinearMap.comp_apply,
    ιMap_apply_rankOne, rmulMapLmul_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul,
    TensorProduct.lid_tmul, lmul_apply, rmul_apply, Nontracial.unit_adjoint_eq, one_smul, mul_one,
    LinearMap.one_apply, dOut_apply, rmul_eq_mul, rankOne_real_apply, ← rankOneLm_eq_rankOne,
    rankOneLm_adjoint, LinearMap.mulRight_apply, rankOneLm_apply, ← AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.inner_eq, Matrix.mul_one, conjTranspose_conjTranspose,
    mul_smul_comm]

theorem one_tensor_map_adjoint_comp_phiMap_comp_one_tensor_map [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ LinearMap.adjoint η) ∘ₗ phiMap hφ x ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ =
      dOut hφ x.real :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  simp only [dOut_apply, map_sum, LinearMap.real_sum, map_sum]
  simp_rw [← dOut_apply]
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.sum_apply,
    one_tensor_map_adjoint_comp_phi_map_comp_one_tensor_map_rank_one, LinearMap.real_sum]

private theorem qam.refl_idempotent_real_rank_one [hφ : φ.IsFaithfulPosMap] (a b c d : ℍ) :
    (Qam.reflIdempotent hφ |a⟩⟨b| |c⟩⟨d|).real =
      Qam.reflIdempotent hφ (|c⟩⟨d| : l(ℍ)).real (|a⟩⟨b| : l(ℍ)).real :=
  by
  simp only [Qam.RankOne.reflIdempotent_eq, rankOne_real_apply, ← sig_map_hMul, ←
    conjTranspose_mul]

theorem Qam.reflIdempotent_real [hφ : φ.IsFaithfulPosMap] (a b : l(ℍ)) :
    (Qam.reflIdempotent hφ a b).real = Qam.reflIdempotent hφ b.real a.real :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rankOne
  obtain ⟨γ, ζ, rfl⟩ := b.exists_sum_rankOne
  simp only [map_sum, LinearMap.real_sum, LinearMap.sum_apply, qam.refl_idempotent_real_rank_one]
  rw [Finset.sum_comm]

theorem Qam.reflIdempotent_adjoint [hφ : φ.IsFaithfulPosMap] (a b : l(ℍ)) :
    LinearMap.adjoint (Qam.reflIdempotent hφ a b) = Qam.reflIdempotent hφ (LinearMap.adjoint a) (LinearMap.adjoint b) :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rankOne
  obtain ⟨γ, ζ, rfl⟩ := b.exists_sum_rankOne
  simp_rw [map_sum, LinearMap.sum_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    rankOneLm_eq_rankOne, Qam.RankOne.reflIdempotent_eq, map_sum, ← rankOneLm_eq_rankOne,
    rankOneLm_adjoint]

private theorem D_in_Schur_product_eq_ir_refl_rank_one [hφ : φ.IsFaithfulPosMap] (a b c d : ℍ) :
    dIn (Qam.reflIdempotent hφ |a⟩⟨b| |c⟩⟨d|) =
      Qam.reflIdempotent hφ ((|a⟩⟨b| : l(ℍ)) ∘ₗ LinearMap.adjoint (|c⟩⟨d| : l(ℍ)).real) id :=
  by
  simp_rw [dIn_apply, rankOne_real_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    rankOneLm_comp_rankOneLm, _root_.map_smul, LinearMap.smul_apply, rankOneLm_eq_rankOne]
  rw [Qam.RankOne.reflIdempotent_eq, Qam.reflexive_eq_rankOne, ← rankOneLm_eq_rankOne,
    rankOneLm_apply, Module.Dual.IsFaithfulPosMap.inner_right_conj, sig_neg_one,
    conjTranspose_conjTranspose, Matrix.one_mul, _root_.map_smul, lmul_eq_mul]

theorem dIn_Schur_product_eq_ir_refl [hφ : φ.IsFaithfulPosMap] (A B : l(ℍ)) :
    dIn (Qam.reflIdempotent hφ A B) = Qam.reflIdempotent hφ (A ∘ₗ LinearMap.adjoint B.real) id :=
  by
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rankOne
  obtain ⟨α, β, rfl⟩ := B.exists_sum_rankOne
  simp only [map_sum, LinearMap.sum_apply, LinearMap.real_sum, LinearMap.comp_sum,
    LinearMap.sum_comp, D_in_Schur_product_eq_ir_refl_rank_one]

private theorem D_out_Schur_product_eq_ir_refl'_rank_one [hφ : φ.IsFaithfulPosMap] (a b c d : ℍ) :
    dOut hφ (Qam.reflIdempotent hφ |a⟩⟨b| |c⟩⟨d|) =
      Qam.reflIdempotent hφ id (LinearMap.adjoint (|c⟩⟨d| : l(ℍ)) ∘ₗ (|a⟩⟨b| : l(ℍ)).real) :=
  by
  simp_rw [dOut_apply, rankOne_real_apply, Qam.RankOne.reflIdempotent_eq, ← rankOneLm_eq_rankOne,
    rankOneLm_adjoint, rankOneLm_comp_rankOneLm, _root_.map_smul, rankOneLm_eq_rankOne,
    Qam.reflexive'_eq_rankOne, ContinuousLinearMap.coe_coe, rankOne_apply, _root_.map_smul,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, conjTranspose_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, add_neg_self, Module.Dual.IsFaithfulPosMap.sig_zero,
    Module.Dual.IsFaithfulPosMap.inner_left_hMul, Matrix.mul_one]
  rfl

theorem dOut_Schur_product_eq_ir_refl' [hφ : φ.IsFaithfulPosMap] (A B : l(ℍ)) :
    dOut hφ (Qam.reflIdempotent hφ A B) =
      Qam.reflIdempotent hφ id (LinearMap.adjoint B ∘ₗ A.real) :=
  by
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rankOne
  obtain ⟨α, β, rfl⟩ := B.exists_sum_rankOne
  simp only [map_sum, LinearMap.sum_apply, LinearMap.real_sum, LinearMap.comp_sum,
    LinearMap.sum_comp, D_out_Schur_product_eq_ir_refl'_rank_one]
  rw [Finset.sum_comm]

set_option maxHeartbeats 0 in
theorem grad_adjoint_grad [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    LinearMap.adjoint (grad hφ x) ∘ₗ grad hφ x =
      dIn (Qam.reflIdempotent hφ x x.real) - Qam.reflIdempotent hφ x x -
          Qam.reflIdempotent hφ (LinearMap.adjoint x) (LinearMap.adjoint x) +
        dOut hφ (Qam.reflIdempotent hφ x.real x) :=
  by
  simp_rw [grad, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.adjoint_comp, map_sub, LinearMap.adjoint_adjoint,
    TensorProduct.map_adjoint, LinearMap.adjoint_one, LinearMap.adjoint_adjoint]
  simp only [LinearMap.comp_sub, LinearMap.sub_comp]
  simp_rw [← LinearMap.comp_assoc, LinearMap.comp_assoc (_ ⊗ₘ _) (_ ⊗ₘ _), ← TensorProduct.map_comp,
    LinearMap.one_comp, LinearMap.comp_one, dIn_Schur_product_eq_ir_refl,
    dOut_Schur_product_eq_ir_refl', Qam.reflIdempotent, schurIdempotent_apply_apply,
    LinearMap.real_real, LinearMap.comp_assoc, sub_eq_add_neg, neg_add, neg_neg,
    ← LinearMap.neg_comp, add_assoc]
  symm
  congr 1
  nth_rw 1 [add_rotate']
  congr 1
  nth_rw 1 [add_comm]
  -- congr 1

set_option synthInstance.maxHeartbeats 0 in
theorem ι_inv_grad_apply_rankOne [hφ : φ.IsFaithfulPosMap] (a b x : ℍ) :
    (ιInvMap hφ) ((grad hφ |a⟩⟨b|) x) =
      rmul x ∘ₗ (|a⟩⟨b| : l(ℍ)).real - (|a⟩⟨b| : l(ℍ)) ∘ₗ rmul x :=
  by
  simp_rw [grad_apply, ιInvMap, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    LinearMap.comp_apply, tensorOneMap_apply, oneTensorMap_apply, phiMap_eq, LinearMap.comp_apply,
    rankOne_real_apply, ιMap_apply_rankOne, rmulMapLmul_apply, TensorProduct.map_tmul,
    tenSwap_apply, LinearEquiv.coe_coe, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_symm_mk,
    Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, neg_zero, Module.Dual.IsFaithfulPosMap.sig_zero,
    LinearMap.one_apply, op_apply, unop_apply, MulOpposite.unop_op,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, Module.Dual.IsFaithfulPosMap.sig_apply_sig,
    neg_neg, neg_add_self, Module.Dual.IsFaithfulPosMap.sig_zero, lmul_apply, rmul_apply]
  rw [← @LinearMap.mulRight_apply ℂ _ _ _ _ _ _ x aᴴ, ← LinearMap.comp_rankOne]
  -- simp_rw [Module.Dual.IsFaithfulPosMap.sig_conjTranspose]
  simp_rw [mul_one, one_mul, conjTranspose_mul, sig_map_hMul,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, Module.Dual.IsFaithfulPosMap.sig_apply_sig,
    add_neg_self, Module.Dual.IsFaithfulPosMap.sig_zero,
    conjTranspose_conjTranspose, ← @LinearMap.mulRight_apply ℂ _ _ _ _ _ _ _ b, ←
    LinearMap.matrix.mulRight_adjoint, ← LinearMap.rankOne_comp]
  rfl

theorem ιInvMap_apply [hφ : φ.IsFaithfulPosMap] (x y : ℍ) : ιInvMap hφ (x ⊗ₜ[ℂ] y) = |y⟩⟨hφ.sig (-1) xᴴ| := by
  simp_rw [ιInvMap, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    tenSwap_apply, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_symm_mk,
    Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, op_apply, unop_apply, MulOpposite.unop_op,
    neg_zero, Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.one_apply]

theorem phiMap_eq' [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    phiMap hφ x = ιMap hφ ∘ₗ Qam.reflIdempotent hφ x ∘ₗ ιInvMap hφ :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  simp_rw [map_sum, LinearMap.sum_comp, LinearMap.comp_sum]
  apply Finset.sum_congr rfl; intros
  rw [TensorProduct.ext_iff]
  intro a b
  simp_rw [phiMap_eq, LinearMap.comp_apply, ιInvMap_apply, ιMap_apply_rankOne, rmulMapLmul_apply,
    TensorProduct.map_tmul, Qam.RankOne.reflIdempotent_eq, ιMap_apply_rankOne, rmul_apply,
    lmul_apply, conjTranspose_mul, Module.Dual.IsFaithfulPosMap.sig_conjTranspose, sig_map_hMul,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, add_neg_self, Module.Dual.IsFaithfulPosMap.sig_zero,
    conjTranspose_conjTranspose]

theorem phiMapMapsToBimoduleMaps [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} : (phiMap hφ A).IsBimoduleMap :=
  by
  intro x y a
  obtain ⟨α, β, rfl⟩ := TensorProduct.eq_span a
  obtain ⟨γ, ζ, rfl⟩ := A.exists_sum_rankOne
  simp_rw [map_sum, LinearMap.sum_apply, Bimodule.lsmul_sum, Bimodule.sum_rsmul, phiMap_eq,
    LinearMap.comp_apply, ιMap_apply_rankOne, rmulMapLmul_apply, map_sum]
  simp only [Bimodule.rsmul_apply, Bimodule.lsmul_apply, TensorProduct.map_tmul, rmul_apply,
    lmul_apply, Matrix.mul_assoc]
  rw [Finset.sum_comm]

open scoped Bimodule
open Bimodule in
noncomputable def LinearMap.IsBimoduleMaps.Submodule' :
  Submodule ℂ (l(ℍ ⊗[ℂ] ℍ)) :=
{ carrier := λ x => x.IsBimoduleMap
  add_mem' :=
    λ a b ha hb => by
      intro x
      simp_rw [LinearMap.add_apply]
      rw [a, b]
      simp_rw [Bimodule.lsmul_add, Bimodule.add_rsmul]
  zero_mem' := λ _ _ _ => by simp only [zero_apply, lsmul_zero, zero_rsmul]
  smul_mem' := λ r x hx => hx.smul r }

-- set_option synthInstance.maxHeartbeats 0 in
theorem phiMap_range [hφ : φ.IsFaithfulPosMap] : LinearMap.range (phiMap hφ) ≤ (LinearMap.IsBimoduleMaps.Submodule' : Submodule ℂ (l(ℍ ⊗[ℂ] ℍ))) :=
  by
  intro A
  simp_rw [LinearMap.mem_range]
  rintro ⟨y, rfl⟩
  exact phiMapMapsToBimoduleMaps

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_3 x_4) -/
theorem orthonormal_basis_tensorProduct_sum_repr [hφ : φ.IsFaithfulPosMap] (a b : ℍ) :
    ∑ x_3 : p × p, ∑ x_4 : p × p,
        ⟪(hφ.basis.tensorProduct hφ.basis) (x_3, x_4), a ⊗ₜ[ℂ] b⟫_ℂ •
          (hφ.basis.tensorProduct hφ.basis) (x_3, x_4) =
      a ⊗ₜ b :=
  by
  simp_rw [Basis.tensorProduct_apply', TensorProduct.inner_tmul, ← TensorProduct.smul_tmul_smul, ←
    TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, Module.Dual.IsFaithfulPosMap.basis_apply, ←
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, ← OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.sum_repr]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_1 x_2 x_3 x_4) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_3 x_4) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_1 x_2) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 0 in
theorem LinearMap.tensor_matrix_eq_rankOne [hφ : φ.IsFaithfulPosMap] (x : l(ℍ ⊗[ℂ] ℍ)) :
    x =
      ∑ i, ∑ j, ∑ k, ∑ l,
        ⟪(Basis.tensorProduct hφ.basis hφ.basis) (i, j),
            x ((Basis.tensorProduct hφ.basis hφ.basis) (k, l))⟫_ℂ •
          |(Basis.tensorProduct hφ.basis hφ.basis)
              (i, j)⟩⟨(Basis.tensorProduct hφ.basis hφ.basis) (k, l)| :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  rw [TensorProduct.inner_ext_iff']
  intro c d
  simp_rw [ContinuousLinearMap.coe_sum, ContinuousLinearMap.coe_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_smul_left,
    ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left, inner_conj_symm]
  have :=
    calc
      ∑ x_1 : p × p, ∑ x_2 : p × p, ∑ x_3 : p × p, ∑ x_4 : p × p,
            ⟪x ((hφ.basis.tensorProduct hφ.basis) (x_3, x_4)),
                  (hφ.basis.tensorProduct hφ.basis) (x_1, x_2)⟫_ℂ *
                ⟪a ⊗ₜ[ℂ] b, (hφ.basis.tensorProduct hφ.basis) (x_3, x_4)⟫_ℂ *
              ⟪(hφ.basis.tensorProduct hφ.basis) (x_1, x_2), c ⊗ₜ[ℂ] d⟫_ℂ =
          ⟪x
              (∑ x_3 : p × p, ∑ x_4 : p × p,
                ⟪(hφ.basis.tensorProduct hφ.basis) (x_3, x_4), a ⊗ₜ[ℂ] b⟫_ℂ •
                  (hφ.basis.tensorProduct hφ.basis) (x_3, x_4)),
              ∑ x_1 : p × p, ∑ x_2 : p × p,
              ⟪(hφ.basis.tensorProduct hφ.basis) (x_1, x_2), c ⊗ₜ[ℂ] d⟫_ℂ •
                (hφ.basis.tensorProduct hφ.basis) (x_1, x_2)⟫_ℂ :=
        ?_
      _ = ⟪x (a ⊗ₜ b), c ⊗ₜ d⟫_ℂ := ?_
  · simp_rw [← this, mul_assoc]
    repeat'
      apply Finset.sum_congr rfl; intros
    symm
    congr 1
    exact @inner_conj_symm ℂ (ℍ ⊗[ℂ] ℍ) _ (TensorProduct.normedAddCommGroup) (TensorProduct.innerProductSpace) _ _
  . simp_rw [map_sum, inner_sum, sum_inner, _root_.map_smul, inner_smul_right,
      inner_smul_left, @inner_conj_symm ℂ (ℍ ⊗[ℂ] ℍ) _ (TensorProduct.normedAddCommGroup) (TensorProduct.innerProductSpace)]
      -- Basis.tensorProduct_apply, starRingEnd_apply,
      -- mul_star, ← starRingEnd_apply, inner_conj_symm]
    repeat'
      apply Finset.sum_congr rfl; intros
    simp_rw [mul_assoc]
    rw [mul_comm ⟪a ⊗ₜ b, _⟫_ℂ ⟪_, c ⊗ₜ d⟫_ℂ]
    rw [mul_rotate']
    -- simp only [← mul_assoc, mul_comm, mul_rotate]
  · simp_rw [orthonormal_basis_tensorProduct_sum_repr]

set_option synthInstance.maxHeartbeats 0 in
noncomputable def phiInvMap (hφ : φ.IsFaithfulPosMap) :
    (LinearMap.IsBimoduleMaps.Submodule' : Submodule ℂ l(ℍ ⊗[ℂ] ℍ)) →ₗ[ℂ] l(ℍ)
    where
  toFun x := ιInvMap hφ ((x : l(ℍ ⊗[ℂ] ℍ)) 1)
  map_add' x y := by simp_rw [Submodule.coe_add, LinearMap.add_apply, map_add]
  map_smul' r x := by
    simp only [Submodule.coe_smul, LinearMap.smul_apply, _root_.map_smul, RingHom.id_apply]

noncomputable def phiInv'Map (hφ : φ.IsFaithfulPosMap) : l(ℍ ⊗[ℂ] ℍ) →ₗ[ℂ] l(ℍ) :=
  { toFun := fun x => τ ∘ₗ (LinearMap.adjoint η ⊗ₘ id) ∘ₗ (x : l(ℍ ⊗[ℂ] ℍ)) ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹
    map_add' := fun x y => by simp only [Submodule.coe_add, LinearMap.add_comp, LinearMap.comp_add]
    map_smul' := fun r x => by
      simp only [Submodule.coe_smul, LinearMap.comp_smul, LinearMap.smul_comp,
        _root_.map_smul, RingHom.id_apply] }

noncomputable def phiInv'MapCoe (hφ : φ.IsFaithfulPosMap) :
    (LinearMap.IsBimoduleMaps.Submodule' : Submodule ℂ l(ℍ ⊗[ℂ] ℍ)) →ₗ[ℂ] l(ℍ) :=
  letI := Fact.mk hφ
  { toFun := fun x => phiInv'Map hφ x
    map_add' := fun x y => by
      simp only [phiInv'Map, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, LinearMap.add_comp,
        LinearMap.comp_add]
    map_smul' := fun r x => by
      simp only [phiInv'Map, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul, LinearMap.comp_smul,
        LinearMap.smul_comp, _root_.map_smul, RingHom.id_apply] }

theorem phiInv'Map_apply (hφ : φ.IsFaithfulPosMap) (x y : l(ℍ)) :
    phiInv'Map hφ (x ⊗ₘ y) = y ∘ₗ (|(1 : ℍ)⟩⟨(1 : ℍ)| : l(ℍ)) ∘ₗ x :=
  by
  simp_rw [LinearMap.ext_iff]
  intro a
  simp_rw [phiInv'Map, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.lid_symm_apply, TensorProduct.comm_symm_tmul, TensorProduct.map_tmul,
    TensorProduct.lid_tmul, ContinuousLinearMap.coe_coe, LinearMap.one_apply,
    Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, Nontracial.unit_adjoint_eq,
    rankOne_apply, Module.Dual.IsFaithfulPosMap.inner_eq, conjTranspose_one, one_smul,
    Matrix.one_mul, _root_.map_smul]

theorem ιLinearEquiv_apply_eq (hφ : φ.IsFaithfulPosMap) (x : l(ℍ)) : ιLinearEquiv hφ x = ιMap hφ x :=
  rfl

theorem ιLinearEquiv_symm_apply_eq (hφ : φ.IsFaithfulPosMap) (x : ℍ ⊗[ℂ] ℍ) :
    (ιLinearEquiv hφ).symm x = ιInvMap hφ x :=
  rfl

noncomputable def phiMapCoe (hφ : φ.IsFaithfulPosMap) :
    l(ℍ) →ₗ[ℂ] (LinearMap.IsBimoduleMaps.Submodule' : Submodule ℂ l(ℍ ⊗[ℂ] ℍ))
    where
  toFun x :=
    ⟨phiMap hφ x, @phiMapMapsToBimoduleMaps p _ _ φ hφ x⟩
  map_add' x y :=
    by
      simp only [map_add]
      ext
      simp only [LinearMap.add_apply, Submodule.coe_add, Subtype.coe_mk]
  map_smul' r x :=
    by
      simp only [_root_.map_smul]
      ext
      simp only [LinearMap.smul_apply, Submodule.coe_smul, Subtype.coe_mk, RingHom.id_apply]

theorem phi_map_left_inverse [hφ : φ.IsFaithfulPosMap] : phiInvMap hφ ∘ₗ phiMapCoe hφ = 1 :=
  by
  apply LinearMap.ext_of_rank_one'
  intro x y
  simp_rw [LinearMap.one_apply, LinearMap.comp_apply, phiMapCoe, LinearMap.coe_mk, phiMap_eq',
    phiInvMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [LinearMap.comp_apply]
  simp_rw [← ιLinearEquiv_apply_eq, ← ιLinearEquiv_symm_apply_eq, LinearEquiv.symm_apply_apply]
  have : (ιLinearEquiv hφ).symm 1 = Qam.completeGraph ℍ :=
    by
    simp_rw [ιLinearEquiv_symm_apply_eq, Algebra.TensorProduct.one_def, ιInvMap_apply,
      conjTranspose_one, _root_.map_one]
    rfl
  rw [this, Qam.reflIdempotent, Qam.refl_idempotent_completeGraph_right]

theorem phi_map_left_inverse' [hφ : φ.IsFaithfulPosMap] : (phiInvMap hφ) ∘ (phiMapCoe hφ)
  = ⇑(1 : l(ℍ →ₗ[ℂ] ℍ)) :=
by
  have := @phi_map_left_inverse p _ _ φ hφ
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply] at this
  ext1 x
  ext1 a
  simp_rw [Function.comp_apply, this]

theorem phi_inv'_map_phi_map [hφ : φ.IsFaithfulPosMap] : phiInv'MapCoe hφ ∘ₗ phiMapCoe hφ = 1 :=
  by
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [phiInv'MapCoe, phiMapCoe, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    phiMap_eq,
    LinearMap.comp_apply, ιMap_apply_rankOne, rmulMapLmul_apply, phiInv'Map_apply,
    rmul_eq_mul, ← LinearMap.matrix.mulRight_adjoint, LinearMap.rankOne_comp',
    LinearMap.comp_rankOne, lmul_apply, LinearMap.mulRight_apply, mul_one, one_mul,
    LinearMap.one_apply]

theorem phi_inv'_map_phi_map' [hφ : φ.IsFaithfulPosMap] : phiInv'MapCoe hφ ∘ phiMapCoe hφ = ⇑(1 : l(l(ℍ))) :=
by
  have := @phi_inv'_map_phi_map p _ _ φ hφ
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply] at this
  ext1 x
  ext1 a
  simp_rw [Function.comp_apply, this]

theorem phi_map_right_inverse [hφ : φ.IsFaithfulPosMap] (x : { x : l(ℍ ⊗[ℂ] ℍ) // x.IsBimoduleMap }) :
    phiMapCoe hφ (phiInvMap hφ x) = x :=
  by
  simp_rw [phiInvMap, LinearMap.coe_mk, AddHom.coe_mk, phiMapCoe, LinearMap.coe_mk,
    AddHom.coe_mk, phiMap_eq,
    LinearMap.comp_apply, ← ιLinearEquiv_apply_eq, ← ιLinearEquiv_symm_apply_eq,
    LinearEquiv.apply_symm_apply, Subtype.ext_iff, TensorProduct.ext_iff]
  intro a b
  rw [rmulMapLmul_apply_apply, ← Subtype.mem x, Bimodule.lsmul_one, Bimodule.rsmul_apply, one_mul]

noncomputable def phiLinearEquiv (hφ : φ.IsFaithfulPosMap) :
    l(ℍ) ≃ₗ[ℂ] { x : l(ℍ ⊗[ℂ] ℍ) // x.IsBimoduleMap } :=
  letI := Fact.mk hφ
  { toFun := fun x => phiMapCoe hφ x
    invFun := fun x => phiInvMap hφ x
    left_inv := fun x => by
      simp only [← LinearMap.comp_apply, phi_map_left_inverse, LinearMap.one_apply, Subtype.coe_mk]
    right_inv := fun x => by simp only [phi_map_right_inverse x, Subtype.coe_eta]
    map_add' := fun x y => by simp only [map_add, Subtype.coe_eta]
    map_smul' := fun r x => by simp only [_root_.map_smul, RingHom.id_apply] }

theorem LinearEquiv.comp_inj {R M₁ M₂ M₃ : Type _} [Semiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ ≃ₗ[R] M₂) {x y : M₂ →ₗ[R] M₃} :
    x = y ↔ x ∘ₗ (f : M₁ →ₗ[R] M₂) = y ∘ₗ (f : M₁ →ₗ[R] M₂) :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply]
  refine' ⟨fun h a => by rw [h], fun h a => _⟩
  specialize h (f.symm a)
  simp_rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
  exact h

set_option maxHeartbeats 600000 in
theorem phi_inv'_map_eq_phi_inv'_map [hφ : φ.IsFaithfulPosMap] : phiInvMap hφ = phiInv'MapCoe hφ := by
  simp_rw [LinearEquiv.comp_inj (phiLinearEquiv hφ), phiLinearEquiv, LinearMap.ext_iff,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  intros i j
  congr 1
  calc (phiInvMap hφ) ((phiMapCoe hφ) i)
      = (phiInvMap hφ ∘ phiMapCoe hφ) i := rfl
    _ = (1 : l(l(ℍ))) i := by simp only [phi_map_left_inverse']
    _ = (phiInv'MapCoe hφ ∘ phiMapCoe hφ) i := by simp only [phi_inv'_map_phi_map']
    _ = (phiInv'MapCoe hφ) ((phiMapCoe hφ) i) := rfl

  -- simp_rw [← Function.comp_apply _ (phiInvMap hφ), phi_map_lefφverse', phi_inv'_map_phi_map', forall₂_true_iff]

theorem sig_apply_sig_inv [hφ : φ.IsFaithfulPosMap] {t : ℝ} {x : ℍ} : hφ.sig t (hφ.sig (-t) x) = x := by
  rw [sig_eq_iff_eq_sig_inv]

theorem sig_inv_apply_sig [hφ : φ.IsFaithfulPosMap] {t : ℝ} {x : ℍ} : hφ.sig (-t) (hφ.sig t x) = x :=
  by
  symm
  rw [← sig_eq_iff_eq_sig_inv]

theorem rsmul_module_map_of_real_lsmul_module_map {n : Type _} [Fintype n] {f : l(Matrix n n ℂ)}
    (hf : ∀ a x : Matrix n n ℂ, f (a * x) = a * f x) (a x : Matrix n n ℂ) :
    f.real (a * x) = f.real a * x := by
  simp_rw [LinearMap.real_apply, star_eq_conjTranspose, conjTranspose_mul, hf, conjTranspose_mul,
    conjTranspose_conjTranspose]

theorem lsmul_module_map_iff_symm_eq_rsmul_module_map [hφ : φ.IsFaithfulPosMap] {f : l(ℍ)} :
    f = rmul (f 1) ↔ LinearEquiv.symmMap ℂ ℍ f = lmul (f 1) :=
  by
  rw [← LinearEquiv.eq_symm_apply, LinearEquiv.symmMap_symm_apply,
    @lmul_adjoint _ _ _ _ _ _ _ φ fun x y => by
        simp only [star_eq_conjTranspose]
        exact Module.Dual.IsFaithfulPosMap.inner_eq x y,
    lmul_eq_mul, LinearMap.mulLeft_real, star_star, rmul_eq_mul]

theorem LinearMap.real_adjoint_eq [hφ : φ.IsFaithfulPosMap] (f : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) :
    LinearMap.adjoint (f.real) =
      (hφ.sig (-1)).toLinearMap ∘ₗ (LinearMap.adjoint f).real ∘ₗ (hφ.sig 1).toLinearMap :=
  by
  rw [LinearMap.adjoint_real_apply]
  simp_rw [LinearMap.ext_iff]
  intro x
  rw [LinearMap.comp_apply]
  rw [AlgEquiv.toLinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply]
  simp_rw [AlgEquiv.toLinearMap_apply, sig_inv_apply_sig]
  -- simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, sig_inv_apply_sig, forall_true_iff]

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 0 in
theorem left_hand_twist_eq_sig_one [hφ : φ.IsFaithfulPosMap] :
    τ ∘ₗ
        ((LinearMap.adjoint η ∘ₗ m) ⊗ₘ id) ∘ₗ
          υ⁻¹ ∘ₗ
            (id ⊗ₘ
                ((TensorProduct.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ)) ∘ₗ
              υ ∘ₗ (LinearMap.adjoint m ⊗ₘ id) ∘ₗ (tensorOneMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) =
      (hφ.sig 1).toLinearMap :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp only [LinearMap.comp_apply, tensorOneMap_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply, LinearMap.mul'_adjoint, one_apply, boole_mul, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, LinearMap.one_apply]
  simp only [TensorProduct.sum_tmul, map_sum, ← TensorProduct.smul_tmul', _root_.map_smul,
    TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    TensorProduct.assoc_symm_tmul, TensorProduct.lid_tmul, LinearMap.comp_apply,
    LinearMap.mul'_apply, LinearMap.one_apply, Nontracial.unit_adjoint_eq]
  have : ∀ i j : p, φ (stdBasisMatrix i j 1 * x) = (x * φ.matrix) j i :=
    by
    intro i j
    rw [← star_one ℂ, ← stdBasisMatrix_conjTranspose, ← Module.Dual.IsFaithfulPosMap.inner_eq,
      inner_stdBasisMatrix_left]
  rw [Finset.sum_rotate]
  simp only [this, smul_smul, ← Finset.sum_smul, ← mul_apply]
  simp_rw [← smul_stdBasisMatrix']
  rw [← matrix_eq_sum_std_basis (φ.matrix⁻¹ * (x * _)), sig_one, Matrix.mul_assoc]

set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 0 in
theorem right_hand_twist_eq_sig_neg_one [hφ : φ.IsFaithfulPosMap] :
    τ ∘ₗ
        ϰ ∘ₗ
          (id ⊗ₘ LinearMap.adjoint η ∘ₗ m) ∘ₗ
            υ ∘ₗ
              (((TensorProduct.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) ⊗ₘ
                  id) ∘ₗ
                υ⁻¹ ∘ₗ (id ⊗ₘ LinearMap.adjoint m) ∘ₗ (oneTensorMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) =
      (hφ.sig (-1)).toLinearMap :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp only [LinearMap.comp_apply, oneTensorMap_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply, LinearMap.mul'_adjoint, one_apply, boole_mul, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, LinearMap.one_apply]
  simp only [TensorProduct.tmul_sum, map_sum, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul',
    _root_.map_smul, TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.lid_tmul,
    LinearMap.comp_apply, LinearMap.mul'_apply, LinearMap.one_apply, Nontracial.unit_adjoint_eq]
  have : ∀ i j : p, φ (x * stdBasisMatrix i j 1) = (φ.matrix * x) j i :=
    by
    intro i j
    rw [← conjTranspose_conjTranspose x, ← Module.Dual.IsFaithfulPosMap.inner_eq, ←
      inner_conj_symm, inner_stdBasisMatrix_left, starRingEnd_apply, ← star_apply,
      star_eq_conjTranspose, conjTranspose_mul, hφ.matrixIsPosDef.1.eq]
  simp only [this, smul_smul, ← Finset.sum_smul, ← mul_apply]
  simp_rw [← smul_stdBasisMatrix', mul_comm, ← mul_apply]
  rw [← matrix_eq_sum_std_basis (φ.matrix * x * _), sig_neg_one]

theorem balance_symm_1 [hφ : φ.IsFaithfulPosMap] :
    (LinearMap.adjoint η ∘ₗ m ∘ₗ (hφ.sig 1).toLinearMap ⊗ₘ id) =
      LinearMap.adjoint η ∘ₗ m ∘ₗ id ⊗ₘ (hφ.sig (-1)).toLinearMap :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Nontracial.unit_adjoint_eq, LinearMap.one_apply, AlgEquiv.toLinearMap_apply]
  nth_rw 1 [← linear_functional_apply_sig (-1)]
  rw [_root_.map_mul (hφ.sig (-1)) _ b, sig_inv_apply_sig]

theorem balance_symm_2 [hφ : φ.IsFaithfulPosMap] :
    (LinearMap.adjoint η ∘ₗ m ∘ₗ id ⊗ₘ (hφ.sig (-1)).toLinearMap) =
      LinearMap.adjoint η ∘ₗ
        m ∘ₗ ((TensorProduct.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Nontracial.unit_adjoint_eq, TensorProduct.comm_tmul, LinearMap.one_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply]
  calc
    φ (a * hφ.sig (-1) b) = ⟪aᴴ, hφ.sig (-1) b⟫_ℂ := by
      rw [Module.Dual.IsFaithfulPosMap.inner_eq, conjTranspose_conjTranspose]
    _ = ⟪bᴴ, a⟫_ℂ := by
      rw [Nontracial.inner_symm, Module.Dual.IsFaithfulPosMap.sig_conjTranspose, sig_apply_sig_inv,
        conjTranspose_conjTranspose]
    _ = φ (b * a) := by rw [Module.Dual.IsFaithfulPosMap.inner_eq, conjTranspose_conjTranspose]
