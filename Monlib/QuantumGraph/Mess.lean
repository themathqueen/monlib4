/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import QuantumGraph.Nontracial
import QuantumGraph.ToProjections
import QuantumGraph.QamA
import LinearAlgebra.MyBimodule
import QuantumGraph.Symm
import QuantumGraph.SchurIdempotent

#align_import quantum_graph.mess

/-!
 # Some messy stuff

 This file contains some messy stuff that I don't want to put in the main file.

 Will organise this later.
-/


variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

open scoped TensorProduct BigOperators Kronecker Functional

local notation "ℍ" => Matrix n n ℂ

local notation "⊗K" => Matrix (n × n) (n × n) ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "L(" x ")" => x →L[ℂ] x

local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable {φ : Module.Dual ℂ ℍ} [hφ : Fact φ.IsFaithfulPosMap] {ψ : Module.Dual ℂ (Matrix p p ℂ)}
  (hψ : ψ.IsFaithfulPosMap)

open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ) :
    (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "υ⁻¹" =>
  ((TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ)).symm :
    Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ)

local notation "ϰ" =>
  (↑(TensorProduct.comm ℂ (Matrix n n ℂ) ℂ) : Matrix n n ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "ϰ⁻¹" =>
  ((TensorProduct.comm ℂ (Matrix n n ℂ) ℂ).symm : ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] ℂ)

local notation "τ" => (TensorProduct.lid ℂ (Matrix n n ℂ) : ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

local notation "τ⁻¹" =>
  ((TensorProduct.lid ℂ (Matrix n n ℂ)).symm : Matrix n n ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

noncomputable def ιMap (hφ : φ.IsFaithfulPosMap) : l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍ :=
  letI := Fact.mk hφ
  { toFun := fun x => (id ⊗ₘ x) (m.adjoint 1)
    map_add' := fun x y =>
      by
      obtain ⟨α, β, h⟩ := TensorProduct.eq_span (m.adjoint (1 : ℍ))
      rw [← h]
      simp only [map_sum, TensorProduct.map_tmul, LinearMap.add_apply, TensorProduct.tmul_add,
        Finset.sum_add_distrib]
    map_smul' := fun r x => by
      simp_rw [RingHom.id_apply, TensorProduct.map_smul_right, LinearMap.smul_apply] }

theorem sig_neg_one (a : ℍ) : hφ.elim.sig (-1) a = φ.Matrix ⬝ a ⬝ φ.Matrix⁻¹ := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg, pos_def.rpow_one_eq_self,
    pos_def.rpow_neg_one_eq_inv_self]

theorem sig_one (a : ℍ) : hφ.elim.sig 1 a = φ.Matrix⁻¹ ⬝ a ⬝ φ.Matrix := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, pos_def.rpow_one_eq_self,
    pos_def.rpow_neg_one_eq_inv_self]

theorem ιMap_apply_rankOne (a b : ℍ) : ιMap hφ.elim |a⟩⟨b| = hφ.elim.sig (-1) bᴴ ⊗ₜ[ℂ] a :=
  by
  simp_rw [ιMap, LinearMap.coe_mk, LinearMap.mul'_adjoint, one_apply, boole_mul, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, SMulHomClass.map_smul,
    TensorProduct.map_tmul, LinearMap.one_apply, ContinuousLinearMap.coe_coe, rankOne_apply]
  have : ∀ i j, inner b (std_basis_matrix i j 1) = (φ.matrix ⬝ bᴴ) j i :=
    by
    intro i j
    rw [← inner_conj_symm, inner_stdBasisMatrix_left, starRingEnd_apply, ← star_apply,
      star_eq_conj_transpose, conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.Eq]
  simp_rw [this, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul', smul_smul,
    mul_comm _ ((_ ⬝ _) _ _), ← Finset.sum_smul, ← mul_apply, ← sig_neg_one,
    TensorProduct.smul_tmul', ← smul_std_basis_matrix', ← TensorProduct.sum_tmul]
  rw [← matrix_eq_sum_std_basis]

theorem ιMap_eq_psi : ιMap hφ.elim = (id ⊗ₘ unop) ∘ₗ tenSwap ∘ₗ (hφ.elim.psi 0 1).toLinearMap :=
  by
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [ιMap_apply_rankOne, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tenSwap_apply, TensorProduct.map_tmul,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, op_apply, unop_apply, MulOpposite.unop_op,
    Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.one_apply]

theorem ιMap_comp_inv :
    (ιMap hφ.elim ∘ₗ (hφ.elim.psi 0 1).symm.toLinearMap ∘ₗ (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ id ⊗ₘ op) =
      1 :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp_rw [ιMap_eq_psi, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, tenSwap_apply_tenSwap, ← LinearMap.comp_apply, ←
    TensorProduct.map_comp, unop_comp_op, LinearMap.one_comp, TensorProduct.map_one]

theorem ι_inv_comp_ιMap :
    ((hφ.elim.psi 0 1).symm.toLinearMap ∘ₗ (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ id ⊗ₘ op) ∘ₗ ιMap hφ.elim =
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
    conj_transpose_conj_transpose, Module.Dual.IsFaithfulPosMap.sig_apply_sig, neg_add_self,
    Module.Dual.IsFaithfulPosMap.sig_zero]

noncomputable def ιInvMap (hφ : φ.IsFaithfulPosMap) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] l(ℍ) :=
  ((hφ.psi 0 1).symm : ℍ ⊗[ℂ] ℍᵐᵒᵖ →ₗ[ℂ] l(ℍ)) ∘ₗ (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ id ⊗ₘ op

noncomputable def ιLinearEquiv (hφ : φ.IsFaithfulPosMap) : l(ℍ) ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ :=
  letI := Fact.mk hφ
  LinearEquiv.ofLinear (ιMap hφ) (ιInvMap hφ) ιMap_comp_inv ι_inv_comp_ιMap

private noncomputable def phi_map_aux (hφ : Fact φ.IsFaithfulPosMap) (x : l(ℍ)) : l(ℍ ⊗[ℂ] ℍ) :=
  (id ⊗ₘ m) ∘ₗ υ ∘ₗ ((id ⊗ₘ x) ⊗ₘ id) ∘ₗ m.adjoint ⊗ₘ id

private theorem phi_map_aux_add (hφ : Fact φ.IsFaithfulPosMap) (x y : l(ℍ)) :
    phiMapAux hφ (x + y) = phiMapAux hφ x + phiMapAux hφ y := by
  simp_rw [phi_map_aux, TensorProduct.map_add, TensorProduct.add_map, LinearMap.add_comp,
    LinearMap.comp_add]

private theorem phi_map_aux_smul (hφ : Fact φ.IsFaithfulPosMap) (x : ℂ) (y : l(ℍ)) :
    phiMapAux hφ (x • y) = x • phiMapAux hφ y :=
  by
  apply TensorProduct.ext'
  intro a b
  rw [phi_map_aux, LinearMap.comp_apply, TensorProduct.map_smul, TensorProduct.smul_map,
    LinearMap.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_apply,
    SMulHomClass.map_smul]
  rfl

noncomputable def phiMap (hφ : φ.IsFaithfulPosMap) : l(ℍ) →ₗ[ℂ] l(ℍ ⊗[ℂ] ℍ)
    where
  toFun x :=
    letI := Fact.mk hφ
    (id ⊗ₘ m) ∘ₗ υ ∘ₗ ((id ⊗ₘ x) ⊗ₘ id) ∘ₗ m.adjoint ⊗ₘ id
  map_add' x y := phiMapAux_add (Fact.mk hφ) x y
  map_smul' x y := phiMapAux_smul (Fact.mk hφ) x y

theorem Module.Dual.IsFaithfulPosMap.sig_isSymmetric {t : ℝ} :
    LinearMap.IsSymmetric (hφ.elim.sig t).toLinearMap :=
  by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, _root_.is_self_adjoint]
  exact Module.Dual.IsFaithfulPosMap.sig_adjoint

theorem ιInvMap_mul_adjoint_eq_rmul : ιInvMap hφ.elim ∘ₗ m.adjoint = rmul :=
  by
  simp_rw [LinearMap.ext_iff, ← Matrix.ext_iff]
  intro x a i j
  simp_rw [LinearMap.comp_apply, LinearMap.mul'_adjoint, map_sum, SMulHomClass.map_smul, ιInvMap,
    LinearMap.comp_apply, TensorProduct.map_tmul, tenSwap_apply, Module.Dual.IsFaithfulPosMap.psi,
    LinearEquiv.coe_coe, LinearEquiv.coe_symm_mk, Module.Dual.IsFaithfulPosMap.psiInvFun'_apply,
    unop_apply, op_apply, MulOpposite.unop_op, neg_zero, Module.Dual.IsFaithfulPosMap.sig_zero,
    LinearMap.one_apply, std_basis_matrix_conj_transpose, star_one, LinearMap.sum_apply,
    LinearMap.smul_apply, Matrix.sum_apply, Pi.smul_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, Pi.smul_apply, ← AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.sig_isSymmetric _ a, inner_stdBasisMatrix_left, smul_eq_mul,
    std_basis_matrix, mul_boole, mul_ite, MulZeroClass.mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← mul_apply, mul_comm (x _ _), ← mul_apply,
    AlgEquiv.toLinearMap_apply, ← Matrix.mul_assoc, ← sig_one, ←
    Module.Dual.IsFaithfulPosMap.sig_symm_eq, AlgEquiv.apply_symm_apply]
  rfl

theorem psi_inv_0_0_mul_adjoint_eq_lmul :
    ((hφ.elim.psi 0 0).symm : ℍ ⊗[ℂ] ℍᵐᵒᵖ →ₗ[ℂ] l(ℍ)) ∘ₗ (id ⊗ₘ op) ∘ₗ m.adjoint = lmul :=
  by
  simp_rw [LinearMap.ext_iff, ← Matrix.ext_iff]
  intro x a i j
  simp_rw [LinearMap.comp_apply, LinearMap.mul'_adjoint, map_sum, SMulHomClass.map_smul,
    TensorProduct.map_tmul, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_coe,
    LinearEquiv.coe_symm_mk, Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, unop_op, neg_zero,
    Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.one_apply, std_basis_matrix_conj_transpose,
    star_one, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_apply, Pi.smul_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, Pi.smul_apply, inner_stdBasisMatrix_left,
    smul_eq_mul, std_basis_matrix, mul_boole, mul_ite, MulZeroClass.mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  letI := hφ.elim.matrix_is_pos_def.invertible
  simp_rw [mul_comm (x _ _), mul_assoc, ← Finset.mul_sum, ← mul_apply, mul_comm _ ((_ ⬝ _) _ _), ←
    mul_apply, Matrix.mul_assoc, mul_inv_of_invertible, Matrix.mul_one]
  rfl

theorem tenSwap_psi_eq_psi_real {t s : ℝ} :
    tenSwap ∘ₗ (hφ.elim.psi t s : l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍᵐᵒᵖ) =
      (hφ.elim.psi s t : l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍᵐᵒᵖ).Real :=
  by
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [LinearMap.real_eq, LinearMap.star_eq_adjoint, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    rankOneLm_eq_rankOne, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tenSwap_apply, TensorProduct.star_tmul, star,
    op_apply, MulOpposite.unop_op, conj_transpose_conj_transpose]

theorem rankOne_map_rankOne_eq [hφ : Fact φ.IsFaithfulPosMap] (x y z w : ℍ) :
    ((|x⟩⟨y| : l(ℍ)) ⊗ₘ (|z⟩⟨w| : l(ℍ))) = |x ⊗ₜ[ℂ] z⟩⟨y ⊗ₜ[ℂ] w| :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  simp_rw [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, rankOne_apply,
    TensorProduct.inner_tmul, TensorProduct.smul_tmul_smul]

theorem phiMap_eq : phiMap hφ.elim = (rmulMapLmul : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] l(ℍ ⊗[ℂ] ℍ)) ∘ₗ ιMap hφ.elim :=
  by
  apply LinearMap.ext_of_rank_one'
  intro x y
  rw [TensorProduct.ext_iff]
  intro a b
  rw [TensorProduct.inner_ext_iff']
  intro c d
  simp_rw [phiMap, LinearMap.coe_mk, LinearMap.comp_apply, TensorProduct.map_tmul]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (m.adjoint a)
  rw [← h]
  simp_rw [map_sum, TensorProduct.sum_tmul, map_sum, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    TensorProduct.assoc_tmul, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    LinearMap.one_apply, rankOne_apply, LinearMap.mul'_apply, sum_inner, smul_mul_assoc,
    TensorProduct.tmul_smul, inner_smul_left, inner_conj_symm, TensorProduct.inner_tmul, ←
    mul_assoc, mul_comm (inner (β _) _ : ℂ), ← Finset.sum_mul, ← TensorProduct.inner_tmul, ←
    sum_inner, h, LinearMap.adjoint_inner_left, LinearMap.mul'_apply, mul_eq_mul]
  rw [Module.Dual.IsFaithfulPosMap.inner_left_conj _ _ y, ← TensorProduct.inner_tmul]
  revert c d
  rw [← TensorProduct.inner_ext_iff', ιMap_apply_rankOne, rmulMapLmul_apply]
  simp only [TensorProduct.map_tmul, rmul_apply, lmul_apply, sig_neg_one, mul_eq_mul]

noncomputable def grad (hφ : φ.IsFaithfulPosMap) : l(ℍ) →+ ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ :=
  letI := Fact.mk hφ
  { toFun := fun x => ((x.adjoint ⊗ₘ id) - id ⊗ₘ x) ∘ₗ m.adjoint
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

private theorem grad_apply_rank_one (x y : ℍ) :
    grad hφ.elim |x⟩⟨y| =
      phiMap hφ.elim (|x⟩⟨y| : l(ℍ)).Real ∘ₗ tensorOneMap - phiMap hφ.elim |x⟩⟨y| ∘ₗ oneTensorMap :=
  by
  rw [LinearMap.ext_iff]
  intro a
  rw [TensorProduct.inner_ext_iff']
  intro c d
  simp_rw [LinearMap.sub_apply, inner_sub_left, LinearMap.comp_apply, oneTensorMap_apply,
    tensorOneMap_apply, rankOne_real_apply, grad, AddMonoidHom.coe_mk, LinearMap.sub_comp,
    LinearMap.sub_apply, inner_sub_left, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    LinearMap.comp_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (m.adjoint a)
  rw [← h]
  simp_rw [map_sum, sum_inner, TensorProduct.map_tmul, rankOneLm_eq_rankOne, phiMap_eq,
    LinearMap.comp_apply, ιMap_apply_rankOne, rmulMapLmul_apply, TensorProduct.map_tmul,
    TensorProduct.inner_tmul, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
    inner_conj_symm, LinearMap.one_apply, mul_comm (inner (α _) _ : ℂ), mul_assoc, ← Finset.mul_sum,
    ← TensorProduct.inner_tmul, ← sum_inner, h, sum_inner, TensorProduct.inner_tmul,
    mul_comm _ (inner (α _) _ : ℂ), ← mul_assoc, mul_comm _ (inner (α _) _ : ℂ), ← Finset.sum_mul, ←
    TensorProduct.inner_tmul, ← sum_inner, h, TensorProduct.inner_tmul,
    LinearMap.adjoint_inner_left, LinearMap.mul'_apply,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, conj_transpose_conj_transpose, neg_neg,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, neg_add_self, Module.Dual.IsFaithfulPosMap.sig_zero,
    rmul_apply, lmul_apply, one_mul, mul_one, mul_eq_mul, ←
    Module.Dual.IsFaithfulPosMap.inner_right_hMul, sig_neg_one, ←
    Module.Dual.IsFaithfulPosMap.inner_left_conj]

theorem grad_apply (x : l(ℍ)) :
    grad hφ.elim x = phiMap hφ.elim x.Real ∘ₗ tensorOneMap - phiMap hφ.elim x ∘ₗ oneTensorMap :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  rw [map_sum, LinearMap.real_sum]
  simp_rw [map_sum, LinearMap.sum_comp, ← Finset.sum_sub_distrib, grad_apply_rank_one]

theorem oneTensorMap_adjoint [hφ : Fact φ.IsFaithfulPosMap] :
    (oneTensorMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ).adjoint = τ ∘ₗ ϰ ∘ₗ id ⊗ₘ η.adjoint := by
  simp_rw [oneTensorMap, LinearMap.adjoint_comp, ← LinearEquiv.toLinearMap_eq_coe,
    TensorProduct.lid_symm_adjoint, TensorProduct.comm_symm_adjoint, TensorProduct.map_adjoint,
    LinearMap.adjoint_one, Nontracial.unit_adjoint_eq, LinearEquiv.toLinearMap_eq_coe,
    LinearMap.comp_assoc]

theorem oneTensorMap_adjoint_apply [hφ : Fact φ.IsFaithfulPosMap] (x y : ℍ) :
    (oneTensorMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ).adjoint (x ⊗ₜ[ℂ] y) = φ y • x := by
  simp_rw [oneTensorMap_adjoint, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.lid_tmul, LinearMap.one_apply,
    Nontracial.unit_adjoint_eq]

theorem tensorOneMap_adjoint [hφ : Fact φ.IsFaithfulPosMap] :
    (tensorOneMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ).adjoint = τ ∘ₗ η.adjoint ⊗ₘ id := by
  simp_rw [tensorOneMap, LinearMap.adjoint_comp, ← LinearEquiv.toLinearMap_eq_coe,
    TensorProduct.lid_symm_adjoint, TensorProduct.map_adjoint, LinearMap.adjoint_one,
    Nontracial.unit_adjoint_eq, LinearEquiv.toLinearMap_eq_coe]

theorem tensorOneMap_adjoint_apply [hφ : Fact φ.IsFaithfulPosMap] (x y : ℍ) :
    (tensorOneMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ).adjoint (x ⊗ₜ y) = φ x • y := by
  simp_rw [tensorOneMap_adjoint, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, LinearMap.one_apply, Nontracial.unit_adjoint_eq]

private theorem phi_map_adjoint_rank_one (x y : ℍ) :
    (phiMap hφ.elim |x⟩⟨y|).adjoint = phiMap hφ.elim (|x⟩⟨y| : l(ℍ)).Real := by
  simp_rw [phiMap_eq, rankOne_real_apply, LinearMap.comp_apply, ιMap_apply_rankOne,
    rmulMapLmul_apply, TensorProduct.map_adjoint, rmul_eq_mul, lmul_eq_mul,
    LinearMap.Matrix.mulLeft_adjoint, ← LinearMap.Matrix.mulRight_adjoint]

theorem phiMap_adjoint (x : l(ℍ)) : (phiMap hφ.elim x).adjoint = phiMap hφ.elim x.Real :=
  by
  obtain ⟨α, β, h⟩ := x.exists_sum_rank_one
  rw [h]
  simp_rw [LinearMap.real_sum, map_sum, phi_map_adjoint_rank_one]

private theorem grad_adjoint_rank_one (x y : ℍ) :
    (grad hφ.elim |x⟩⟨y| : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ).adjoint =
      τ ∘ₗ (η.adjoint ⊗ₘ id) ∘ₗ phiMap hφ.elim |x⟩⟨y| -
        τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ η.adjoint) ∘ₗ phiMap hφ.elim (|x⟩⟨y| : l(ℍ)).Real :=
  by
  simp_rw [grad_apply_rank_one, map_sub, LinearMap.adjoint_comp, tensorOneMap_adjoint,
    oneTensorMap_adjoint, ← phi_map_adjoint_rank_one, LinearMap.adjoint_adjoint,
    LinearMap.comp_assoc]

theorem grad_adjoint (x : l(ℍ)) :
    (grad hφ.elim x).adjoint =
      τ ∘ₗ (η.adjoint ⊗ₘ id) ∘ₗ phiMap hφ.elim x -
        τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ η.adjoint) ∘ₗ phiMap hφ.elim x.Real :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  rw [LinearMap.real_sum]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.sum_comp, LinearMap.comp_sum,
    grad_adjoint_rank_one, Finset.sum_sub_distrib]

theorem sig_map_hMul (t : ℝ) (x y : ℍ) :
    hφ.elim.sig t (x ⬝ y) = hφ.elim.sig t x ⬝ hφ.elim.sig t y := by
  simp only [← mul_eq_mul, _root_.map_mul]

private theorem phi_map_mul_rank_one (x y z w : ℍ) :
    phiMap hφ.elim (Qam.reflIdempotent hφ.elim |x⟩⟨y| |z⟩⟨w|) =
      phiMap hφ.elim |x⟩⟨y| ∘ₗ phiMap hφ.elim |z⟩⟨w| :=
  by
  simp_rw [Qam.RankOne.reflIdempotent_eq, phiMap_eq, LinearMap.comp_apply, ιMap_apply_rankOne,
    rmulMapLmul_apply, ← TensorProduct.map_comp, lmul_eq_mul, rmul_eq_mul, ← LinearMap.mulRight_mul,
    ← LinearMap.mulLeft_mul, mul_eq_mul, ← sig_map_hMul, ← conj_transpose_mul]

theorem phiMap_mul (A B : l(ℍ)) :
    phiMap hφ.elim (Qam.reflIdempotent hφ.elim A B) = phiMap hφ.elim A ∘ₗ phiMap hφ.elim B :=
  by
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one
  obtain ⟨γ, ζ, rfl⟩ := B.exists_sum_rank_one
  -- rw [linear_map.eq_rank_one_of_faithful_pos_map hφ A,
  --   B.eq_rank_one_of_faithful_pos_map hφ],
  simp_rw [map_sum, LinearMap.sum_apply, map_sum, phi_map_mul_rank_one, ← LinearMap.sum_comp, ←
    LinearMap.comp_sum]

theorem phiMap_of_real_Schur_idempotent {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ.elim x x = x) :
    (phiMap hφ.elim x).adjoint = phiMap hφ.elim x ∧ IsIdempotentElem (phiMap hφ.elim x) := by
  simp_rw [IsIdempotentElem, phiMap_adjoint, LinearMap.mul_eq_comp, ← phiMap_mul,
    (LinearMap.isReal_iff _).mp hx1, hx2, and_self_iff]

@[instance]
private def hmm {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (U : Submodule ℂ H) : CompleteSpace U :=
  FiniteDimensional.complete ℂ U

def phiMap_of_real_Schur_idempotent_orthogonal_projection {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ.elim x x = x) :
    ∃ U : Submodule ℂ (ℍ ⊗[ℂ] ℍ), (orthogonalProjection' U : l(ℍ ⊗[ℂ] ℍ)) = phiMap hφ.elim x :=
  by
  rw [orthogonal_projection_iff_lm, _root_.is_self_adjoint, LinearMap.star_eq_adjoint]
  simp_rw [phiMap_of_real_Schur_idempotent hx1 hx2, and_true_iff]

noncomputable def phiMap_of_real_Schur_idempotent.submodule {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ.elim x x = x) : Submodule ℂ (ℍ ⊗[ℂ] ℍ) := by
  choose U hU using phiMap_of_real_Schur_idempotent_orthogonal_projection hx1 hx2 <;> exact U

def phiMap_of_real_Schur_idempotent.orthogonal_projection_eq {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ.elim x x = x) :
    (orthogonalProjection' (phiMap_of_real_Schur_idempotent.submodule hx1 hx2) : l(ℍ ⊗[ℂ] ℍ)) =
      phiMap hφ.elim x :=
  phiMap_of_real_Schur_idempotent.Submodule._proof_11 hx1 hx2

theorem grad_apply_of_real_Schur_idempotent {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ.elim x x = x) :
    phiMap hφ.elim x ∘ₗ grad hφ.elim x = grad hφ.elim x := by
  simp_rw [grad_apply, (LinearMap.isReal_iff _).mp hx1, ← LinearMap.comp_sub, ←
    LinearMap.comp_assoc, ← phiMap_mul, hx2]

theorem grad_of_real_Schur_idempotent_range {x : l(ℍ)} (hx1 : x.IsReal)
    (hx2 : Qam.reflIdempotent hφ.elim x x = x) :
    (grad hφ.elim x).range ≤ phiMap_of_real_Schur_idempotent.submodule hx1 hx2 :=
  by
  rw [← grad_apply_of_real_Schur_idempotent hx1 hx2, ←
    phiMap_of_real_Schur_idempotent.orthogonal_projection_eq hx1 hx2]
  nth_rw 1 [← orthogonalProjection.range (phiMap_of_real_Schur_idempotent.submodule hx1 hx2)]
  rw [LinearMap.range_le_iff_comap]
  -- rw [range_le_iff_comap],
  apply Submodule.ext
  simp_rw [Submodule.mem_top, iff_true_iff, Submodule.mem_comap, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]
  intro a
  exact LinearMap.mem_range_self _ _

noncomputable def dIn : l(ℍ) →ₗ[ℂ] l(ℍ)
    where
  toFun x := m ∘ₗ (x ⊗ₘ id) ∘ₗ tensorOneMap
  map_add' x y := by simp only [TensorProduct.add_map, LinearMap.comp_add, LinearMap.add_comp]
  map_smul' r x := by
    simp only [TensorProduct.smul_map, LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply]

noncomputable def dOut (hφ : φ.IsFaithfulPosMap) : l(ℍ) →+ l(ℍ) :=
  letI := Fact.mk hφ
  { toFun := fun x => m ∘ₗ (id ⊗ₘ x.adjoint) ∘ₗ oneTensorMap
    map_add' := fun x y => by
      simp only [map_add, TensorProduct.map_add, LinearMap.comp_add, LinearMap.add_comp]
    map_zero' := by
      simp only [map_zero, TensorProduct.map_zero, LinearMap.zero_comp, LinearMap.comp_zero] }

theorem dIn_apply (x : l(ℍ)) : dIn x = lmul (x 1) :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [dIn, LinearMap.coe_mk, LinearMap.comp_apply, tensorOneMap_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, LinearMap.one_apply, lmul_apply]

theorem dOut_apply (x : l(ℍ)) : dOut hφ.elim x = rmul (x.adjoint 1) :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [dOut, AddMonoidHom.coe_mk, LinearMap.comp_apply, oneTensorMap_apply,
    TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.one_apply, rmul_apply]

theorem tensor_one_map_adjoint_comp_phiMap_comp_one_tensor_map_rankOne (x y : ℍ) :
    τ ∘ₗ (η.adjoint ⊗ₘ id) ∘ₗ phiMap hφ.elim |x⟩⟨y| ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ = |x⟩⟨y| :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.comm_symm_tmul, TensorProduct.map_tmul, LinearMap.one_apply,
    Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, phiMap_eq, LinearMap.comp_apply,
    ιMap_apply_rankOne, rmulMapLmul_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    lmul_apply, rmul_apply, Nontracial.unit_adjoint_eq]
  have := Module.Dual.IsFaithfulPosMap.hMul_left hφ.elim aᴴ y 1
  rw [Matrix.one_mul, Matrix.mul_one, ← sig_neg_one, conj_transpose_conj_transpose,
    conj_transpose_mul, conj_transpose_conj_transpose] at this
  simp only [LinearMap.one_apply, mul_one, mul_one, mul_eq_mul, ← this, one_smul, Matrix.mul_one]
  rw [ContinuousLinearMap.coe_coe, rankOne_apply, Module.Dual.IsFaithfulPosMap.inner_eq]

theorem tensor_one_map_adjoint_comp_phiMap_comp_one_tensor_map (x : l(ℍ)) :
    τ ∘ₗ (η.adjoint ⊗ₘ id) ∘ₗ phiMap hφ.elim x ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ = x :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.sum_apply,
    tensor_one_map_adjoint_comp_phiMap_comp_one_tensor_map_rankOne]

private theorem tensor_one_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one (x y : ℍ) :
    τ ∘ₗ (η.adjoint ⊗ₘ id) ∘ₗ phiMap hφ.elim |x⟩⟨y| ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ = dIn (|x⟩⟨y| : l(ℍ)) :=
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

theorem tensor_one_map_adjoint_comp_phiMap_comp_tensor_one_map (x : l(ℍ)) :
    τ ∘ₗ (η.adjoint ⊗ₘ id) ∘ₗ phiMap hφ.elim x ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ = dIn x :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.sum_apply,
    tensor_one_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one]

private theorem one_tensor_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one (x y : ℍ) :
    τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ η.adjoint) ∘ₗ phiMap hφ.elim |x⟩⟨y| ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ =
      (|x⟩⟨y| : l(ℍ)).Real.adjoint :=
  by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.map_tmul, LinearMap.one_apply, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, phiMap_eq, LinearMap.comp_apply, ιMap_apply_rankOne,
    rmulMapLmul_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul, TensorProduct.lid_tmul,
    lmul_apply, rmul_apply, Nontracial.unit_adjoint_eq, one_smul, one_mul, LinearMap.one_apply,
    rankOne_real_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint, rankOneLm_apply,
    Module.Dual.IsFaithfulPosMap.inner_eq, conj_transpose_conj_transpose, mul_eq_mul]

theorem one_tensor_map_adjoint_comp_phiMap_comp_tensor_one_map (x : l(ℍ)) :
    τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ η.adjoint) ∘ₗ phiMap hφ.elim x ∘ₗ (η ⊗ₘ id) ∘ₗ τ⁻¹ = x.Real.adjoint :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.sum_apply,
    one_tensor_map_adjoint_comp_phi_map_comp_tensor_one_map_rank_one, LinearMap.real_sum]

private theorem one_tensor_map_adjoint_comp_phi_map_comp_one_tensor_map_rank_one (x y : ℍ) :
    τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ η.adjoint) ∘ₗ phiMap hφ.elim |x⟩⟨y| ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ =
      dOut hφ.elim (|x⟩⟨y| : l(ℍ)).Real :=
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
    Module.Dual.IsFaithfulPosMap.inner_eq, Matrix.mul_one, conj_transpose_conj_transpose,
    mul_smul_comm]

theorem one_tensor_map_adjoint_comp_phiMap_comp_one_tensor_map (x : l(ℍ)) :
    τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ η.adjoint) ∘ₗ phiMap hφ.elim x ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ =
      dOut hφ.elim x.Real :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  simp only [dOut_apply, map_sum, LinearMap.real_sum, map_sum]
  simp_rw [← dOut_apply]
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.sum_apply,
    one_tensor_map_adjoint_comp_phi_map_comp_one_tensor_map_rank_one, LinearMap.real_sum]

private theorem qam.refl_idempotent_real_rank_one (a b c d : ℍ) :
    (Qam.reflIdempotent hφ.elim |a⟩⟨b| |c⟩⟨d|).Real =
      Qam.reflIdempotent hφ.elim (|c⟩⟨d| : l(ℍ)).Real (|a⟩⟨b| : l(ℍ)).Real :=
  by
  simp only [Qam.RankOne.reflIdempotent_eq, rankOne_real_apply, ← sig_map_hMul, ←
    conj_transpose_mul]

theorem Qam.reflIdempotent_real (a b : l(ℍ)) :
    (Qam.reflIdempotent hφ.elim a b).Real = Qam.reflIdempotent hφ.elim b.Real a.Real :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one
  obtain ⟨γ, ζ, rfl⟩ := b.exists_sum_rank_one
  simp only [map_sum, LinearMap.real_sum, LinearMap.sum_apply, qam.refl_idempotent_real_rank_one]
  rw [Finset.sum_comm]

theorem Qam.reflIdempotent_adjoint (a b : l(ℍ)) :
    (Qam.reflIdempotent hφ.elim a b).adjoint = Qam.reflIdempotent hφ.elim a.adjoint b.adjoint :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one
  obtain ⟨γ, ζ, rfl⟩ := b.exists_sum_rank_one
  simp_rw [map_sum, LinearMap.sum_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    rankOneLm_eq_rankOne, Qam.RankOne.reflIdempotent_eq, map_sum, ← rankOneLm_eq_rankOne,
    rankOneLm_adjoint]

private theorem D_in_Schur_product_eq_ir_refl_rank_one (a b c d : ℍ) :
    dIn (Qam.reflIdempotent hφ.elim |a⟩⟨b| |c⟩⟨d|) =
      Qam.reflIdempotent hφ.elim ((|a⟩⟨b| : l(ℍ)) ∘ₗ (|c⟩⟨d| : l(ℍ)).Real.adjoint) id :=
  by
  simp_rw [dIn_apply, rankOne_real_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    rankOneLm_comp_rankOneLm, SMulHomClass.map_smul, LinearMap.smul_apply, rankOneLm_eq_rankOne]
  rw [Qam.RankOne.reflIdempotent_eq, Qam.reflexive_eq_rankOne, ContinuousLinearMap.coe_coe,
    rankOne_apply, Module.Dual.IsFaithfulPosMap.inner_right_conj, sig_neg_one,
    conj_transpose_conj_transpose, Matrix.one_mul, SMulHomClass.map_smul, lmul_eq_mul]

theorem dIn_Schur_product_eq_ir_refl (A B : l(ℍ)) :
    dIn (Qam.reflIdempotent hφ.elim A B) = Qam.reflIdempotent hφ.elim (A ∘ₗ B.Real.adjoint) id :=
  by
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one
  obtain ⟨α, β, rfl⟩ := B.exists_sum_rank_one
  simp only [map_sum, LinearMap.sum_apply, LinearMap.real_sum, LinearMap.comp_sum,
    LinearMap.sum_comp, D_in_Schur_product_eq_ir_refl_rank_one]

private theorem D_out_Schur_product_eq_ir_refl'_rank_one (a b c d : ℍ) :
    dOut hφ.elim (Qam.reflIdempotent hφ.elim |a⟩⟨b| |c⟩⟨d|) =
      Qam.reflIdempotent hφ.elim id ((|c⟩⟨d| : l(ℍ)).adjoint ∘ₗ (|a⟩⟨b| : l(ℍ)).Real) :=
  by
  simp_rw [dOut_apply, rankOne_real_apply, Qam.RankOne.reflIdempotent_eq, ← rankOneLm_eq_rankOne,
    rankOneLm_adjoint, rankOneLm_comp_rankOneLm, SMulHomClass.map_smul, rankOneLm_eq_rankOne,
    Qam.reflexive'_eq_rankOne, ContinuousLinearMap.coe_coe, rankOne_apply, SMulHomClass.map_smul,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, conj_transpose_conj_transpose,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, add_neg_self, Module.Dual.IsFaithfulPosMap.sig_zero,
    Module.Dual.IsFaithfulPosMap.inner_left_hMul, Matrix.mul_one]
  rfl

theorem dOut_Schur_product_eq_ir_refl' (A B : l(ℍ)) :
    dOut hφ.elim (Qam.reflIdempotent hφ.elim A B) =
      Qam.reflIdempotent hφ.elim id (B.adjoint ∘ₗ A.Real) :=
  by
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one
  obtain ⟨α, β, rfl⟩ := B.exists_sum_rank_one
  simp only [map_sum, LinearMap.sum_apply, LinearMap.real_sum, LinearMap.comp_sum,
    LinearMap.sum_comp, D_out_Schur_product_eq_ir_refl'_rank_one]
  rw [Finset.sum_comm]

theorem grad_adjoint_grad (x : l(ℍ)) :
    (grad hφ.elim x).adjoint ∘ₗ grad hφ.elim x =
      dIn (Qam.reflIdempotent hφ.elim x x.Real) - Qam.reflIdempotent hφ.elim x x -
          Qam.reflIdempotent hφ.elim x.adjoint x.adjoint +
        dOut hφ.elim (Qam.reflIdempotent hφ.elim x.Real x) :=
  by
  simp_rw [grad, AddMonoidHom.coe_mk, LinearMap.adjoint_comp, map_sub, LinearMap.adjoint_adjoint,
    TensorProduct.map_adjoint, LinearMap.adjoint_one, LinearMap.adjoint_adjoint]
  simp only [LinearMap.comp_sub, LinearMap.sub_comp]
  simp_rw [← LinearMap.comp_assoc, LinearMap.comp_assoc (_ ⊗ₘ _) (_ ⊗ₘ _), ← TensorProduct.map_comp,
    LinearMap.one_comp, LinearMap.comp_one, dIn_Schur_product_eq_ir_refl,
    dOut_Schur_product_eq_ir_refl', Qam.reflIdempotent, schurIdempotent, LinearMap.coe_mk,
    LinearMap.real_real, LinearMap.comp_assoc, sub_eq_add_neg, neg_add, neg_neg, add_assoc]

theorem ι_inv_grad_apply_rankOne (a b x : ℍ) :
    (ιInvMap hφ.elim) ((grad hφ.elim |a⟩⟨b|) x) =
      rmul x ∘ₗ (|a⟩⟨b| : l(ℍ)).Real - (|a⟩⟨b| : l(ℍ)) ∘ₗ rmul x :=
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
  simp_rw [conj_transpose_one, mul_one, one_mul, mul_eq_mul, conj_transpose_mul, sig_map_hMul,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, Module.Dual.IsFaithfulPosMap.sig_apply_sig,
    add_neg_self, Module.Dual.IsFaithfulPosMap.sig_zero, ← mul_eq_mul,
    conj_transpose_conj_transpose, ← @LinearMap.mulRight_apply ℂ _ _ _ _ _ _ _ b, ←
    LinearMap.Matrix.mulRight_adjoint, ← LinearMap.rankOne_comp]
  rfl

theorem ιInvMap_apply (x y : ℍ) : ιInvMap hφ.elim (x ⊗ₜ[ℂ] y) = |y⟩⟨hφ.elim.sig (-1) xᴴ| := by
  simp_rw [ιInvMap, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    tenSwap_apply, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_symm_mk,
    Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, op_apply, unop_apply, MulOpposite.unop_op,
    neg_zero, Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.one_apply]

theorem phiMap_eq' (x : l(ℍ)) :
    phiMap hφ.elim x = ιMap hφ.elim ∘ₗ Qam.reflIdempotent hφ.elim x ∘ₗ ιInvMap hφ.elim :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  simp_rw [map_sum, LinearMap.sum_comp, LinearMap.comp_sum]
  apply Finset.sum_congr rfl; intros
  rw [TensorProduct.ext_iff]
  intro a b
  simp_rw [phiMap_eq, LinearMap.comp_apply, ιInvMap_apply, ιMap_apply_rankOne, rmulMapLmul_apply,
    TensorProduct.map_tmul, Qam.RankOne.reflIdempotent_eq, ιMap_apply_rankOne, rmul_apply,
    lmul_apply, conj_transpose_mul, Module.Dual.IsFaithfulPosMap.sig_conjTranspose, sig_map_hMul,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, add_neg_self, Module.Dual.IsFaithfulPosMap.sig_zero,
    conj_transpose_conj_transpose]
  rfl

theorem phiMapMapsToBimoduleMaps {A : l(ℍ)} : (phiMap hφ.elim A).IsBimoduleMap :=
  by
  intro x y a
  obtain ⟨α, β, rfl⟩ := TensorProduct.eq_span a
  obtain ⟨γ, ζ, rfl⟩ := A.exists_sum_rank_one
  simp_rw [map_sum, LinearMap.sum_apply, Bimodule.lsmul_sum, Bimodule.sum_rsmul, phiMap_eq,
    LinearMap.comp_apply, ιMap_apply_rankOne, rmulMapLmul_apply, map_sum]
  simp only [Bimodule.rsmul_apply, Bimodule.lsmul_apply, TensorProduct.map_tmul, rmul_apply,
    lmul_apply, Matrix.mul_assoc]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem phiMap_range : (phiMap hφ.elim).range ≤ IsBimoduleMap.submodule :=
  by
  intro A
  simp_rw [LinearMap.mem_range]
  rintro ⟨y, rfl⟩
  exact phiMapMapsToBimoduleMaps

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_3 x_4) -/
theorem orthonormal_basis_tensorProduct_sum_repr (a b : ℍ) :
    ∑ (x_3 : n × n) (x_4 : n × n),
        ⟪(hφ.elim.Basis.TensorProduct hφ.elim.Basis) (x_3, x_4), a ⊗ₜ[ℂ] b⟫_ℂ •
          (hφ.elim.Basis.TensorProduct hφ.elim.Basis) (x_3, x_4) =
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
theorem LinearMap.tensor_matrix_eq_rankOne (x : l(ℍ ⊗[ℂ] ℍ)) :
    x =
      ∑ (i) (j) (k) (l),
        ⟪(Basis.tensorProduct hφ.elim.Basis hφ.elim.Basis) (i, j),
            x ((Basis.tensorProduct hφ.elim.Basis hφ.elim.Basis) (k, l))⟫_ℂ •
          |(Basis.tensorProduct hφ.elim.Basis hφ.elim.Basis)
              (i, j)⟩⟨(Basis.tensorProduct hφ.elim.Basis hφ.elim.Basis) (k, l)| :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  rw [TensorProduct.inner_ext_iff']
  intro c d
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_smul_left,
    ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left, inner_conj_symm]
  have :=
    calc
      ∑ (x_1 : n × n) (x_2 : n × n) (x_3 : n × n) (x_4 : n × n),
            ⟪x ((hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4)),
                  (hφ.elim.basis.tensor_product hφ.elim.basis) (x_1, x_2)⟫_ℂ *
                ⟪a ⊗ₜ[ℂ] b, (hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4)⟫_ℂ *
              ⟪(hφ.elim.basis.tensor_product hφ.elim.basis) (x_1, x_2), c ⊗ₜ[ℂ] d⟫_ℂ =
          ⟪x
              (∑ (x_3 : n × n) (x_4 : n × n),
                ⟪(hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4), a ⊗ₜ[ℂ] b⟫_ℂ •
                  (hφ.elim.basis.tensor_product hφ.elim.basis) (x_3, x_4)),
            ∑ (x_1 : n × n) (x_2 : n × n),
              ⟪(hφ.elim.basis.tensor_product hφ.elim.basis) (x_1, x_2), c ⊗ₜ[ℂ] d⟫_ℂ •
                (hφ.elim.basis.tensor_product hφ.elim.basis) (x_1, x_2)⟫_ℂ :=
        _
      _ = ⟪x (a ⊗ₜ b), c ⊗ₜ d⟫_ℂ := _
  · simp_rw [← this, mul_assoc]
  · simp_rw [map_sum, inner_sum, sum_inner, SMulHomClass.map_smul, inner_smul_left,
      inner_smul_right, inner_conj_symm]
    repeat' apply Finset.sum_congr rfl; intros
    simp only [← mul_assoc, mul_comm, mul_rotate]
    rw [mul_comm ⟪a ⊗ₜ b, _⟫_ℂ ⟪_, c ⊗ₜ d⟫_ℂ]
  · simp_rw [orthonormal_basis_tensorProduct_sum_repr]

noncomputable def phiInvMap (hφ : φ.IsFaithfulPosMap) :
    (IsBimoduleMap.submodule : Submodule ℂ l(ℍ ⊗[ℂ] ℍ)) →ₗ[ℂ] l(ℍ)
    where
  toFun x := ιInvMap hφ ((x : l(ℍ ⊗[ℂ] ℍ)) 1)
  map_add' x y := by simp_rw [Submodule.coe_add, LinearMap.add_apply, map_add]
  map_smul' r x := by
    simp only [Submodule.coe_smul, LinearMap.smul_apply, SMulHomClass.map_smul, RingHom.id_apply]

noncomputable def phiInv'Map (hφ : φ.IsFaithfulPosMap) : l(ℍ ⊗[ℂ] ℍ) →ₗ[ℂ] l(ℍ) :=
  letI := Fact.mk hφ
  { toFun := fun x => τ ∘ₗ (η.adjoint ⊗ₘ id) ∘ₗ (x : l(ℍ ⊗[ℂ] ℍ)) ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹
    map_add' := fun x y => by simp only [Submodule.coe_add, LinearMap.add_comp, LinearMap.comp_add]
    map_smul' := fun r x => by
      simp only [Submodule.coe_smul, LinearMap.comp_smul, LinearMap.smul_comp,
        SMulHomClass.map_smul, RingHom.id_apply] }

noncomputable def phiInv'MapCoe (hφ : φ.IsFaithfulPosMap) :
    (IsBimoduleMap.submodule : Submodule ℂ l(ℍ ⊗[ℂ] ℍ)) →ₗ[ℂ] l(ℍ) :=
  letI := Fact.mk hφ
  { toFun := fun x => phiInv'Map hφ x
    map_add' := fun x y => by
      simp only [phiInv'Map, LinearMap.coe_mk, Submodule.coe_add, LinearMap.add_comp,
        LinearMap.comp_add]
    map_smul' := fun r x => by
      simp only [phiInv'Map, LinearMap.coe_mk, Submodule.coe_smul, LinearMap.comp_smul,
        LinearMap.smul_comp, SMulHomClass.map_smul, RingHom.id_apply] }

theorem phiInv'Map_apply (x y : l(ℍ)) :
    phiInv'Map hφ.elim (x ⊗ₘ y) = y ∘ₗ (|(1 : ℍ)⟩⟨(1 : ℍ)| : l(ℍ)) ∘ₗ x :=
  by
  simp_rw [LinearMap.ext_iff]
  intro a
  simp_rw [phiInv'Map, LinearMap.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.lid_symm_apply, TensorProduct.comm_symm_tmul, TensorProduct.map_tmul,
    TensorProduct.lid_tmul, ContinuousLinearMap.coe_coe, LinearMap.one_apply,
    Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, Nontracial.unit_adjoint_eq,
    rankOne_apply, Module.Dual.IsFaithfulPosMap.inner_eq, conj_transpose_one, one_smul,
    Matrix.one_mul, SMulHomClass.map_smul]

theorem ιLinearEquiv_apply_eq (x : l(ℍ)) : ιLinearEquiv hφ.elim x = ιMap hφ.elim x :=
  rfl

theorem ιLinearEquiv_symm_apply_eq (x : ℍ ⊗[ℂ] ℍ) :
    (ιLinearEquiv hφ.elim).symm x = ιInvMap hφ.elim x :=
  rfl

private noncomputable def phi_map_coe_aux (hφ : Fact φ.IsFaithfulPosMap) (x : l(ℍ)) :
    (IsBimoduleMap.submodule : Submodule ℂ l(ℍ ⊗[ℂ] ℍ)) :=
  ⟨phiMap hφ.elim x, phiMapMapsToBimoduleMaps⟩

private theorem phi_map_coe_aux_add (hφ : Fact φ.IsFaithfulPosMap) (x y : l(ℍ)) :
    phiMapCoeAux hφ (x + y) = phiMapCoeAux hφ x + phiMapCoeAux hφ y :=
  by
  simp only [phi_map_coe_aux, map_add]
  ext1
  simp only [LinearMap.add_apply, Submodule.coe_add, Subtype.coe_mk]

private theorem phi_map_coe_aux_smul (hφ : Fact φ.IsFaithfulPosMap) (r : ℂ) (x : l(ℍ)) :
    phiMapCoeAux hφ (r • x) = r • phiMapCoeAux hφ x :=
  by
  simp only [phi_map_coe_aux, SMulHomClass.map_smul]
  ext1
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Subtype.coe_mk]

noncomputable def phiMapCoe (hφ : φ.IsFaithfulPosMap) :
    l(ℍ) →ₗ[ℂ] (IsBimoduleMap.submodule : Submodule ℂ l(ℍ ⊗[ℂ] ℍ))
    where
  toFun x :=
    letI := Fact.mk hφ
    ⟨phiMap hφ x, phiMapMapsToBimoduleMaps⟩
  map_add' := phiMapCoeAux_add (Fact.mk hφ)
  map_smul' := phiMapCoeAux_smul (Fact.mk hφ)

theorem phi_map_left_inverse : phiInvMap hφ.elim ∘ₗ phiMapCoe hφ.elim = 1 :=
  by
  apply LinearMap.ext_of_rank_one'
  intro x y
  simp_rw [LinearMap.one_apply, LinearMap.comp_apply, phiMapCoe, LinearMap.coe_mk, phiMap_eq',
    phiInvMap, LinearMap.coe_mk, Subtype.coe_mk]
  simp_rw [LinearMap.comp_apply]
  simp_rw [← ιLinearEquiv_apply_eq, ← ιLinearEquiv_symm_apply_eq, LinearEquiv.symm_apply_apply]
  have : (ιLinearEquiv hφ.elim).symm 1 = Qam.completeGraph ℍ :=
    by
    simp_rw [ιLinearEquiv_symm_apply_eq, Algebra.TensorProduct.one_def, ιInvMap_apply,
      conj_transpose_one, _root_.map_one]
    rfl
  rw [this, Qam.reflIdempotent, Qam.refl_idempotent_completeGraph_right]

theorem phi_inv'_map_phi_map : phiInv'MapCoe hφ.elim ∘ₗ phiMapCoe hφ.elim = 1 :=
  by
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [phiInv'MapCoe, phiMapCoe, LinearMap.comp_apply, LinearMap.coe_mk, phiMap_eq,
    LinearMap.comp_apply, ιMap_apply_rankOne, rmulMapLmul_apply, Subtype.coe_mk, phiInv'Map_apply,
    rmul_eq_mul, ← LinearMap.Matrix.mulRight_adjoint, LinearMap.rankOne_comp',
    LinearMap.comp_rankOne, lmul_apply, LinearMap.mulRight_apply, mul_one, one_mul,
    LinearMap.one_apply]

theorem phi_map_right_inverse (x : { x : l(ℍ ⊗[ℂ] ℍ) // x.IsBimoduleMap }) :
    phiMapCoe hφ.elim (phiInvMap hφ.elim x) = x :=
  by
  simp_rw [phiInvMap, LinearMap.coe_mk, phiMapCoe, LinearMap.coe_mk, phiMap_eq,
    LinearMap.comp_apply, ← ιLinearEquiv_apply_eq, ← ιLinearEquiv_symm_apply_eq,
    LinearEquiv.apply_symm_apply, Subtype.ext_iff, TensorProduct.ext_iff, Subtype.coe_mk]
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
    map_add' := fun x y => by simp only [map_add, Subtype.coe_eta] <;> rfl
    map_smul' := fun r x => by simp only [SMulHomClass.map_smul, RingHom.id_apply] }

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

theorem phi_inv'_map_eq_phi_inv'_map : phiInvMap hφ.elim = phiInv'MapCoe hφ.elim := by
  simp_rw [LinearEquiv.comp_inj (phiLinearEquiv hφ.elim), phiLinearEquiv, LinearMap.ext_iff,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_mk, ← LinearMap.comp_apply,
    phi_map_left_inverse, phi_inv'_map_phi_map, eq_self_iff_true, forall₂_true_iff]

theorem sig_apply_sig_inv {t : ℝ} {x : ℍ} : hφ.elim.sig t (hφ.elim.sig (-t) x) = x := by
  rw [sig_eq_iff_eq_sig_inv]

theorem sig_inv_apply_sig {t : ℝ} {x : ℍ} : hφ.elim.sig (-t) (hφ.elim.sig t x) = x :=
  by
  symm
  rw [← sig_eq_iff_eq_sig_inv]

theorem rsmul_module_map_of_real_lsmul_module_map {n : Type _} [Fintype n] {f : l(Matrix n n ℂ)}
    (hf : ∀ a x : Matrix n n ℂ, f (a ⬝ x) = a ⬝ f x) (a x : Matrix n n ℂ) :
    f.Real (a ⬝ x) = f.Real a ⬝ x := by
  simp_rw [LinearMap.real_eq, star_eq_conj_transpose, conj_transpose_mul, hf, conj_transpose_mul,
    conj_transpose_conj_transpose]

theorem lsmul_module_map_iff_symm_eq_rsmul_module_map [hφ : Fact φ.IsFaithfulPosMap] {f : l(ℍ)} :
    f = rmul (f 1) ↔ LinearEquiv.symmMap ℂ ℍ f = lmul (f 1) :=
  by
  rw [← LinearEquiv.eq_symm_apply, LinearEquiv.symmMap_symm_apply,
    @lmul_adjoint _ _ _ _ _ _ _ φ fun x y => by
      simp only [star_eq_conj_transpose, mul_eq_mul] <;>
        exact Module.Dual.IsFaithfulPosMap.inner_eq x y,
    lmul_eq_mul, LinearMap.mulLeft_real, star_star, rmul_eq_mul]
  simp only [iff_self_iff]

theorem LinearMap.real_adjoint_eq (f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    f.Real.adjoint =
      (hφ.elim.sig (-1)).toLinearMap ∘ₗ f.adjoint.Real ∘ₗ (hφ.elim.sig 1).toLinearMap :=
  by
  rw [LinearMap.adjoint_real_eq]
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, sig_inv_apply_sig,
    eq_self_iff_true, forall_true_iff]

theorem left_hand_twist_eq_sig_one :
    τ ∘ₗ
        ((η.adjoint ∘ₗ m) ⊗ₘ id) ∘ₗ
          υ⁻¹ ∘ₗ
            (id ⊗ₘ
                ((TensorProduct.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ)) ∘ₗ
              υ ∘ₗ (m.adjoint ⊗ₘ id) ∘ₗ (tensorOneMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) =
      (hφ.elim.sig 1).toLinearMap :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp only [LinearMap.comp_apply, tensorOneMap_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply, LinearMap.mul'_adjoint, one_apply, boole_mul, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, LinearMap.one_apply]
  simp only [TensorProduct.sum_tmul, map_sum, ← TensorProduct.smul_tmul', SMulHomClass.map_smul,
    TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    TensorProduct.assoc_symm_tmul, TensorProduct.lid_tmul, LinearMap.comp_apply,
    LinearMap.mul'_apply, LinearMap.one_apply, Nontracial.unit_adjoint_eq]
  have : ∀ i j : n, φ (std_basis_matrix i j 1 ⬝ x) = (x ⬝ φ.matrix) j i :=
    by
    intro i j
    rw [← star_one ℂ, ← std_basis_matrix_conj_transpose, ← Module.Dual.IsFaithfulPosMap.inner_eq,
      inner_stdBasisMatrix_left]
  rw [Finset.sum_rotate]
  simp only [mul_eq_mul, this, smul_smul, ← Finset.sum_smul, ← mul_apply]
  simp_rw [← smul_std_basis_matrix']
  rw [← matrix_eq_sum_std_basis (φ.matrix⁻¹ ⬝ (x ⬝ _)), sig_one, Matrix.mul_assoc]

theorem right_hand_twist_eq_sig_neg_one :
    τ ∘ₗ
        ϰ ∘ₗ
          (id ⊗ₘ η.adjoint ∘ₗ m) ∘ₗ
            υ ∘ₗ
              (((TensorProduct.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) ⊗ₘ
                  id) ∘ₗ
                υ⁻¹ ∘ₗ (id ⊗ₘ m.adjoint) ∘ₗ (oneTensorMap : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) =
      (hφ.elim.sig (-1)).toLinearMap :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp only [LinearMap.comp_apply, oneTensorMap_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply, LinearMap.mul'_adjoint, one_apply, boole_mul, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, LinearMap.one_apply]
  simp only [TensorProduct.tmul_sum, map_sum, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul',
    SMulHomClass.map_smul, TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.lid_tmul,
    LinearMap.comp_apply, LinearMap.mul'_apply, LinearMap.one_apply, Nontracial.unit_adjoint_eq]
  have : ∀ i j : n, φ (x ⬝ std_basis_matrix i j 1) = (φ.matrix ⬝ x) j i :=
    by
    intro i j
    rw [← conj_transpose_conj_transpose x, ← Module.Dual.IsFaithfulPosMap.inner_eq, ←
      inner_conj_symm, inner_stdBasisMatrix_left, starRingEnd_apply, ← star_apply,
      star_eq_conj_transpose, conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.Eq]
  simp only [mul_eq_mul, this, smul_smul, ← Finset.sum_smul, ← mul_apply]
  simp_rw [← smul_std_basis_matrix', mul_comm, ← mul_apply]
  rw [← matrix_eq_sum_std_basis (φ.matrix ⬝ x ⬝ _), sig_neg_one]

theorem balance_symm_1 :
    (η.adjoint ∘ₗ m ∘ₗ (hφ.elim.sig 1).toLinearMap ⊗ₘ id) =
      η.adjoint ∘ₗ m ∘ₗ id ⊗ₘ (hφ.elim.sig (-1)).toLinearMap :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Nontracial.unit_adjoint_eq, LinearMap.one_apply, AlgEquiv.toLinearMap_apply]
  nth_rw 1 [← linear_functional_apply_sig (-1)]
  rw [_root_.map_mul (hφ.elim.sig (-1)) _ b, sig_inv_apply_sig]

theorem balance_symm_2 :
    (η.adjoint ∘ₗ m ∘ₗ id ⊗ₘ (hφ.elim.sig (-1)).toLinearMap) =
      η.adjoint ∘ₗ
        m ∘ₗ ((TensorProduct.comm ℂ ℍ ℍ : ℍ ⊗[ℂ] ℍ ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍ) : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Nontracial.unit_adjoint_eq, TensorProduct.comm_tmul, LinearMap.one_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply]
  calc
    φ (a ⬝ hφ.elim.sig (-1) b) = ⟪aᴴ, hφ.elim.sig (-1) b⟫_ℂ := by
      rw [Module.Dual.IsFaithfulPosMap.inner_eq, conj_transpose_conj_transpose]
    _ = ⟪bᴴ, a⟫_ℂ := by
      rw [Nontracial.inner_symm, Module.Dual.IsFaithfulPosMap.sig_conjTranspose, sig_apply_sig_inv,
        conj_transpose_conj_transpose]
    _ = φ (b ⬝ a) := by rw [Module.Dual.IsFaithfulPosMap.inner_eq, conj_transpose_conj_transpose]

