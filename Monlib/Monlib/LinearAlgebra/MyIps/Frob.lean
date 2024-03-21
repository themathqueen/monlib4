/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyIps.TensorHilbert
import LinearAlgebra.MyIps.Nontracial
import LinearAlgebra.DirectSumFromTo
import LinearAlgebra.PiDirectSum

#align_import linear_algebra.my_ips.frob

/-!
 # Frobenius equations

 This file contains the proof of the Frobenius equations.
-/


variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} (hφ : φ.IsFaithfulPosMap) {ψ : Module.Dual ℂ (Matrix p p ℂ)}
  (hψ : ψ.IsFaithfulPosMap) {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {θ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hθ : ∀ i, Fact (θ i).IsFaithfulPosMap]

open scoped Matrix Kronecker TensorProduct BigOperators Functional

open Matrix

-- def linear_map.is_faithful_pos_map.tensor_pow (x : ℕ) :
--   ⨂[ℂ]^x (matrix n n ℂ) →ₗ[ℂ] ℂ :=
-- { to_fun := λ a, by { simp only [tensor_algebra] } }
noncomputable def Module.Dual.tensorMul {n p : Type _} (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) : Module.Dual ℂ (Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) :=
  (TensorProduct.lid ℂ ℂ : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) ∘ₗ TensorProduct.map φ₁ φ₂

theorem Module.Dual.tensorMul_apply (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (x : Matrix n n ℂ) (y : Matrix p p ℂ) :
    (φ₁.tensorMul φ₂) (x ⊗ₜ[ℂ] y) = φ₁ x * φ₂ y :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem Module.Dual.tensorMul_apply' (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (x : Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) :
    φ₁.tensorMul φ₂ x =
      ∑ (i) (j) (k) (l),
        x.toKronecker (i, k) (j, l) *
          (φ₁ (stdBasisMatrix i j (1 : ℂ)) * φ₂ (stdBasisMatrix k l (1 : ℂ))) :=
  by
  simp_rw [← Module.Dual.tensorMul_apply, ← smul_eq_mul, ← SMulHomClass.map_smul, ← map_sum]
  rw [← x.matrix_eq_sum_std_basis]

theorem Module.Dual.tensorMul_apply'' (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (a : Matrix (n × p) (n × p) ℂ) :
    ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct) a = (φ₁.Matrix ⊗ₖ φ₂.Matrix ⬝ a).trace :=
  by
  have :
    (φ₁.matrix ⊗ₖ φ₂.matrix ⬝ a).trace =
      ((trace_linear_map _ ℂ ℂ).comp (LinearMap.mulLeft ℂ (φ₁.matrix ⊗ₖ φ₂.matrix))) a :=
    rfl
  simp_rw [this]
  clear this
  revert a
  rw [← LinearMap.ext_iff, kronecker_product.ext_iff]
  intro x y
  simp_rw [LinearMap.comp_apply, kronecker_to_tensor_product_apply, Module.Dual.tensorMul_apply,
    LinearMap.mulLeft_apply, trace_linear_map_apply, mul_eq_mul, ← mul_kronecker_mul,
    trace_kronecker, Module.Dual.apply]

theorem Module.Dual.tensorMul_matrix (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) :
    Module.Dual.matrix ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct) = φ₁.Matrix ⊗ₖ φ₂.Matrix :=
  by
  symm
  apply Module.Dual.apply_eq_of
  simp_rw [← Module.Dual.tensorMul_apply'' φ₁ φ₂]
  intros
  rfl

@[instance]
def Module.Dual.IsFaithfulPosMap.tensorMul {φ₁ : Module.Dual ℂ (Matrix n n ℂ)}
    {φ₂ : Module.Dual ℂ (Matrix p p ℂ)} [hφ₁ : Fact φ₁.IsFaithfulPosMap]
    [hφ₂ : Fact φ₂.IsFaithfulPosMap] :
    Fact (Module.Dual.IsFaithfulPosMap ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct)) :=
  by
  apply Fact.mk
  rw [Module.Dual.isFaithfulPosMap_iff_of_matrix, Module.Dual.tensorMul_matrix]
  exact pos_def.kronecker hφ₁.elim.matrix_is_pos_def hφ₂.elim.matrix_is_pos_def

theorem Matrix.kroneckerToTensorProduct_adjoint [hφ : Fact φ.IsFaithfulPosMap]
    [hψ :
      Fact
        ψ.IsFaithfulPosMap] :-- = @linear_map.adjoint ℂ (matrix (n × p) (n × p) ℂ) (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) _
      --   (nacg_th hφ hψ) (nacg_tt hφ hψ) (ips_th hφ hψ) (ips_tt hφ hψ) _ _
      (@TensorProduct.toKronecker ℂ n p _ _ _ _ _ :
        Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix (n × p) (n × p) ℂ) =
      (kroneckerToTensorProduct :
          Matrix (n × p) (n × p) ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ).adjoint :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  apply @ext_inner_left ℂ _ _
  intro a
  rw [TensorProduct.toKronecker_apply, LinearMap.adjoint_inner_right, kmul_representation a]
  simp_rw [map_sum, SMulHomClass.map_smul, sum_inner, inner_smul_left]
  repeat'
    apply Finset.sum_congr rfl
    intros
  symm
  calc
    (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          inner (std_basis_matrix x_1 x_2 1 ⊗ₖ std_basis_matrix x_3 x_4 1).kroneckerToTensorProduct
            (x ⊗ₜ[ℂ] y) =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          inner (std_basis_matrix x_1 x_2 1 ⊗ₜ[ℂ] std_basis_matrix x_3 x_4 1) (x ⊗ₜ[ℂ] y) :=
      by rw [kronecker_to_tensor_product_apply]
    _ =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (inner (std_basis_matrix x_1 x_2 1) x * inner (std_basis_matrix x_3 x_4 1) y) :=
      by rw [TensorProduct.inner_tmul]
    _ =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          inner (std_basis_matrix x_1 x_2 1 ⊗ₖ std_basis_matrix x_3 x_4 1) (x ⊗ₖ y) :=
      by
      rw [Module.Dual.IsFaithfulPosMap.inner_eq' (_ ⊗ₖ _), Module.Dual.tensorMul_matrix,
          kronecker_conj_transpose, ← mul_kronecker_mul, ← mul_kronecker_mul, trace_kronecker,
          Module.Dual.IsFaithfulPosMap.inner_eq', Module.Dual.IsFaithfulPosMap.inner_eq'] <;>
        rfl

theorem TensorProduct.toKronecker_adjoint [hφ : Fact φ.IsFaithfulPosMap]
    [hψ : Fact ψ.IsFaithfulPosMap] :
    (kroneckerToTensorProduct : Matrix (n × p) (n × p) ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) =
      (@TensorProduct.toKronecker ℂ n p _ _ _ _ _ :
          Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix (n × p) (n × p) ℂ).adjoint :=
  by rw [@Matrix.kroneckerToTensorProduct_adjoint n p _ _ _ _ φ ψ, LinearMap.adjoint_adjoint]

theorem Matrix.kroneckerToTensorProduct_comp_toKronecker :
    (kroneckerToTensorProduct : Matrix (n × p) (n × p) ℂ →ₗ[ℂ] _).comp
        (TensorProduct.toKronecker : Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] _) =
      1 :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp_rw [LinearMap.comp_apply, TensorProduct.toKronecker_to_tensorProduct, LinearMap.one_apply]

local notation "ℍ" => Matrix n n ℂ

local notation "ℍ₂" => ∀ i, Matrix (s i) (s i) ℂ

local notation "ℍ_" i => Matrix (s i) (s i) ℂ

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

theorem frobenius_equation [hφ : Fact φ.IsFaithfulPosMap] :
    ((LinearMap.mul' ℂ ℍ ⊗ₘ id) ∘ₗ υ⁻¹ ∘ₗ id ⊗ₘ (LinearMap.mul' ℂ ℍ).adjoint) =
      (LinearMap.mul' ℂ ℍ).adjoint ∘ₗ LinearMap.mul' ℂ ℍ :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp_rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_adjoint,
    TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, SMulHomClass.map_smul,
    LinearMap.one_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul]
  simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.one_apply]
  -- kronecker_to_tensor_product_apply, linear_equiv.coe_to_linear_map,
  -- tensor_product.assoc_symm_tmul, linear_map.mul'_apply, linear_equiv.coe_coe],
  rw [←
    Function.Injective.eq_iff
      (kroneckerToTensor : Matrix (n × n) (n × n) ℂ ≃ₐ[ℂ] ℍ ⊗[ℂ] ℍ).symm.Injective]
  simp_rw [map_sum, SMulHomClass.map_smul, kroneckerToTensor, AlgEquiv.symm_symm, tensorToKronecker,
    AlgEquiv.coe_mk, TensorProduct.toKronecker_apply, ← Matrix.ext_iff, Matrix.sum_apply,
    Pi.smul_apply, kronecker_map, of_apply, mul_eq_mul, mul_apply, std_basis_matrix, mul_boole,
    smul_ite, smul_zero, ite_and, Finset.smul_sum, smul_ite, smul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp_rw [smul_eq_mul, mul_one, ← mul_apply, mul_rotate _ _ (x _ _), mul_assoc, ← Finset.mul_sum, ←
    mul_apply, mul_comm _ ((x ⬝ y) _ _), eq_self_iff_true, forall₂_true_iff]

local notation "l(" x ")" => x →ₗ[ℂ] x

open scoped BigOperators

noncomputable def matrixDirectSumFromTo
    (i j : k) :-- {k : Type*} [decidable_eq k] {s : k → Type*}
        -- [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
        -- (i j : k) :
        Matrix
        (s i) (s i) ℂ →ₗ[ℂ]
      Matrix (s j) (s j) ℂ :=
  @directSumFromTo ℂ _ k _ (fun a => Matrix (s a) (s a) ℂ) _ (fun a => Matrix.module) i j

theorem matrixDirectSumFromTo_same (i : k) :
    (matrixDirectSumFromTo i i : Matrix (s i) (s i) ℂ →ₗ[ℂ] _) = 1 :=
  directSumFromTo_apply_same _

theorem LinearMap.pi_mul'_apply_include_block' {i j : k} :
    LinearMap.mul' ℂ ℍ₂ ∘ₗ
        TensorProduct.map (includeBlock : (ℍ_ i) →ₗ[ℂ] ℍ₂) (includeBlock : (ℍ_ j) →ₗ[ℂ] ℍ₂) =
      if i = j then
        (includeBlock : (ℍ_ j) →ₗ[ℂ] ℍ₂) ∘ₗ
          LinearMap.mul' ℂ (ℍ_ j) ∘ₗ
            TensorProduct.map (matrixDirectSumFromTo i j) (1 : (ℍ_ j) →ₗ[ℂ] ℍ_ j)
      else 0 :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  ext1 a
  simp only [LinearMap.comp_apply, dite_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    include_block_mul_same, Finset.sum_apply, include_block_apply, Finset.sum_dite_eq',
    Finset.mem_univ, if_true, Pi.mul_apply, dite_hMul, hMul_dite, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, ite_apply_lm, LinearMap.zero_apply, ite_apply, Pi.zero_apply,
    LinearMap.one_apply]
  by_cases j = a
  · simp_rw [matrixDirectSumFromTo, directSumFromTo, LinearMap.comp_apply]
    simp [Pi.single, Function.update, h]
    split_ifs <;> finish
  · simp [h]

noncomputable def directSumTensorMatrix :
    ((∀ i, Matrix (s i) (s i) ℂ) ⊗[ℂ] ∀ i, Matrix (s i) (s i) ℂ) ≃ₗ[ℂ]
      ∀ i : k × k, (ℍ_ i.1) ⊗[ℂ] ℍ_ i.2 :=
  @directSumTensor ℂ _ k k _ _ _ _ (fun i => Matrix (s i) (s i) ℂ) (fun i => Matrix (s i) (s i) ℂ) _
    _ (fun i => Matrix.module) fun i => Matrix.module

noncomputable def directSumTensorToKronecker :
    ℍ₂ ⊗[ℂ] ℍ₂ ≃ₗ[ℂ] ∀ i : k × k, Matrix (s i.fst × s i.snd) (s i.fst × s i.snd) ℂ
    where
  toFun x i := (directSumTensorMatrix x i).toKronecker
  invFun x := directSumTensorMatrix.symm fun i => (x i).kroneckerToTensorProduct
  left_inv x := by
    simp only [TensorProduct.toKronecker_to_tensorProduct, LinearEquiv.symm_apply_apply]
  right_inv x := by
    simp only [LinearEquiv.apply_symm_apply, kronecker_to_tensor_product_to_kronecker]
  map_add' x y := by simp only [map_add, Pi.add_apply]; rfl
  map_smul' r x :=
    by
    simp only [SMulHomClass.map_smul, Pi.smul_apply, RingHom.id_apply]
    rfl

theorem frobenius_equation_direct_sum_aux [hθ : ∀ i, Fact (θ i).IsFaithfulPosMap] (x y : ℍ₂)
    (i j : k) :
    ((LinearMap.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂))) ∘ₗ
          ↑(TensorProduct.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm ∘ₗ
            (1 : l(ℍ₂)) ⊗ₘ ((LinearMap.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂))
        (includeBlock (x i) ⊗ₜ[ℂ] includeBlock (y j)) =
      if i = j then
        ((includeBlock ⊗ₘ includeBlock) ∘ₗ
            (LinearMap.mul' ℂ (ℍ_ j)).adjoint ∘ₗ LinearMap.mul' ℂ (ℍ_ j))
          (x j ⊗ₜ[ℂ] y j)
      else 0 :=
  by
  have :=
    calc
      ((LinearMap.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂))) ∘ₗ
              ↑(TensorProduct.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm ∘ₗ
                (1 : l(ℍ₂)) ⊗ₘ ((LinearMap.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂))
            (include_block (x i) ⊗ₜ[ℂ] include_block (y j)) =
          (LinearMap.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂)))
            ((TensorProduct.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
              ((include_block ⊗ₘ include_block ⊗ₘ include_block)
                (x i ⊗ₜ[ℂ] (LinearMap.mul' ℂ (ℍ_ j)).adjoint (y j)))) :=
        _
      _ =
          (LinearMap.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂)))
            (((include_block ⊗ₘ include_block) ⊗ₘ include_block)
              ((TensorProduct.assoc ℂ (ℍ_ i) (ℍ_ j) (ℍ_ j)).symm
                (x i ⊗ₜ[ℂ] (LinearMap.mul' ℂ (ℍ_ j)).adjoint (y j)))) :=
        _
      _ =
          if i = j then
            (((include_block : (ℍ_ j) →ₗ[ℂ] ℍ₂) ⊗ₘ include_block) ∘ₗ
                (LinearMap.mul' ℂ (ℍ_ j) ⊗ₘ (1 : l(ℍ_ j))) ∘ₗ
                  ↑(TensorProduct.assoc ℂ (ℍ_ j) (ℍ_ j) (ℍ_ j)).symm ∘ₗ
                    (1 : l(ℍ_ j)) ⊗ₘ (LinearMap.mul' ℂ (ℍ_ j)).adjoint)
              (x j ⊗ₜ[ℂ] y j)
          else 0 :=
        _
  · simp only [this, @frobenius_equation (s j)]
  ·
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
      LinearMap.one_apply, LinearMap.pi_mul'_adjoint_single_block]
  · congr
    simp_rw [← LinearEquiv.coe_coe, ← LinearMap.comp_apply, TensorProduct.assoc_includeBlock]
  · simp_rw [← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.pi_mul'_apply_include_block', LinearMap.comp_apply, TensorProduct.ite_map,
      ite_apply_lm, TensorProduct.zero_map, LinearMap.zero_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, LinearMap.one_apply]
    obtain ⟨α, β, hαβ⟩ := TensorProduct.eq_span ((LinearMap.mul' ℂ (ℍ_ j)).adjoint (y j))
    rw [← hαβ]
    simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.assoc_symm_tmul,
      TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.one_apply]
    split_ifs
    · apply Finset.sum_congr rfl
      intros
      rw [h, matrixDirectSumFromTo, directSumFromTo_apply_same, LinearMap.one_apply]
    · rfl

theorem directSumTensorToKronecker_apply (x y : ℍ₂) (r : k × k) (a b : s r.1 × s r.2) :
    (directSumTensorToKronecker (x ⊗ₜ[ℂ] y)) r a b = x r.1 a.1 b.1 * y r.2 a.2 b.2 := by
  simp_rw [directSumTensorToKronecker, LinearEquiv.coe_mk, directSumTensorMatrix,
    directSumTensor_apply, TensorProduct.toKronecker_apply, kronecker_map, of_apply]

-- lemma pi_frobenius_equation [hθ : Π i, fact (θ i).is_faithful_pos_map] :
--   ((linear_map.mul' ℂ ℍ₂  ⊗ₘ (1 : l(ℍ₂)))
--     ∘ₗ ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
--       ∘ₗ ((1 : l(ℍ₂)) ⊗ₘ ((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] (ℍ₂ ⊗[ℂ] ℍ₂))))
--     = (((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂) ∘ₗ (linear_map.mul' ℂ ℍ₂ : ℍ₂ ⊗[ℂ] ℍ₂ →ₗ[ℂ] ℍ₂)) :=
-- begin
--   apply tensor_product.ext',
--   intros x y,
--   rw [← sum_include_block x, ← sum_include_block y],
--   calc
--   ((linear_map.mul' ℂ ℍ₂ ⊗ₘ (1 : l(ℍ₂)))
--     ∘ₗ ↑(tensor_product.assoc ℂ ℍ₂ ℍ₂ ℍ₂).symm
--       ∘ₗ ((1 : l(ℍ₂)) ⊗ₘ ((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] (ℍ₂ ⊗[ℂ] ℍ₂))))
--         ((∑ i, include_block (x i)) ⊗ₜ[ℂ] (∑ j, include_block (y j)))
--   =
--   ∑ i j, if (i = j) then (
--       ((include_block ⊗ₘ include_block) ∘ₗ
--         ((linear_map.mul' ℂ (ℍ_ j)).adjoint ∘ₗ (linear_map.mul' ℂ (ℍ_ j))))
--         ((x j) ⊗ₜ[ℂ] (y j))) else 0 :
--   by { simp_rw [tensor_product.sum_tmul, tensor_product.tmul_sum, map_sum],
--     repeat { apply finset.sum_congr rfl, intros },
--     rw [frobenius_equation_direct_sum_aux], }
--   ... =
--   ∑ j, ((include_block ⊗ₘ include_block)
--       ((linear_map.mul' ℂ (ℍ_ j)).adjoint
--       ((linear_map.mul' ℂ (ℍ_ j))
--       ((x j) ⊗ₜ[ℂ] (y j))))) :
--   by { simp_rw [finset.sum_ite_eq, finset.mem_univ, if_true,
--     linear_map.comp_apply], }
--   ... =
--   ∑ j, (((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂)
--     ∘ₗ (include_block ∘ₗ (linear_map.mul' ℂ (ℍ_ j))))
--       ((x j) ⊗ₜ[ℂ] (y j)) :
--   by { simp_rw [linear_map.comp_apply, linear_map.pi_mul'_adjoint_single_block], }
--   ... =
--   ∑ i j, ite (i = j)
--   ((((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂) ∘ₗ
--   (include_block.comp ((linear_map.mul' ℂ (matrix (s j) (s j) ℂ)).comp (matrix_direct_sum_from_to i j ⊗ₘ 1))))
--      (x i ⊗ₜ[ℂ] y j)
--   )
--    0 :
--   by { simp_rw [finset.sum_ite_eq, finset.mem_univ, if_true,
--     matrix_direct_sum_from_to_same, tensor_product.map_one, linear_map.comp_one], }
--   ... =
--   ∑ j, (((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂)
--     ((linear_map.mul' ℂ ℍ₂ : ℍ₂ ⊗[ℂ] ℍ₂ →ₗ[ℂ] ℍ₂)
--      (include_block (x j) ⊗ₜ[ℂ] include_block (y j)))) :
--   by { simp_rw [← linear_map.pi_mul'_apply_include_block'], }
--   ... =
--   (((linear_map.mul' ℂ ℍ₂).adjoint : ℍ₂ →ₗ[ℂ] ℍ₂ ⊗[ℂ] ℍ₂) ∘ₗ (linear_map.mul' ℂ ℍ₂ : ℍ₂ ⊗[ℂ] ℍ₂ →ₗ[ℂ] ℍ₂))
--   ((∑ i, include_block (x i)) ⊗ₜ[ℂ] (∑ j, include_block (y j))) :
--   by {  },
-- end
theorem frobenius_equation' [hφ : Fact φ.IsFaithfulPosMap] :
    ((id ⊗ₘ LinearMap.mul' ℂ ℍ) ∘ₗ υ ∘ₗ (LinearMap.mul' ℂ ℍ).adjoint ⊗ₘ id) =
      (LinearMap.mul' ℂ ℍ).adjoint ∘ₗ LinearMap.mul' ℂ ℍ :=
  by
  have := @frobenius_equation n _ _ φ _
  apply_fun LinearMap.adjoint at this
  simp_rw [LinearMap.adjoint_comp, TensorProduct.map_adjoint, LinearMap.adjoint_adjoint,
    TensorProduct.assoc_symm_adjoint, ← LinearMap.star_eq_adjoint, star_one,
    LinearMap.comp_assoc] at this
  exact this

theorem LinearMap.mul'_assoc :
    (LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ LinearMap.mul' ℂ (Matrix n n ℂ) ⊗ₘ id) =
      LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ
        (id ⊗ₘ LinearMap.mul' ℂ (Matrix n n ℂ)) ∘ₗ
          (↑(TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ) : _ ≃ₗ[ℂ] _) :
            _ →ₗ[ℂ] _) :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    LinearMap.one_apply, LinearEquiv.coe_coe, TensorProduct.assoc_tmul, mul_assoc]

theorem LinearMap.mul'_coassoc [hφ : Fact φ.IsFaithfulPosMap] :
    ((LinearMap.mul' ℂ ℍ).adjoint ⊗ₘ id) ∘ₗ (LinearMap.mul' ℂ ℍ).adjoint =
      υ⁻¹ ∘ₗ (id ⊗ₘ (LinearMap.mul' ℂ ℍ).adjoint) ∘ₗ (LinearMap.mul' ℂ ℍ).adjoint :=
  by
  have := @LinearMap.mul'_assoc n _ _
  apply_fun LinearMap.adjoint at this
  simp_rw [LinearMap.adjoint_comp, TensorProduct.map_adjoint, TensorProduct.assoc_adjoint, ←
    LinearMap.star_eq_adjoint, star_one, LinearMap.comp_assoc] at this
  exact this

--  m(η ⊗ id) = τ
theorem LinearMap.mul'_comp_unit_map_id_eq_lid : (LinearMap.mul' ℂ ℍ ∘ₗ η ⊗ₘ id) = τ :=
  by
  rw [TensorProduct.ext_iff]
  intro α x
  simp_rw [LinearMap.comp_apply, TensorProduct.map_tmul, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.mul'_apply, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, LinearMap.one_apply, smul_mul_assoc, one_mul]

-- m(id ⊗ η)κ⁻¹ = τ
theorem LinearMap.mul'_comp_id_map_unit_assoc_eq_lid : LinearMap.mul' ℂ ℍ ∘ₗ (id ⊗ₘ η) ∘ₗ ϰ⁻¹ = τ :=
  by
  rw [TensorProduct.ext_iff]
  intro α x
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_symm_tmul,
    TensorProduct.map_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
    LinearMap.one_apply, LinearMap.mul'_apply, TensorProduct.lid_tmul, mul_smul_one]

private theorem linear_map.id_map_mul'_comp_unit_eq [hφ : Fact φ.IsFaithfulPosMap] :
    (id ⊗ₘ (LinearMap.mul' ℂ ℍ).adjoint ∘ₗ η) = (id ⊗ₘ (LinearMap.mul' ℂ ℍ).adjoint) ∘ₗ id ⊗ₘ η :=
  by rw [← TensorProduct.map_comp, LinearMap.comp_one]

-- (m ⊗ id)υ⁻¹(id ⊗ m⋆η)κ⁻¹τ⁻¹ = m⋆
theorem LinearMap.mul'_adjoint_eq' [hφ : Fact φ.IsFaithfulPosMap] :
    (LinearMap.mul' ℂ ℍ ⊗ₘ id) ∘ₗ υ⁻¹ ∘ₗ (id ⊗ₘ (LinearMap.mul' ℂ ℍ).adjoint ∘ₗ η) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹ =
      (LinearMap.mul' ℂ ℍ).adjoint :=
  by
  rw [linear_map.id_map_mul'_comp_unit_eq]
  have := @frobenius_equation n _ _ φ _
  simp_rw [← LinearMap.comp_assoc] at this ⊢
  rw [this]
  simp_rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ ϰ⁻¹, ← LinearMap.comp_assoc _ (_ ∘ₗ ϰ⁻¹),
    LinearMap.mul'_comp_id_map_unit_assoc_eq_lid, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

private theorem linear_map.mul'_comp_unit_map_id_eq [hφ : Fact φ.IsFaithfulPosMap] :
    (((LinearMap.mul' ℂ ℍ).adjoint ∘ₗ η) ⊗ₘ id) = ((LinearMap.mul' ℂ ℍ).adjoint ⊗ₘ id) ∘ₗ η ⊗ₘ id :=
  by rw [← TensorProduct.map_comp, LinearMap.comp_one]

-- (id ⊗ m)υ(m∗η ⊗ id) τ⁻¹ = m⋆
theorem LinearMap.mul'_adjoint_eq'' [hφ : Fact φ.IsFaithfulPosMap] :
    (id ⊗ₘ LinearMap.mul' ℂ ℍ) ∘ₗ υ ∘ₗ (((LinearMap.mul' ℂ ℍ).adjoint ∘ₗ η) ⊗ₘ id) ∘ₗ τ⁻¹ =
      (LinearMap.mul' ℂ ℍ).adjoint :=
  by
  rw [linear_map.mul'_comp_unit_map_id_eq]
  have := @frobenius_equation' n _ _ φ _
  simp_rw [← LinearMap.comp_assoc] at this ⊢
  rw [this]
  simp_rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ (_ ⊗ₘ _),
    LinearMap.mul'_comp_unit_map_id_eq_lid, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

