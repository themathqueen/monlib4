/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Mul''
import Monlib.LinearAlgebra.MyMatrix.PosDefRpow
import Monlib.LinearAlgebra.InnerAut
import Monlib.LinearAlgebra.MyMatrix.Reshape
import Monlib.LinearAlgebra.ToMatrixOfEquiv
import Monlib.LinearAlgebra.MyIps.TensorHilbert
import Monlib.LinearAlgebra.MyIps.Functional
import Monlib.LinearAlgebra.MyIps.MatIps
import Monlib.LinearAlgebra.MyIps.MulOp
import Monlib.LinearAlgebra.MyMatrix.IncludeBlock
import Monlib.LinearAlgebra.MyIps.OpUnop
import Monlib.LinearAlgebra.PiDirectSum
import Monlib.LinearAlgebra.tensorProduct

#align_import linear_algebra.my_ips.nontracial

/-!

# Some results on the Hilbert space on finite-dimensional C*-algebras

This file contains some results on the Hilbert space on finite-dimensional C*-algebras
  (so just a direct sum of matrix algebras over ℂ).

-/


variable {n : Type _} [Fintype n]

local notation "ℍ" => Matrix n n ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "L(" x ")" => x →L[ℂ] x

local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

open scoped Matrix

open Matrix

variable [DecidableEq n] {φ : Module.Dual ℂ (Matrix n n ℂ)}
  {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
  [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}

-- :TODO: make this a def:
-- local notation "PiMat k s" => Π i, Matrix (s i) (s i) ℂ

open scoped Kronecker Matrix BigOperators TensorProduct Functional

open Module.Dual

section SingleBlock

/-! # Section single_block -/


theorem inner_stdBasisMatrix_left [hφ : φ.IsFaithfulPosMap] (i j : n) (x : Matrix n n ℂ) :
    ⟪stdBasisMatrix i j (1 : ℂ), x⟫_ℂ = (x * φ.matrix) i j :=
  by
  simp only [IsFaithfulPosMap.inner_eq', stdBasisMatrix_conjTranspose, star_one]
  rw [Matrix.mul_assoc, ← trace_mul_cycle', Matrix.stdBasisMatrix_hMul_trace]

theorem inner_stdBasisMatrix_stdBasisMatrix [hφ : φ.IsFaithfulPosMap] (i j k l : n) :
    ⟪stdBasisMatrix i j (1 : ℂ), stdBasisMatrix k l (1 : ℂ)⟫_ℂ = ite (i = k) (φ.matrix l j) 0 :=
  by
  simp_rw [inner_stdBasisMatrix_left, mul_apply, stdBasisMatrix, boole_mul, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_ite_eq]
  simp_rw [@eq_comm _ (k : n) (i : n)]

-- set_option trace.Meta.synthInstance true
-- set_option pp.all true
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.isLevelDefEq true

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_5 x_6) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 350000 in
/-- we can expres the nontracial adjoint of `linear_map.mul'` by
  $$m^*(x) = \sum_{i,j,k,l} x_{il}Q^{-1}_{kj}(e_{ij} \otimes_t e_{kl})$$ -/
theorem LinearMap.mul'_adjoint [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
    LinearMap.adjoint (LinearMap.mul' ℂ ℍ) x =
      ∑ i : n, ∑ j : n, ∑ k : n, ∑ l : n,
        (x i l * φ.matrix⁻¹ k j) • stdBasisMatrix i j 1 ⊗ₜ[ℂ] stdBasisMatrix k l 1 :=
  by
  apply @ext_inner_left ℂ _ _
  intro v
  rw [LinearMap.adjoint_inner_right, v.matrix_eq_sum_std_basis]
  simp_rw [map_sum, SMulHomClass.map_smul, LinearMap.mul'_apply, sum_inner, inner_sum,
    stdBasisMatrix_hMul, inner_smul_left, inner_smul_right, starRingEnd_apply, star_ite, one_mul,
    star_one, star_zero, TensorProduct.inner_tmul, inner_stdBasisMatrix_stdBasisMatrix]
  simp only [boole_mul, mul_ite, ite_mul, zero_mul, mul_zero, one_mul, mul_one]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  simp only [inner_stdBasisMatrix_left, ← Finset.mul_sum]
  have :
    ∀ x_1 x_2 x_3 x_4 : n,
      ∑ x_5 : n, ∑ x_6 : n,
          x x_1 x_6 * φ.matrix⁻¹ x_3 x_5 * (φ.matrix x_5 x_2 * φ.matrix x_6 x_4) =
        (φ.matrix⁻¹ * φ.matrix) x_3 x_2 * (x * φ.matrix) x_1 x_4 :=
    by
    intro x_1 x_2 x_3 x_4
    calc ∑ x_5 : n, ∑ x_6 : n, x x_1 x_6 * φ.matrix⁻¹ x_3 x_5 * (φ.matrix x_5 x_2 * φ.matrix x_6 x_4)
        = (∑ x_5 : n, φ.matrix⁻¹ x_3 x_5 * φ.matrix x_5 x_2) * (∑ x_6 : n, x x_1 x_6 * φ.matrix x_6 x_4) :=
        by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          repeat'
            apply Finset.sum_congr rfl; intros
          rw [mul_comm (x x_1 _), mul_mul_mul_comm]
      _ = (φ.matrix⁻¹ * φ.matrix) x_3 x_2 * (x * φ.matrix) x_1 x_4 :=
        by simp_rw [← Matrix.mul_apply]
  haveI hm := hφ.matrixIsPosDef.invertible
  simp_rw [this, inv_mul_of_invertible, Matrix.one_apply, boole_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem Matrix.linearMap_ext_iff_inner_map [hφ : φ.IsFaithfulPosMap] {x y : l(ℍ)} :
    x = y ↔ ∀ u v : ℍ, ⟪x u, v⟫_ℂ = ⟪y u, v⟫_ℂ :=
  by
  simp_rw [LinearMap.ext_iff]
  refine' ⟨fun h u v => by rw [h], fun h a => _⟩
  apply @_root_.ext_inner_right ℂ _ _
  exact h _

theorem Matrix.linearMap_ext_iff_map_inner [hφ : φ.IsFaithfulPosMap] {x y : l(ℍ)} :
    x = y ↔ ∀ u v : ℍ, ⟪v, x u⟫_ℂ = ⟪v, y u⟫_ℂ :=
  by
  rw [@Matrix.linearMap_ext_iff_inner_map n _ _ φ]
  simp_rw [← inner_conj_symm _ (x _), ←
    inner_conj_symm (y _) _]
  exact
    ⟨fun h u v => by rw [h, starRingEnd_self_apply], fun h u v => by
      rw [← h, starRingEnd_self_apply]⟩

open scoped Matrix

theorem Matrix.inner_conj_Q [hφ : φ.IsFaithfulPosMap] (a x : ℍ) :
    ⟪x, φ.matrix * a * φ.matrix⁻¹⟫_ℂ = ⟪x * aᴴ, 1⟫_ℂ :=
  by
  simp_rw [IsFaithfulPosMap.inner_eq', ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp_rw [← Matrix.mul_assoc,
    @inv_mul_of_invertible n ℂ _ _ _ φ.matrix hφ.matrixIsPosDef.invertible, Matrix.one_mul,
    conjTranspose_mul, Matrix.mul_one, conjTranspose_conjTranspose]
  rw [← Matrix.trace_mul_cycle, Matrix.mul_assoc]

theorem Matrix.inner_star_right [hφ : φ.IsFaithfulPosMap] (b y : ℍ) :
    ⟪b, y⟫_ℂ = ⟪1, bᴴ * y⟫_ℂ := by
  simp_rw [IsFaithfulPosMap.inner_eq', ← Matrix.mul_assoc, conjTranspose_one, Matrix.mul_one]

theorem Matrix.inner_star_left [hφ : φ.IsFaithfulPosMap] (a x : ℍ) :
    ⟪a, x⟫_ℂ = ⟪xᴴ * a, 1⟫_ℂ := by
  rw [← inner_conj_symm, Matrix.inner_star_right, inner_conj_symm]

theorem one_inner [hφ : φ.IsFaithfulPosMap] (a : ℍ) : ⟪1, a⟫_ℂ = (φ.matrix * a).trace := by
  rw [IsFaithfulPosMap.inner_eq', conjTranspose_one, Matrix.mul_one]

theorem Module.Dual.IsFaithfulPosMap.map_star (hφ : φ.IsFaithfulPosMap) (x : ℍ) :
    φ (star x) = star (φ x) :=
  hφ.1.isReal x

theorem Nontracial.unit_adjoint_eq [hφ : φ.IsFaithfulPosMap] :
    LinearMap.adjoint (Algebra.linearMap ℂ ℍ : ℂ →ₗ[ℂ] ℍ) = φ := by
  rw [← @IsFaithfulPosMap.adjoint_eq n _ _ φ, LinearMap.adjoint_adjoint]

local notation "m" => LinearMap.mul' ℂ ℍ

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 350000 in
theorem Qam.Nontracial.mul_comp_mul_adjoint [hφ : φ.IsFaithfulPosMap] :
    LinearMap.mul' ℂ ℍ ∘ₗ LinearMap.adjoint (LinearMap.mul' ℂ ℍ) = trace (φ.matrix⁻¹) • 1 :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, ← Matrix.ext_iff, LinearMap.mul'_adjoint,
    map_sum, SMulHomClass.map_smul, LinearMap.mul'_apply,
    Matrix.sum_apply, LinearMap.smul_apply, Matrix.smul_apply,
    smul_eq_mul, LinearMap.one_apply, mul_apply, stdBasisMatrix,
    boole_mul, Finset.mul_sum, mul_ite, MulZeroClass.mul_zero, mul_one, ite_and]
  intro x i j
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp_rw [← Finset.mul_sum, ← trace_iff φ.matrix⁻¹, mul_comm]

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

theorem Module.Dual.IsFaithfulPosMap.inner_coord' [hφ : φ.IsFaithfulPosMap] (ij : n × n)
    (x : ℍ) : ⟪hφ.basis ij, x⟫_ℂ = (x * hφ.matrixIsPosDef.rpow (1 / 2)) ij.1 ij.2 := by
  rw [IsFaithfulPosMap.basis_apply, ← IsFaithfulPosMap.orthonormalBasis_apply,
    IsFaithfulPosMap.inner_coord _ ij x]

theorem rankOne_toMatrix [hφ : φ.IsFaithfulPosMap] (a b : Matrix n n ℂ) :
    hφ.toMatrix (|a⟩⟨b| : l(ℍ)) =
      col (reshape (a * hφ.matrixIsPosDef.rpow (1 / 2))) *
        (col (reshape (b * hφ.matrixIsPosDef.rpow (1 / 2))))ᴴ :=
  by
  -- letI := hφ.normed_add_comm_group,
  ext i j
  simp_rw [IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, SMulHomClass.map_smul, Finsupp.smul_apply,
    IsFaithfulPosMap.basis_repr_apply, ← inner_conj_symm b,
    Module.Dual.IsFaithfulPosMap.inner_coord', smul_eq_mul, mul_comm, conjTranspose_col, ←
    vecMulVec_eq, vecMulVec_apply, Pi.star_apply, reshape_apply, IsROrC.star_def]

noncomputable def Module.Dual.IsFaithfulPosMap.sig (hφ : φ.IsFaithfulPosMap) (z : ℝ) :
    Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ
    where
  toFun a := hφ.matrixIsPosDef.rpow (-z) * a * hφ.matrixIsPosDef.rpow z
  invFun a := hφ.matrixIsPosDef.rpow z * a * hφ.matrixIsPosDef.rpow (-z)
  left_inv a := by
    simp_rw [Matrix.mul_assoc, PosDef.rpow_mul_rpow, ← Matrix.mul_assoc, PosDef.rpow_mul_rpow,
      add_neg_self, PosDef.rpow_zero, Matrix.one_mul, Matrix.mul_one]
  right_inv a := by
    simp_rw [Matrix.mul_assoc, PosDef.rpow_mul_rpow, ← Matrix.mul_assoc, PosDef.rpow_mul_rpow,
      neg_add_self, PosDef.rpow_zero, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by simp_rw [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    simp_rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      PosDef.rpow_mul_rpow, neg_add_self, PosDef.rpow_zero]
  map_mul' a b := by
    simp_rw [Matrix.mul_assoc, ← Matrix.mul_assoc (hφ.matrixIsPosDef.rpow _),
      PosDef.rpow_mul_rpow, add_neg_self, PosDef.rpow_zero, Matrix.one_mul]

theorem Module.Dual.IsFaithfulPosMap.sig_apply (hφ : φ.IsFaithfulPosMap) (z : ℝ) (x : ℍ) :
    hφ.sig z x = hφ.matrixIsPosDef.rpow (-z) * x * hφ.matrixIsPosDef.rpow z :=
  rfl

theorem Module.Dual.IsFaithfulPosMap.sig_symm_apply (hφ : φ.IsFaithfulPosMap) (z : ℝ) (x : ℍ) :
    (hφ.sig z).symm x = hφ.matrixIsPosDef.rpow z * x * hφ.matrixIsPosDef.rpow (-z) :=
  rfl

theorem Module.Dual.IsFaithfulPosMap.sig_symm_eq (hφ : φ.IsFaithfulPosMap) (z : ℝ) :
    (hφ.sig z).symm = hφ.sig (-z) := by
  ext1
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply hφ,
    Module.Dual.IsFaithfulPosMap.sig_symm_apply hφ, neg_neg]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
noncomputable def Module.Dual.IsFaithfulPosMap.psiToFun' (hφ : φ.IsFaithfulPosMap) (t s : ℝ) :
    l(ℍ) →ₗ[ℂ] ℍ ⊗[ℂ] ℍᵐᵒᵖ
    where
  toFun x :=
    ∑ i, ∑ j, ∑ k, ∑ l,
      hφ.toMatrix x (i, j) (k, l) •
        hφ.sig t (hφ.basis (i, j)) ⊗ₜ (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.sig s (hφ.basis (k, l)))ᴴ
  map_add' x y := by simp_rw [map_add, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [SMulHomClass.map_smul, Matrix.smul_apply, smul_assoc, RingHom.id_apply, Finset.smul_sum]

theorem Module.Dual.IsFaithfulPosMap.sig_conjTranspose (hφ : φ.IsFaithfulPosMap) (t : ℝ) (x : ℍ) :
    (hφ.sig t x)ᴴ = hφ.sig (-t) xᴴ := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, conjTranspose_mul,
    (Matrix.PosDef.rpow.isHermitian _ _).eq, neg_neg, ← Matrix.mul_assoc]

theorem Module.Dual.IsFaithfulPosMap.psiToFun'_apply [hφ : φ.IsFaithfulPosMap] (t s : ℝ)
    (x y : ℍ) :
    hφ.psiToFun' t s |x⟩⟨y| = hφ.sig t x ⊗ₜ[ℂ] (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.sig s y)ᴴ :=
  by
  simp_rw [Module.Dual.IsFaithfulPosMap.psiToFun', LinearMap.coe_mk,
    AddHom.coe_mk, IsFaithfulPosMap.toMatrix,
    LinearMap.toMatrixAlgEquiv_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    SMulHomClass.map_smul, Finsupp.smul_apply, ← inner_conj_symm y, ←
    IsFaithfulPosMap.basis_repr_apply]
  simp_rw [← TensorProduct.tmul_smul, smul_eq_mul, mul_comm (starRingEnd ℂ _), ← smul_smul, ←
    TensorProduct.tmul_sum, ← Finset.smul_sum, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul,
    ← SMulHomClass.map_smul, starRingEnd_apply, ← conjTranspose_smul, ← SMulHomClass.map_smul, ←
    map_sum, ← conjTranspose_sum, ← map_sum, ← Finset.sum_product', Prod.mk.eta,
    Finset.univ_product_univ]
  simp only [IsFaithfulPosMap.basis_repr_apply, ← rankOne_apply, ← ContinuousLinearMap.sum_apply,
    IsFaithfulPosMap.basis_apply, ← IsFaithfulPosMap.orthonormalBasis_apply,
    rankOne.sum_orthonormalBasis_eq_id, ContinuousLinearMap.one_apply]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
set_option synthInstance.maxHeartbeats 30000 in
noncomputable def Module.Dual.IsFaithfulPosMap.psiInvFun' (hφ : φ.IsFaithfulPosMap) (t s : ℝ) :
  ℍ ⊗[ℂ] ℍᵐᵒᵖ →ₗ[ℂ] l(ℍ) :=
{ toFun := fun x =>
    ∑ i : n × n in Finset.univ ×ˢ Finset.univ, ∑ j : n × n in Finset.univ ×ˢ Finset.univ,
      ((hφ.basis.tensorProduct hφ.basis.mulOpposite).repr x) (i, j) •
        |hφ.sig (-t) (hφ.basis (i.1, i.2))⟩⟨hφ.sig (-s) (hφ.basis (j.1, j.2))ᴴ|
  map_add' := fun x y => by simp_rw [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := fun r x => by
    simp_rw [Finset.smul_sum, LinearEquiv.map_smul, RingHom.id_apply,
      Finsupp.smul_apply, smul_assoc] }

theorem Module.Dual.IsFaithfulPosMap.basis_op_repr_apply (hφ : φ.IsFaithfulPosMap) (x : ℍᵐᵒᵖ)
    (ij : n × n) :
    (hφ.basis.mulOpposite.repr x) ij =
      ((unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) x * hφ.matrixIsPosDef.rpow (1 / 2)) ij.1 ij.2 :=
  by
  rw [Basis.mulOpposite_repr_apply, unop, LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv_symm]
  letI := Fact.mk hφ
  rw [Module.Dual.IsFaithfulPosMap.basis_repr_apply]
  exact Module.Dual.IsFaithfulPosMap.inner_coord' _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Module.Dual.IsFaithfulPosMap.psiInvFun'_apply [hφ : φ.IsFaithfulPosMap] (t s : ℝ)
    (x : ℍ) (y : ℍᵐᵒᵖ) :
    (hφ.psiInvFun' t s : ℍ ⊗[ℂ] ℍᵐᵒᵖ →ₗ[ℂ] l(ℍ)) (x ⊗ₜ y) =
      |hφ.sig (-t) x⟩⟨hφ.sig (-s) ((unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) y)ᴴ| :=
  by
  let y' : Matrix n n ℂ := (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) y
  have : y = (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) y' := rfl
  simp_rw [this, Module.Dual.IsFaithfulPosMap.psiInvFun', LinearMap.coe_mk,
    AddHom.coe_mk, Basis.tensorProduct_repr_tmul_apply, Module.Dual.IsFaithfulPosMap.basis_op_repr_apply,
    IsFaithfulPosMap.basis_repr_apply, ← smul_smul]
  have s_rank_one : ∀ (α : ℂ) (x y : ℍ), (|α • x⟩⟨y| : ℍ →ₗ[ℂ] ℍ) = α • ↑|x⟩⟨y| :=
    by
    intro _ _ _
    simp_rw [rankOne.apply_smul]
    rfl
  have rank_one_s : ∀ (α : ℂ) (x y : ℍ), (|x⟩⟨starRingEnd ℂ α • y| : ℍ →ₗ[ℂ] ℍ) = α • ↑|x⟩⟨y| :=
    by
    intro _ _ _
    simp_rw [rankOne.smul_apply, starRingEnd_self_apply]
    rfl
  have rank_one_sumz :
    ∀ (x : ℍ) (y : n × n → ℍ),
      (|x⟩⟨∑ i : n × n, y i| : ℍ →ₗ[ℂ] ℍ) =
        ∑ i in Finset.univ ×ˢ Finset.univ, (|x⟩⟨y i| : ℍ →ₗ[ℂ] ℍ) :=
    fun α β => by
    simp only [rankOne_sum, LinearMap.ext_iff, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sum_apply, LinearMap.sum_apply, Finset.univ_product_univ,
      eq_self_iff_true, forall_true_iff]
  have sumz_rank_one :
    ∀ (x : n × n → ℍ) (y : ℍ),
      (|∑ i : n × n, x i⟩⟨y| : ℍ →ₗ[ℂ] ℍ) =
        ∑ i in Finset.univ ×ˢ Finset.univ, (|x i⟩⟨y| : ℍ →ₗ[ℂ] ℍ) :=
    fun α β => by
    simp only [sum_rankOne, LinearMap.ext_iff, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sum_apply, LinearMap.sum_apply, Finset.univ_product_univ,
      eq_self_iff_true, forall_true_iff]
  simp_rw [← rank_one_s ((unop (op y') * hφ.matrixIsPosDef.rpow (1/2)) _ _), ← s_rank_one, ←
    rank_one_sumz, ← sumz_rank_one, ← SMulHomClass.map_smul, ← map_sum, starRingEnd_apply, ←
    conjTranspose_smul, ← conjTranspose_sum, ← IsFaithfulPosMap.inner_coord,
    IsFaithfulPosMap.basis_apply, ← IsFaithfulPosMap.orthonormalBasis_apply, ←
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr]

theorem Module.Dual.IsFaithfulPosMap.sig_apply_sig (hφ : φ.IsFaithfulPosMap) (t s : ℝ)
    (x : Matrix n n ℂ) : hφ.sig t (hφ.sig s x) = hφ.sig (t + s) x := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, Matrix.PosDef.rpow_mul_rpow, ←
    Matrix.mul_assoc, Matrix.PosDef.rpow_mul_rpow, neg_add, add_comm]

theorem Module.Dual.IsFaithfulPosMap.sig_zero (hφ : φ.IsFaithfulPosMap) (x : Matrix n n ℂ) :
    hφ.sig 0 x = x := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, neg_zero, Matrix.PosDef.rpow_zero,
    Matrix.mul_one, Matrix.one_mul]

set_option synthInstance.maxHeartbeats 45000 in
theorem Module.Dual.IsFaithfulPosMap.Psi_left_inv' (hφ : φ.IsFaithfulPosMap) (t s : ℝ) (A : l(ℍ)) :
    (hφ.psiInvFun' t s) (hφ.psiToFun' t s A) = A :=
  by
  letI := Fact.mk hφ
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp_rw [map_sum, Module.Dual.IsFaithfulPosMap.psiToFun'_apply,
    Module.Dual.IsFaithfulPosMap.psiInvFun'_apply, unop_op, conjTranspose_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, neg_add_self, Module.Dual.IsFaithfulPosMap.sig_zero]

theorem Module.Dual.IsFaithfulPosMap.Psi_right_inv' (hφ : φ.IsFaithfulPosMap) (t s : ℝ)
    (x : Matrix n n ℂ) (y : (Matrix n n ℂ)ᵐᵒᵖ) :
    (hφ.psiToFun' t s) (hφ.psiInvFun' t s (x ⊗ₜ y)) = x ⊗ₜ y :=
  by
  letI := Fact.mk hφ
  simp_rw [Module.Dual.IsFaithfulPosMap.psiInvFun'_apply,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, Module.Dual.IsFaithfulPosMap.sig_apply_sig,
    add_neg_self, Module.Dual.IsFaithfulPosMap.sig_zero, conjTranspose_conjTranspose, op_unop]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private theorem foo_eq (hφ : φ.IsFaithfulPosMap) (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
    x =
      ∑ i : n × n in Finset.univ ×ˢ Finset.univ, ∑ j : n × n in Finset.univ ×ˢ Finset.univ,
        ((hφ.basis.tensorProduct hφ.basis.mulOpposite).repr x) (i, j) •
          hφ.basis i ⊗ₜ[ℂ] (hφ.basis.mulOpposite : Basis (n × n) ℂ _) j :=
  by
  simp_rw [← Finset.sum_product', Finset.univ_product_univ, Prod.mk.eta, ←
    Basis.tensorProduct_apply', Basis.sum_repr]

set_option synthInstance.maxHeartbeats 60000 in
/--
this defines the linear equivalence from linear maps on $M_n$ to $M_n\otimes M_n^\textnormal{op}$, i.e.,
  $$\Psi_{t,s}\colon \mathcal{L}(M_n) \cong_{\texttt{l}} M_n \otimes M_n^\textnormal{op}$$ -/
@[simps]
noncomputable def Module.Dual.IsFaithfulPosMap.psi (hφ : φ.IsFaithfulPosMap) (t s : ℝ) :
    l(ℍ) ≃ₗ[ℂ] ℍ ⊗[ℂ] ℍᵐᵒᵖ where
  toFun x := hφ.psiToFun' t s x
  invFun x := hφ.psiInvFun' t s x
  map_add' x y := map_add _ _ _
  map_smul' r x := LinearMap.map_smul (hφ.psiToFun' t s) _ _
  left_inv x := hφ.Psi_left_inv' t s x
  right_inv x := by
    rw [foo_eq hφ x]
    simp_rw [map_sum, SMulHomClass.map_smul, Module.Dual.IsFaithfulPosMap.Psi_right_inv']

set_option synthInstance.maxHeartbeats 60000 in
theorem Module.Dual.IsFaithfulPosMap.psi_0_0_eq [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    hφ.psi 0 0 x = (TensorProduct.map x op) (LinearMap.adjoint (LinearMap.mul' ℂ ℍ) (1 : ℍ)) :=
  by
  suffices
    ∀ a b : ℍ,
      hφ.psi 0 0 |a⟩⟨b| =
        (TensorProduct.map (↑|a⟩⟨b|) op) (LinearMap.adjoint (LinearMap.mul' ℂ ℍ) (1 : ℍ))
    by
    obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
    simp_rw [map_sum, this, TensorProduct.sum_map, LinearMap.sum_apply]
  intro a b
  simp_rw [LinearMap.mul'_adjoint, one_apply, ite_mul, one_mul, MulZeroClass.zero_mul, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, SMulHomClass.map_smul,
    TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, rankOne_apply, ← inner_conj_symm b,
    inner_stdBasisMatrix_left, starRingEnd_apply, ← conjTranspose_apply, conjTranspose_mul, ←
    TensorProduct.smul_tmul', smul_smul]
  rw [Finset.sum_rotate]
  simp_rw [← Finset.sum_smul, ← mul_apply, hφ.matrixIsPosDef.1.eq,
    @inv_mul_cancel_left_of_invertible n n ℂ _ _ _ φ.matrix bᴴ hφ.matrixIsPosDef.invertible,
    ← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum, ← SMulHomClass.map_smul, ← map_sum, ←
    smul_stdBasisMatrix']
  rw [← matrix_eq_sum_std_basis bᴴ, Module.Dual.IsFaithfulPosMap.psi_apply,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply]
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_zero]

theorem Module.Dual.IsFaithfulPosMap.psi_eq [hφ : φ.IsFaithfulPosMap]
  (t s : ℝ) (x : l(ℍ)) :
  hφ.psi t s x =
    (TensorProduct.map (hφ.sig t).toLinearMap (op ∘ₗ (hφ.sig (-s)).toLinearMap ∘ₗ unop))
      ((TensorProduct.map x op) (LinearMap.adjoint (LinearMap.mul' ℂ ℍ) (1 : ℍ))) :=
  by
  simp_rw [← Module.Dual.IsFaithfulPosMap.psi_0_0_eq, Module.Dual.IsFaithfulPosMap.psi_apply, ←
    LinearMap.comp_apply]
  revert x
  rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [LinearMap.comp_apply, Module.Dual.IsFaithfulPosMap.psiToFun'_apply,
    TensorProduct.map_tmul, Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.comp_apply, unop_op,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose]
  rfl

theorem LinearMap.mulLeft_toMatrix (hφ : φ.IsFaithfulPosMap) (x : Matrix n n ℂ) :
    hφ.toMatrix (LinearMap.mulLeft ℂ x) = x ⊗ₖ 1 :=
  by
  ext
  simp_rw [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.mulLeft_apply, IsFaithfulPosMap.basis_repr_apply,
    Module.Dual.IsFaithfulPosMap.inner_coord', IsFaithfulPosMap.basis_apply, Matrix.mul_assoc,
    PosDef.rpow_mul_rpow, neg_add_self, PosDef.rpow_zero, Matrix.mul_one, Matrix.mul_apply,
    stdBasisMatrix, kroneckerMap, of_apply, Matrix.one_apply, mul_boole, ite_and, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, eq_comm]

theorem LinearMap.mulRight_toMatrix [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
    hφ.toMatrix (LinearMap.mulRight ℂ x) = 1 ⊗ₖ (hφ.sig (1 / 2) x)ᵀ :=
  by
  ext
  simp_rw [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.mulRight_apply, Module.Dual.IsFaithfulPosMap.basis_repr_apply,
    Module.Dual.IsFaithfulPosMap.inner_coord']
  simp_rw [Matrix.mul_apply, kroneckerMap, of_apply, Matrix.one_apply, IsFaithfulPosMap.basis_apply,
    Matrix.mul_apply, stdBasisMatrix, boole_mul, Matrix.transpose_apply, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, eq_comm]
  simp only [ite_mul, MulZeroClass.zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp_rw [← Matrix.mul_apply]
  rfl

theorem Nontracial.inner_symm [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
  ⟪x, y⟫_ℂ = ⟪hφ.sig (-1) yᴴ, xᴴ⟫_ℂ :=
  by
  nth_rw 2 [← inner_conj_symm]
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg, PosDef.rpow_one_eq_self,
    PosDef.rpow_neg_one_eq_inv_self, Matrix.inner_conj_Q, conjTranspose_conjTranspose]
  nth_rw 1 [Matrix.inner_star_right]
  rw [inner_conj_symm]

theorem Module.Dual.IsFaithfulPosMap.sig_adjoint [hφ : φ.IsFaithfulPosMap] {t : ℝ} :
    LinearMap.adjoint (hφ.sig t : ℍ ≃ₐ[ℂ] ℍ).toLinearMap = (hφ.sig t).toLinearMap :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro x
  simp_rw [LinearMap.adjoint_inner_left, Module.Dual.IsFaithfulPosMap.inner_eq',
    AlgEquiv.toLinearMap_apply, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg]
  let hQ := hφ.matrixIsPosDef
  let Q := φ.matrix
  calc
    (Q * xᴴ * (hQ.rpow (-t) * x * hQ.rpow t)).trace =
        (hQ.rpow t * Q * xᴴ * hQ.rpow (-t) * x).trace :=
      ?_
    _ = (hQ.rpow t * hQ.rpow 1 * xᴴ * hQ.rpow (-t) * x).trace := by rw [PosDef.rpow_one_eq_self]
    _ = (hQ.rpow 1 * hQ.rpow t * xᴴ * hQ.rpow (-t) * x).trace := ?_
    _ = (Q * (hQ.rpow t * xᴴ * hQ.rpow (-t)) * x).trace := by
      simp_rw [PosDef.rpow_one_eq_self, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, trace_mul_cycle]
    simp_rw [Matrix.mul_assoc]
  · simp_rw [PosDef.rpow_mul_rpow, add_comm]

theorem Nontracial.inner_symm' [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
    ⟪x, y⟫_ℂ = ⟪hφ.sig (-(1 / 2 : ℝ)) yᴴ, hφ.sig (-(1 / 2 : ℝ)) xᴴ⟫_ℂ :=
  by
  simp_rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_left,
    Module.Dual.IsFaithfulPosMap.sig_adjoint, AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig]
  rw [Nontracial.inner_symm]
  norm_num

theorem Module.Dual.IsFaithfulPosMap.basis_apply' [hφ : Module.Dual.IsFaithfulPosMap φ]
    (i j : n) :
    hφ.basis (i, j) = stdBasisMatrix i j 1 * hφ.matrixIsPosDef.rpow (-(1 / 2)) :=
  Module.Dual.IsFaithfulPosMap.basis_apply _ (i, j)

theorem sig_apply_pos_def_matrix [hφ : Module.Dual.IsFaithfulPosMap φ] (t s : ℝ) :
    hφ.sig t (hφ.matrixIsPosDef.rpow s) = hφ.matrixIsPosDef.rpow s := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, PosDef.rpow_mul_rpow, neg_add_cancel_comm]

theorem sig_apply_pos_def_matrix' [hφ : Module.Dual.IsFaithfulPosMap φ] (t : ℝ) : hφ.sig t φ.matrix = φ.matrix :=
  by
  nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  rw [← sig_apply_pos_def_matrix t (1 : ℝ), PosDef.rpow_one_eq_self]

theorem linear_functional_comp_sig [hφ : Module.Dual.IsFaithfulPosMap φ] (t : ℝ) : φ ∘ₗ (hφ.sig t).toLinearMap = φ :=
  by
  ext1 x
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, φ.apply]
  nth_rw 1 [← sig_apply_pos_def_matrix' t]
  rw [← _root_.map_mul, aut_mat_inner_trace_preserving]

theorem linear_functional_apply_sig [hφ : Module.Dual.IsFaithfulPosMap φ] (t : ℝ) (x : ℍ) : φ (hφ.sig t x) = φ x := by
  rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.comp_apply, linear_functional_comp_sig]

end SingleBlock

section DirectSum

open Module.Dual

/-! # Section direct_sum -/

@[reducible]
def PiMat (k : Type*) [Fintype k] [DecidableEq k] (s : k → Type*) [Π i, Fintype (s i)]
  [Π i, DecidableEq (s i)] := Π i, Matrix (s i) (s i) ℂ

local notation "ℍ_" i => Matrix (s i) (s i) ℂ

theorem includeBlock_adjoint [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    (x : ∀ j, Matrix (s j) (s j) ℂ) :
    LinearMap.adjoint (includeBlock : (ℍ_ i) →ₗ[ℂ] PiMat k s) x = x i :=
  by
  apply @ext_inner_left ℂ _ _
  intro a
  rw [LinearMap.adjoint_inner_right, pi.IsFaithfulPosMap.includeBlock_left_inner]

open scoped ComplexOrder

-- instance
--   Pi.tensorProduct_finiteDimensional :
--       FiniteDimensional ℂ (PiMat k s ⊗[ℂ] PiMat k s) :=
--   by infer_instance
  -- FiniteDimensional.of_finite_basis (Basis.ofVectorSpace ℂ _)
    -- (Basis.ofVectorSpaceIndex ℂ _).toFinite

open scoped Functional

theorem pi_inner_stdBasisMatrix_left [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (i : k) (j l : s i)
    (x : PiMat k s) :
    ⟪blockDiag' (stdBasisMatrix (⟨i, j⟩ : Σ a, s a) (⟨i, l⟩ : Σ a, s a) (1 : ℂ)), x⟫_ℂ =
      (x i * (ψ i).matrix) j l :=
  by
  simp only [← includeBlock_apply_stdBasisMatrix,
    pi.IsFaithfulPosMap.includeBlock_left_inner, inner_stdBasisMatrix_left]

theorem eq_mpr_stdBasisMatrix {k : Type _} {s : k → Type _} [∀ i, DecidableEq (s i)] {i j : k}
    {b c : s j} (h₁ : i = j) :
    (by rw [h₁]; exact stdBasisMatrix b c (1 : ℂ) : Matrix (s i) (s i) ℂ) =
      stdBasisMatrix (by rw [h₁]; exact b) (by rw [h₁]; exact c) (1 : ℂ) :=
  by aesop

theorem pi_inner_stdBasisMatrix_stdBasisMatrix [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i j : k}
    (a b : s i) (c d : s j) :
    ⟪blockDiag' (stdBasisMatrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
        blockDiag' (stdBasisMatrix ⟨j, c⟩ ⟨j, d⟩ (1 : ℂ))⟫_ℂ =
      dite (i = j)
        (fun h => ite (a = by rw [h]; exact c) ((ψ i).matrix (by rw [h]; exact d) b) 0)
        fun _ => 0 :=
  by
  simp only [← includeBlock_apply_stdBasisMatrix]
  by_cases h : i = j
  ·
    simp only [h, dif_pos, pi.IsFaithfulPosMap.includeBlock_inner_same' h,
      inner_stdBasisMatrix_stdBasisMatrix, eq_mpr_stdBasisMatrix h]
  · simp only [h, dif_neg, not_false_iff, pi.IsFaithfulPosMap.includeBlock_inner_ne_same h]

theorem pi_inner_stdBasisMatrix_stdBasisMatrix_same [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    (a b c d : s i) :
    ⟪blockDiag' (stdBasisMatrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
        blockDiag' (stdBasisMatrix ⟨i, c⟩ ⟨i, d⟩ (1 : ℂ))⟫_ℂ =
      ite (a = c) ((ψ i).matrix d b) 0 :=
  by rw [pi_inner_stdBasisMatrix_stdBasisMatrix]; aesop

theorem pi_inner_stdBasisMatrix_stdBasisMatrix_ne [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i j : k}
    (h : i ≠ j) (a b : s i) (c d : s j) :
    ⟪blockDiag' (stdBasisMatrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
        blockDiag' (stdBasisMatrix ⟨j, c⟩ ⟨j, d⟩ (1 : ℂ))⟫_ℂ =
      0 :=
  by rw [pi_inner_stdBasisMatrix_stdBasisMatrix]; aesop

theorem LinearMap.pi_mul'_adjoint_single_block [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    (x : Matrix (s i) (s i) ℂ) :
    (LinearMap.adjoint (LinearMap.mul' ℂ (PiMat k s))) (includeBlock x) =
      (TensorProduct.map includeBlock includeBlock)
        (LinearMap.adjoint (LinearMap.mul' ℂ (ℍ_ i)) x) :=
  by
  rw [TensorProduct.inner_ext_iff']
  intro a b
  rw [LinearMap.adjoint_inner_left, LinearMap.mul'_apply,
    pi.IsFaithfulPosMap.includeBlock_left_inner, ← LinearMap.adjoint_inner_right,
    TensorProduct.map_adjoint, TensorProduct.map_tmul, LinearMap.adjoint_inner_left,
    LinearMap.mul'_apply]
  simp_rw [includeBlock_adjoint, Pi.mul_apply]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b c d) -/
set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem LinearMap.pi_mul'_adjoint [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : PiMat k s) :
    LinearMap.adjoint (LinearMap.mul' ℂ (PiMat k s)) x =
      ∑ r : k, ∑ a, ∑ b, ∑ c, ∑ d,
        (x r a d * (pi.matrixBlock ψ r)⁻¹ c b) •
          blockDiag' (stdBasisMatrix (⟨r, a⟩ : Σ i, s i) (⟨r, b⟩ : Σ i, s i) (1 : ℂ)) ⊗ₜ[ℂ]
            blockDiag' (stdBasisMatrix (⟨r, c⟩ : Σ i, s i) (⟨r, d⟩ : Σ i, s i) (1 : ℂ)) :=
  by
  nth_rw 1 [matrix_eq_sum_includeBlock x]
  simp_rw [map_sum, LinearMap.pi_mul'_adjoint_single_block]
  apply Finset.sum_congr rfl; intros
  rw [LinearMap.mul'_adjoint]
  simp_rw [map_sum, SMulHomClass.map_smul, TensorProduct.map_tmul,
    includeBlock_apply_stdBasisMatrix, pi.matrixBlock_apply]

theorem LinearMap.pi_mul'_apply_includeBlock {i : k} (x : (ℍ_ i) ⊗[ℂ] ℍ_ i) :
    LinearMap.mul' ℂ (PiMat k s) ((TensorProduct.map includeBlock includeBlock) x) =
      includeBlock (LinearMap.mul' ℂ (ℍ_ i) x) :=
  by
  simp_rw [← LinearMap.comp_apply]
  revert x
  rw [← LinearMap.ext_iff, TensorProduct.ext_iff]
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    includeBlock_hMul_same]

private theorem linear_map.pi_mul'_comp_mul_adjoint_aux [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    {i : k} (x : ℍ_ i) :
    LinearMap.mul' ℂ (PiMat k s) (LinearMap.adjoint (LinearMap.mul' ℂ (PiMat k s)) (includeBlock x)) =
      trace ((ψ i).matrix⁻¹) • includeBlock x :=
  by
  rw [LinearMap.pi_mul'_adjoint_single_block, LinearMap.pi_mul'_apply_includeBlock]
  simp_rw [← LinearMap.comp_apply, Qam.Nontracial.mul_comp_mul_adjoint, LinearMap.comp_apply,
    LinearMap.smul_apply, SMulHomClass.map_smul, LinearMap.one_apply]

set_option synthInstance.maxHeartbeats 0 in
theorem LinearMap.pi_mul'_comp_mul'_adjoint [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : PiMat k s) :
    LinearMap.mul' ℂ (PiMat k s) (LinearMap.adjoint (LinearMap.mul' ℂ (PiMat k s)) x) =
      ∑ i, Matrix.trace (((ψ i).matrix)⁻¹) • includeBlock (x i) :=
  by
  nth_rw 1 [matrix_eq_sum_includeBlock x]
  simp_rw [map_sum, linear_map.pi_mul'_comp_mul_adjoint_aux]

lemma Matrix.smul_inj_mul_one {n : Type*} [Fintype n] [DecidableEq n]
  [Nonempty n] (x y : ℂ) :
  x • (1 : Matrix n n ℂ) = y • (1 : Matrix n n ℂ) ↔ x = y :=
by
  simp_rw [← Matrix.ext_iff, Matrix.smul_apply, Matrix.one_apply, smul_ite,
    smul_zero, smul_eq_mul, mul_one]
  constructor
  . intro h
    let i : n := Nonempty.some ‹_›
    specialize h i i
    simp only [↓reduceIte] at h
    exact h
  . rintro rfl i j
    rfl

theorem LinearMap.pi_mul'_comp_mul'_adjoint_eq_smul_id_iff [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    [∀ i, Nontrivial (s i)] (α : ℂ) :
    LinearMap.mul' ℂ (PiMat k s) ∘ₗ (LinearMap.adjoint (LinearMap.mul' ℂ (PiMat k s))) = α • 1 ↔ ∀ i, Matrix.trace ((ψ i).matrix⁻¹) = α :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.pi_mul'_comp_mul'_adjoint,
    Function.funext_iff, Finset.sum_apply, ← LinearMap.map_smul,
    includeBlock_apply, Finset.sum_dite_eq', Finset.mem_univ, if_true,
    LinearMap.smul_apply, LinearMap.one_apply, Pi.smul_apply]
  simp only [eq_mp_eq_cast, cast_eq, ← Pi.smul_apply]
  -- simp_rw [← @Function.funext_iff k]
  constructor
  · intro h
    specialize h (1 : PiMat k s)
    simp only [Pi.smul_apply, Pi.one_apply] at h
    simp_rw [Matrix.smul_inj_mul_one] at h
    exact h
  · intro h i a
    rw [h]

theorem Module.Dual.pi.IsFaithfulPosMap.inner_coord' [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    (ij : s i × s i) (x : PiMat k s) :
    ⟪Module.Dual.pi.IsFaithfulPosMap.basis (fun i => (hψ i)) ⟨i, ij⟩, x⟫_ℂ =
      (x * fun j => (hψ j).matrixIsPosDef.rpow (1 / 2)) i ij.1 ij.2 :=
  by
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.basis_apply, ←
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, Pi.mul_apply,
    Module.Dual.pi.IsFaithfulPosMap.includeBlock_left_inner,
    Module.Dual.IsFaithfulPosMap.inner_coord]

theorem Module.Dual.pi.IsFaithfulPosMap.map_star (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (x : PiMat k s) :
    pi ψ (star x) = star (pi ψ x) :=
  pi.IsPosMap.isReal (fun i => (hψ i).1) x

theorem Nontracial.Pi.unit_adjoint_eq [hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
    LinearMap.adjoint (Algebra.linearMap ℂ (PiMat k s) : ℂ →ₗ[ℂ] PiMat k s) = pi ψ := by
  rw [← pi.IsFaithfulPosMap.adjoint_eq, LinearMap.adjoint_adjoint]

def Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef {k : Type _} {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    (hψ : ∀ i, (ψ i).IsFaithfulPosMap) := fun i => (hψ i).matrixIsPosDef

noncomputable def Pi.PosDef.rpow {k : Type _} {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] {a : ∀ i, Matrix (s i) (s i) ℂ} (ha : ∀ i, (a i).PosDef) (r : ℝ) :=
  fun i => (ha i).rpow r

theorem Pi.PosDef.rpow_hMul_rpow {a : PiMat k s} (ha : ∀ i, (a i).PosDef) (r₁ r₂ : ℝ) :
    Pi.PosDef.rpow ha r₁ * Pi.PosDef.rpow ha r₂ = Pi.PosDef.rpow ha (r₁ + r₂) :=
  by
  ext1 i
  simp only [Pi.mul_apply, Pi.PosDef.rpow, PosDef.rpow_mul_rpow]

theorem Pi.PosDef.rpow_zero {a : PiMat k s} (ha : ∀ i, (a i).PosDef) : Pi.PosDef.rpow ha 0 = 1 :=
  by
  ext x i j
  simp only [Pi.PosDef.rpow, Matrix.PosDef.rpow_zero, Pi.one_apply]

theorem Module.Dual.pi.IsFaithfulPosMap.includeBlock_right_inner {k : Type _} [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
    {ψ : ∀ i : k, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i : k, (ψ i).IsFaithfulPosMap]
    {i : k} (y : ∀ j : k, Matrix (s j) (s j) ℂ) (x : Matrix (s i) (s i) ℂ) :
    ⟪y, includeBlock x⟫_ℂ = ⟪y i, x⟫_ℂ := by
  rw [← inner_conj_symm, pi.IsFaithfulPosMap.includeBlock_left_inner, inner_conj_symm]

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

theorem pi_includeBlock_right_rankOne [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (a : PiMat k s) {i : k}
    (b : ℍ_ i) (c : PiMat k s) (j : k) : |a⟩⟨includeBlock b| c j = ⟪b, c i⟫_ℂ • a j := by
  simp only [rankOne_apply, pi.IsFaithfulPosMap.includeBlock_left_inner, Pi.smul_apply]

theorem pi_includeBlock_left_rankOne [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (b : PiMat k s) {i : k}
    (a : ℍ_ i) (c : PiMat k s) (j : k) :
    |includeBlock a⟩⟨b| c j =
      ⟪b, c⟫_ℂ • dite (i = j) (fun h => by rw [← h]; exact a) fun h => 0 :=
  by
  simp only [rankOne_apply, pi.IsFaithfulPosMap.includeBlock_left_inner, Pi.smul_apply,
    includeBlock_apply, smul_dite, smul_zero]
  rfl

noncomputable def Module.Dual.pi.IsFaithfulPosMap.sig (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) : PiMat k s ≃ₐ[ℂ] PiMat k s :=
  let hQ := Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ
  { toFun := fun x => Pi.PosDef.rpow hQ (-z) * x * Pi.PosDef.rpow hQ z
    invFun := fun x => Pi.PosDef.rpow hQ z * x * Pi.PosDef.rpow hQ (-z)
    left_inv := fun x => by
      simp only [← mul_assoc, Pi.PosDef.rpow_hMul_rpow]
      simp only [mul_assoc, Pi.PosDef.rpow_hMul_rpow]
      simp only [add_neg_self, Pi.PosDef.rpow_zero, one_mul, mul_one, neg_add_self]
    right_inv := fun x => by
      simp only [← mul_assoc, Pi.PosDef.rpow_hMul_rpow]
      simp only [mul_assoc, Pi.PosDef.rpow_hMul_rpow]
      simp only [add_neg_self, Pi.PosDef.rpow_zero, one_mul, mul_one, neg_add_self]
    map_add' := fun x y => by simp only [mul_add, add_mul]
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
        Pi.PosDef.rpow_hMul_rpow, neg_add_self, Pi.PosDef.rpow_zero]
    map_mul' := fun x y => by
      simp_rw [mul_assoc]
      simp only [← mul_assoc (Pi.PosDef.rpow _ z) (Pi.PosDef.rpow _ (-z)) (y * _),
        Pi.PosDef.rpow_hMul_rpow, add_neg_self, Pi.PosDef.rpow_zero, one_mul] }

theorem Module.Dual.pi.IsFaithfulPosMap.sig_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (z : ℝ)
    (x : PiMat k s) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ z) x =
      Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) (-z) * x *
        Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) z :=
  rfl

theorem Module.Dual.pi.IsFaithfulPosMap.sig_symm_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (z : ℝ) (x : PiMat k s) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ z).symm x =
      Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) z * x *
        Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) (-z) :=
  rfl

theorem Module.Dual.pi.IsFaithfulPosMap.sig_symm_eq (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ z).symm = Module.Dual.pi.IsFaithfulPosMap.sig hψ (-z) :=
  by
  ext1
  simp only [Module.Dual.pi.IsFaithfulPosMap.sig_apply,
    Module.Dual.pi.IsFaithfulPosMap.sig_symm_apply, neg_neg]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_apply_single_block
    (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (z : ℝ) {i : k} (x : ℍ_ i) :
    Module.Dual.pi.IsFaithfulPosMap.sig hψ z (includeBlock x) =
      includeBlock ((hψ i).sig z x) :=
  by
  simp only [Module.Dual.pi.IsFaithfulPosMap.sig_apply, Module.Dual.IsFaithfulPosMap.sig_apply,
    Pi.mul_apply]
  simp_rw [hMul_includeBlock, includeBlock_hMul, includeBlock_inj, Pi.PosDef.rpow]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) (x : PiMat k s) {i : k} :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ z x) i = (hψ i).sig z (x i) :=
  rfl

theorem Pi.PosDef.rpow.isPosDef {a : PiMat k s} (ha : ∀ i, (a i).PosDef) (r : ℝ) :
    ∀ i, ((Pi.PosDef.rpow ha r) i).PosDef := by
  intro i
  simp only [Pi.PosDef.rpow]
  exact Matrix.PosDef.rpow.isPosDef _ _

theorem Pi.PosDef.rpow.is_self_adjoint {a : PiMat k s} (ha : ∀ i, (a i).PosDef) (r : ℝ) :
    star (Pi.PosDef.rpow ha r) = Pi.PosDef.rpow ha r :=
  by
  ext1 i
  simp only [Pi.PosDef.rpow, star_apply, Pi.star_apply]
  exact Matrix.PosDef.rpow.isHermitian _ _

theorem Module.Dual.pi.IsFaithfulPosMap.sig_star (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (z : ℝ)
    (x : PiMat k s) :
    star (Module.Dual.pi.IsFaithfulPosMap.sig hψ z x) =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ (-z) (star x) :=
  by
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.sig_apply, StarMul.star_mul,
    Pi.PosDef.rpow.is_self_adjoint, mul_assoc, neg_neg]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (t r : ℝ) (x : PiMat k s) :
    Module.Dual.pi.IsFaithfulPosMap.sig hψ t (Module.Dual.pi.IsFaithfulPosMap.sig hψ r x) =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ (t + r) x :=
  by
  simp only [Module.Dual.pi.IsFaithfulPosMap.sig_apply, Pi.PosDef.rpow_hMul_rpow]
  simp_rw [← mul_assoc, Pi.PosDef.rpow_hMul_rpow, mul_assoc, Pi.PosDef.rpow_hMul_rpow, neg_add,
    add_comm]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_zero (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (x : PiMat k s) :
    Module.Dual.pi.IsFaithfulPosMap.sig hψ 0 x = x := by
  simp only [Module.Dual.pi.IsFaithfulPosMap.sig_apply, Pi.PosDef.rpow_zero, one_mul, mul_one,
    neg_zero]

theorem Module.Dual.pi.IsFaithfulPosMap.toMatrix_apply'' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (f : (∀ i, Matrix (s i) (s i) ℂ) →ₗ[ℂ] ∀ i, Matrix (s i) (s i) ℂ) (r l : Σ r, s r × s r) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hψ i)) f r l =
      (f (includeBlock ((hψ l.1).basis l.2)) *
          Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) (1 / 2 : ℝ))
        r.1 r.2.1 r.2.2 :=
  by
  rw [Module.Dual.pi.IsFaithfulPosMap.toMatrix_apply']
  rfl

theorem Finset.sum_product_univ {β α γ : Type _} [AddCommMonoid β] [Fintype α] [Fintype γ]
    {f : γ × α → β} : ∑ x : γ × α, f x = ∑ x : γ, ∑ y : α, f (x, y) :=
  Finset.sum_product

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a i j b c d) -/
theorem Module.Dual.pi.IsFaithfulPosMap.toMatrix_symm_apply' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x : Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hψ i)).symm x =
      ∑ a, ∑ i, ∑ j, ∑ b, ∑ c, ∑ d,
        x ⟨a, (i, j)⟩ ⟨b, (c, d)⟩ •
          |Module.Dual.pi.IsFaithfulPosMap.basis (fun e => (hψ e))
              ⟨a,
                (i,
                  j)⟩⟩⟨Module.Dual.pi.IsFaithfulPosMap.basis (fun e => (hψ e)) ⟨b, (c, d)⟩| :=
  by
  rw [LinearMap.ext_iff]
  intro y
  rw [Function.funext_iff]
  intro a
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_symm,
    toLinAlgEquiv_apply, mulVec, dotProduct, pi.IsFaithfulPosMap.basis_repr_apply,
    pi.IsFaithfulPosMap.basis_apply, ← Module.Dual.IsFaithfulPosMap.basis_apply',
    Finset.sum_sigma_univ, ContinuousLinearMap.coe_sum,
    ContinuousLinearMap.coe_smul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply,
    pi.IsFaithfulPosMap.includeBlock_left_inner, Finset.sum_product_univ, Finset.sum_smul,
    smul_smul]

theorem TensorProduct.of_basis_eq_span {𝕜 : Type _} {E : Type _} {F : Type _} [IsROrC 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] (x : TensorProduct 𝕜 E F)
    {ι₁ ι₂ : Type _} [Fintype ι₁] [Fintype ι₂] (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F) :
    x = ∑ i : ι₁, ∑ j : ι₂, (b₁.tensorProduct b₂).repr x (i, j) • b₁ i ⊗ₜ[𝕜] b₂ j :=
  x.induction_on
  (by simp only [map_zero, Finsupp.zero_apply, zero_smul, Finset.sum_const_zero])
  (fun α₁ α₂ => by
    simp_rw [Basis.tensorProduct_repr_tmul_apply, ← TensorProduct.smul_tmul_smul, ←
      TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, Basis.sum_repr])
  (fun a b ha hb => by
    simp_rw [_root_.map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← ha, ← hb])

-- example (hψ : Π i, (ψ i).is_faithful_pos_map) :
--   matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ ≃ₐ[ℂ] PiMat k s ⊗[ℂ] PiMat k s :=
-- begin
--   letI : ∀ (i : k), smul_comm_class ℂ ℂ ((λ (i : k), matrix (s i) (s i) ℂ) i) :=
--   λ i, by apply_instance,
--   let h₂ := @direct_sum_tensor ℂ _ k k _ _ _ _ (λ i, ℍ_ i) (λ i, ℍ_ i) _ _
--     (λ i, matrix.module) (λ i, matrix.module),
--   exact
--   { to_fun := λ f,
--     by {
--       let f' :=
--       apply h₂.symm.to_fun,
--       intros i,
--       apply kronecker_to_tensor.to_fun,
--       intros a b,
--       exact f ⟨i.1, (a.1, b.1)⟩ ⟨i.2, (a.2, b.2)⟩,
--      }
--     -- ∑ a i j b c d,
--       -- ((hψ a).basis.tensor_product (hψ b).basis).repr
--       ,
--     inv_fun := _,
--     left_inv := λ x, _,
--     right_inv := λ x, _,
--     map_mul' := λ x y, _,
--     map_add' := λ x y, _,
--     commutes' := λ r, _ }
-- end
-- noncomputable def linear_map.IsFaithfulPosMap.direct_sum.to_matrix'
--   (hψ : ∀ (i : k), (ψ i).is_faithful_pos_map) :
--   l(PiMat k s) ≃ₐ[ℂ] PiMat k s ⊗[ℂ] PiMat k s :=
-- begin
--   let M := linear_map.IsFaithfulPosMap.direct_sum.to_matrix hψ,
--   exact
--   { to_fun := λ f, by { let f' := M f, },
--     inv_fun := _,
--     left_inv := λ x, _,
--     right_inv := λ x, _,
--     map_mul' := λ x y, _,
--     map_add' := λ x y, _,
--     commutes' := λ r, _ }
-- end
theorem Module.Dual.pi.IsFaithfulPosMap.toMatrix_eq_orthonormalBasis_toMatrix
    [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : l(PiMat k s)) :
    (pi.IsFaithfulPosMap.toMatrix fun i => (hψ i)) x =
      (pi.IsFaithfulPosMap.orthonormalBasis hψ).toMatrix x :=
  by
  ext
  simp_rw [pi.IsFaithfulPosMap.toMatrix_apply', OrthonormalBasis.toMatrix_apply,
    pi.IsFaithfulPosMap.orthonormalBasis_apply, pi.IsFaithfulPosMap.includeBlock_left_inner,
    ← Module.Dual.IsFaithfulPosMap.basis_apply, (hψ _).inner_coord']

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
theorem Module.Dual.pi.IsFaithfulPosMap.linearMap_eq [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x : l(PiMat k s)) :
    x =
      ∑ a, ∑ b,
        (Module.Dual.pi.IsFaithfulPosMap.toMatrix (fun i => (hψ i)) x) a b •
          |(Module.Dual.pi.IsFaithfulPosMap.basis fun i => (hψ i))
              a⟩⟨(Module.Dual.pi.IsFaithfulPosMap.basis fun i => (hψ i)) b| :=
  by
  simp_rw [pi.IsFaithfulPosMap.basis_apply, ← pi.IsFaithfulPosMap.orthonormalBasis_apply,
    ContinuousLinearMap.coe_sum, ContinuousLinearMap.coe_smul]
  rw [← OrthonormalBasis.toMatrix_symm_apply]
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.toMatrix_eq_orthonormalBasis_toMatrix,
    StarAlgEquiv.symm_apply_apply]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
set_option synthInstance.maxHeartbeats 0 in
noncomputable def Module.Dual.pi.IsFaithfulPosMap.psiToFun' (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (t r : ℝ) : l(PiMat k s) →ₗ[ℂ] PiMat k s ⊗[ℂ] (PiMat k s)ᵐᵒᵖ
    where
  toFun x :=
    ∑ a, ∑ b,
      (Module.Dual.pi.IsFaithfulPosMap.toMatrix hψ x) a b •
        Module.Dual.pi.IsFaithfulPosMap.sig hψ t
            ((Module.Dual.pi.IsFaithfulPosMap.basis hψ) a) ⊗ₜ[ℂ]
          (op : PiMat k s →ₗ[ℂ] (PiMat k s)ᵐᵒᵖ)
            (star
              (Module.Dual.pi.IsFaithfulPosMap.sig hψ r
                ((Module.Dual.pi.IsFaithfulPosMap.basis hψ) b)))
  map_add' x y := by simp_rw [map_add, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [SMulHomClass.map_smul, Matrix.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

theorem Pi.IsFaithfulPosMap.ToMatrix.rankOne_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x y : PiMat k s) :
    pi.IsFaithfulPosMap.toMatrix hψ |x⟩⟨y| = fun i j : Σ i, s i × s i =>
      (col (reshape (x i.fst * (hψ i.1).matrixIsPosDef.rpow (1 / 2))) *
          (col (reshape (y j.fst * (hψ j.1).matrixIsPosDef.rpow (1 / 2))))ᴴ)
        i.2 j.2 :=
  by
  ext1
  ext1
  simp_rw [pi.IsFaithfulPosMap.toMatrix_apply', ContinuousLinearMap.coe_coe, _root_.rankOne_apply,
    Pi.smul_apply, Matrix.smul_mul, Matrix.smul_apply,
    Module.Dual.pi.IsFaithfulPosMap.includeBlock_right_inner, ← inner_conj_symm (y _),
    IsFaithfulPosMap.inner_coord', smul_eq_mul, mul_comm, ← reshape_apply (x _ * _), ←
    reshape_apply (y _ * _), starRingEnd_apply, conjTranspose_col, ← vecMulVec_eq,
    vecMulVec_apply, Pi.star_apply]

theorem Module.Dual.pi.IsFaithfulPosMap.basis_repr_apply_apply
    [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (a : PiMat k s) (x : Σ i, s i × s i) :
    (Module.Dual.pi.IsFaithfulPosMap.basis hψ).repr a x =
      ((hψ x.1).basis.repr (a x.fst)) x.snd :=
  rfl

theorem Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (t r : ℝ) (a b : PiMat k s) :
    Module.Dual.pi.IsFaithfulPosMap.psiToFun' hψ t r |a⟩⟨b| =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ t a ⊗ₜ[ℂ]
        (op : PiMat k s →ₗ[ℂ] (PiMat k s)ᵐᵒᵖ) (star (Module.Dual.pi.IsFaithfulPosMap.sig hψ r b)) :=
  by
  letI : ∀ i, StarModule ℂ (Matrix ((fun i : k => s i) i) ((fun i : k => s i) i) ℂ) :=
    by
    intro i
    infer_instance
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.psiToFun', LinearMap.coe_mk,
    AddHom.coe_mk,
    Pi.IsFaithfulPosMap.ToMatrix.rankOne_apply, conjTranspose_col, ← vecMulVec_eq,
    vecMulVec_apply, ← TensorProduct.smul_tmul_smul, ← SMulHomClass.map_smul, Pi.star_apply, ←
    star_smul, ← SMulHomClass.map_smul, ← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ←
    map_sum, reshape_apply, ← star_sum, ← map_sum, ← Module.Dual.IsFaithfulPosMap.inner_coord', ←
    IsFaithfulPosMap.basis_repr_apply,
    -- ← Module.Dual.pi.IsFaithfulPosMap.basis_repr_apply_apply,
    Basis.sum_repr]

-- @[instance]
-- private def pi_matrix_tensor_is_semiring :
--     Semiring (∀ i : k × k, Matrix (s i.1) (s i.1) ℂ ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ) :=
--   by
--   apply @Pi.semiring _ _ _
--   intro i
--   infer_instance

-- @[instance]
-- private def pi_matrix_tensor_is_algebra :
--     Algebra ℂ (∀ i : k × k, Matrix (s i.1) (s i.1) ℂ ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ) :=
--   by
--   apply @Pi.algebra _ _ _ _ _ _
--   intro i
--   infer_instance

@[simps]
def Pi.transposeAlgEquiv (p : Type _) [Fintype p] [DecidableEq p] (n : p → Type _)
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] :
    (∀ i, Matrix (n i) (n i) ℂ) ≃ₐ[ℂ] (∀ i, Matrix (n i) (n i) ℂ)ᵐᵒᵖ
    where
  toFun A := MulOpposite.op fun i => (A i)ᵀ
  invFun A i := (MulOpposite.unop A i)ᵀ
  left_inv A := by simp only [MulOpposite.unop_op, transpose_transpose]
  right_inv A := by simp only [MulOpposite.op_unop, transpose_transpose]
  map_add' A B := by
    simp only [Pi.add_apply, transpose_add]
    rfl
  map_mul' A B :=
    by
    simp only [Pi.mul_apply, transpose_mul, ← MulOpposite.op_mul]
    rfl
  commutes' c :=
    by
    simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply, transpose_smul,
      transpose_one]
    rfl

theorem Pi.transposeAlgEquiv_symm_op_apply (A : ∀ i, Matrix (s i) (s i) ℂ) :
    (Pi.transposeAlgEquiv k s).symm (MulOpposite.op A) = fun i => (A i)ᵀ :=
  rfl

private noncomputable def f₂_equiv :
    (PiMat k s) ⊗[ℂ] (PiMat k s) ≃ₐ[ℂ] (Π i : k × k, Matrix (s i.1) (s i.1) ℂ ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ) :=
  by
  let this :=
    @directSumTensorAlgEquiv ℂ _ _ _ _ _ _ _ (fun i => Matrix (s i) (s i) ℂ)
      (fun i => Matrix (s i) (s i) ℂ) (fun i => Matrix.instRing) (fun i => Matrix.instRing)
      (fun i => Matrix.instAlgebra) fun i => Matrix.instAlgebra
  exact this

private noncomputable def f₃_equiv :
    (Π i : k × k, Matrix (s i.1) (s i.1) ℂ ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ) ≃ₐ[ℂ]
      (Π i : k × k, Matrix (s i.1 × s i.2) (s i.1 × s i.2) ℂ) :=
  by
  apply AlgEquiv.piCongrRight
  intro i
  exact kroneckerToTensor.symm

private def f₄_equiv :
    (Π i : k × k, Matrix (s i.1 × s i.2) (s i.1 × s i.2) ℂ) ≃ₐ[ℂ]
      { x : Matrix (Σ i : k × k, s i.1 × s i.2) (Σ i : k × k, s i.1 × s i.2) ℂ //
        x.IsBlockDiagonal } :=
  isBlockDiagonalPiAlgEquiv.symm

noncomputable def tensorProductMulOpEquiv :
    ((PiMat k s) ⊗[ℂ] (PiMat k s)ᵐᵒᵖ) ≃ₐ[ℂ] (Π i : k × k, Matrix (s i.1 × s i.2) (s i.1 × s i.2) ℂ) :=
  (AlgEquiv.TensorProduct.map (1 : PiMat k s ≃ₐ[ℂ] PiMat k s)
        (Pi.transposeAlgEquiv k s : PiMat k s ≃ₐ[ℂ] (PiMat k s)ᵐᵒᵖ).symm).trans
    (f₂_equiv.trans f₃_equiv)

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
noncomputable def Module.Dual.pi.IsFaithfulPosMap.psiInvFun' (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (t r : ℝ) : PiMat k s ⊗[ℂ] (PiMat k s)ᵐᵒᵖ →ₗ[ℂ] l(PiMat k s)
    where
  toFun x :=
    ∑ a : Σ i, s i × s i, ∑ b : Σ i, s i × s i,
      (Basis.tensorProduct (pi.IsFaithfulPosMap.basis hψ)
              (pi.IsFaithfulPosMap.basis hψ).mulOpposite).repr
          x (a, b) •
        ↑|Module.Dual.pi.IsFaithfulPosMap.sig hψ (-t)
              (pi.IsFaithfulPosMap.basis hψ
                a)⟩⟨Module.Dual.pi.IsFaithfulPosMap.sig hψ (-r)
              (star (pi.IsFaithfulPosMap.basis hψ b))|
  map_add' x y := by simp_rw [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [SMulHomClass.map_smul, Finsupp.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

theorem rankOne_smul_smul {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) (r₁ r₂ : 𝕜) :
    rankOne (r₁ • x) (star r₂ • y) = (r₁ * r₂) • (rankOne x y : E →L[𝕜] E) := by
  simp only [rankOne.smul_apply, rankOne.apply_smul, smul_smul, starRingEnd_apply, star_star, mul_comm]

theorem rankOne_lm_smul_smul {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x y : E) (r₁ r₂ : 𝕜) :
    ↑(rankOne (r₁ • x) (star r₂ • y) : E →L[𝕜] E) =
      (r₁ * r₂) • ((rankOne x y : E →L[𝕜] E) : E →ₗ[𝕜] E) :=
  by rw [rankOne_smul_smul, ContinuousLinearMap.coe_smul]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem rankOne_sum_sum {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι₁ ι₂ : Type _} [Fintype ι₁] [Fintype ι₂] (f : ι₁ → E) (g : ι₂ → E) :
    rankOne (∑ i, f i) (∑ i, g i) = ∑ i, ∑ j, (rankOne (f i) (g j) : E →L[𝕜] E) := by
  simp only [sum_rankOne, rankOne_sum]
  rw [Finset.sum_comm]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem rankOne_lm_sum_sum {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι₁ ι₂ : Type _} [Fintype ι₁] [Fintype ι₂] (f : ι₁ → E) (g : ι₂ → E) :
    ↑(rankOne (∑ i, f i) (∑ i, g i) : E →L[𝕜] E) =
      ∑ i, ∑ j, ((rankOne (f i) (g j) : E →L[𝕜] E) : E →ₗ[𝕜] E) :=
  by simp_rw [sum_rankOne, rankOne_sum, ContinuousLinearMap.coe_sum]

theorem Module.Dual.pi.IsFaithfulPosMap.psiInvFun'_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (t r : ℝ) (x : PiMat k s) (y : (PiMat k s)ᵐᵒᵖ) :
    Module.Dual.pi.IsFaithfulPosMap.psiInvFun' hψ t r (x ⊗ₜ[ℂ] y) =
      |Module.Dual.pi.IsFaithfulPosMap.sig hψ (-t)
          x⟩⟨Module.Dual.pi.IsFaithfulPosMap.sig hψ (-r) (star (MulOpposite.unop y))| :=
  by
  letI : ∀ i, StarModule ℂ (Matrix ((fun i : k => s i) i) ((fun i : k => s i) i) ℂ) :=
    by
    intro i
    infer_instance
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.psiInvFun', LinearMap.coe_mk,
    AddHom.coe_mk,
    Basis.tensorProduct_repr_tmul_apply, ← rankOne_lm_smul_smul, ← rankOne_lm_sum_sum, ←
    SMulHomClass.map_smul, ← star_smul, Basis.mulOpposite_repr_apply, ← map_sum, ← star_sum,
    Basis.sum_repr]

theorem Module.Dual.pi.IsFaithfulPosMap.Psi_left_inv [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (t r : ℝ) (x y : PiMat k s) :
    Module.Dual.pi.IsFaithfulPosMap.psiInvFun' hψ t r
        (Module.Dual.pi.IsFaithfulPosMap.psiToFun' hψ t r |x⟩⟨y|) =
      |x⟩⟨y| :=
  by
  rw [Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply,
    Module.Dual.pi.IsFaithfulPosMap.psiInvFun'_apply, op_apply, MulOpposite.unop_op, star_star]
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig, neg_add_self,
    Module.Dual.pi.IsFaithfulPosMap.sig_zero]

theorem Module.Dual.pi.IsFaithfulPosMap.Psi_right_inv [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (t r : ℝ) (x : PiMat k s) (y : (PiMat k s)ᵐᵒᵖ) :
    Module.Dual.pi.IsFaithfulPosMap.psiToFun' hψ t r
        (Module.Dual.pi.IsFaithfulPosMap.psiInvFun' hψ t r (x ⊗ₜ[ℂ] y)) =
      x ⊗ₜ[ℂ] y :=
  by
  rw [Module.Dual.pi.IsFaithfulPosMap.psiInvFun'_apply,
    Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply]
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig, add_neg_self,
    Module.Dual.pi.IsFaithfulPosMap.sig_zero, star_star, op_apply, MulOpposite.op_unop]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
@[simps]
noncomputable def Module.Dual.pi.IsFaithfulPosMap.psi (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (t r : ℝ) : l(PiMat k s) ≃ₗ[ℂ] ((PiMat k s) ⊗[ℂ] (PiMat k s)ᵐᵒᵖ) :=
  letI := hψ
  { toFun := fun x => Module.Dual.pi.IsFaithfulPosMap.psiToFun' hψ t r x
    invFun := fun x => Module.Dual.pi.IsFaithfulPosMap.psiInvFun' hψ t r x
    left_inv := fun x => by
      obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
      simp only [map_sum, Module.Dual.pi.IsFaithfulPosMap.Psi_left_inv]
    right_inv := fun x => by
      obtain ⟨α, β, rfl⟩ := x.eq_span
      simp only [Module.Dual.pi.IsFaithfulPosMap.Psi_right_inv, map_sum]
    map_add' := fun x y => by simp_rw [map_add]
    map_smul' := fun r x => by
      simp_rw [SMulHomClass.map_smul]
      rfl }

theorem Pi.inner_symm [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x y : PiMat k s) :
    ⟪x, y⟫_ℂ = ⟪Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star y), star x⟫_ℂ :=
  by
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq', ← Module.Dual.IsFaithfulPosMap.inner_eq',
    Nontracial.inner_symm (x _)]
  rfl

theorem Module.Dual.pi.IsFaithfulPosMap.sig_adjoint [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    {t : ℝ} :
    LinearMap.adjoint (Module.Dual.pi.IsFaithfulPosMap.sig hψ t : PiMat k s ≃ₐ[ℂ] PiMat k s).toLinearMap =
      (Module.Dual.pi.IsFaithfulPosMap.sig hψ t).toLinearMap :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro x
  simp_rw [LinearMap.adjoint_inner_left, AlgEquiv.toLinearMap_apply,
    Module.Dual.pi.IsFaithfulPosMap.inner_eq', ← Module.Dual.IsFaithfulPosMap.inner_eq',
    Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks, ← AlgEquiv.toLinearMap_apply, ←
    LinearMap.adjoint_inner_left, Module.Dual.IsFaithfulPosMap.sig_adjoint]

theorem Module.Dual.IsFaithfulPosMap.norm_eq {ψ : Module.Dual ℂ (Matrix n n ℂ)}
    [hψ : ψ.IsFaithfulPosMap] (x : Matrix n n ℂ) : ‖x‖ = Real.sqrt (IsROrC.re (ψ (xᴴ * x))) :=
  by simp_rw [InnerProductSpace.Core.norm_eq_sqrt_inner, ← Module.Dual.IsFaithfulPosMap.inner_eq]

theorem Module.Dual.pi.IsFaithfulPosMap.norm_eq {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : Π i, (ψ i).IsFaithfulPosMap] (x : Π i, Matrix (s i) (s i) ℂ) :
    ‖x‖ = Real.sqrt (IsROrC.re (pi ψ (star x * x))) := by
  simp_rw [← Module.Dual.pi.IsFaithfulPosMap.inner_eq]
  exact norm_eq_sqrt_inner _

theorem norm_hMul_norm_eq_norm_tmul {𝕜 B C : Type _} [IsROrC 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] (x : B) (y : C) : ‖x‖ * ‖y‖ = ‖x ⊗ₜ[𝕜] y‖ := by
  calc
    ‖x‖ * ‖y‖ = Real.sqrt (IsROrC.re (inner x x : 𝕜)) * Real.sqrt (IsROrC.re (inner y y : 𝕜)) := by
      simp_rw [@norm_eq_sqrt_inner 𝕜]
    _ = Real.sqrt (IsROrC.re (inner x x : 𝕜) * IsROrC.re (inner y y : 𝕜)) := by
      rw [Real.sqrt_mul inner_self_nonneg]
    _ = Real.sqrt (IsROrC.re ((inner x x : 𝕜) * (inner y y : 𝕜))) :=
      by
      congr 1
      simp only [IsROrC.mul_re, @inner_self_im 𝕜, MulZeroClass.zero_mul, sub_zero]
    _ = Real.sqrt (IsROrC.re (inner (x ⊗ₜ[𝕜] y) (x ⊗ₜ[𝕜] y) : 𝕜)) := by
      rw [TensorProduct.inner_tmul]
    _ = ‖x ⊗ₜ[𝕜] y‖ := by rw [@norm_eq_sqrt_inner 𝕜]

-- instance Matrix.is_fd : FiniteDimensional ℂ (Matrix n n ℂ) := by infer_instance

-- instance Matrix.is_starModule {n : Type _} [Fintype n] [DecidableEq n] :
    -- StarModule ℂ (Matrix n n ℂ) := by infer_instance

-- instance Pi.matrix.is_fd : FiniteDimensional ℂ PiMat k s := by infer_instance

-- instance Pi.matrix.is_starModule : StarModule ℂ PiMat k s := by infer_instance

-- instance Pi.matrix.is_topologicalAddGroup : TopologicalAddGroup (∀ i : k, Matrix (s i) (s i) ℂ) :=
--   by
--   apply @Pi.topologicalAddGroup _ _ _ _ _
  -- intro b
  -- infer_instance

-- instance Pi.matrix.continuousSMul : ContinuousSMul ℂ PiMat k s := by infer_instance

theorem Pi.rankOneLm_real_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x y : PiMat k s) :
    LinearMap.real (rankOneLm x y : (PiMat k s) →ₗ[ℂ] (PiMat k s)) =
      (rankOneLm (star x) (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star y))) :=
  by
  rw [LinearMap.ext_iff]
  intro x_1
  simp_rw [rankOneLm_apply, LinearMap.real_apply, rankOneLm_apply,
    star_smul, ← starRingEnd_apply]
  have := @Pi.inner_symm _ _ _ _ _ _ _ hψ (star x_1) y
  rw [star_star] at this
  rw [← this, inner_conj_symm]

theorem Pi.PosDef.rpow_one_eq_self {Q : PiMat k s} (hQ : ∀ i, (Q i).PosDef) : Pi.PosDef.rpow hQ 1 = Q :=
  by
  ext i
  simp only [Pi.PosDef.rpow, Matrix.PosDef.rpow_one_eq_self]

theorem Pi.PosDef.rpow_neg_one_eq_inv_self {Q : PiMat k s} (hQ : ∀ i, (Q i).PosDef) :
    Pi.PosDef.rpow hQ (-1) = Q⁻¹ := by
  ext i
  simp_rw [Pi.PosDef.rpow, Matrix.PosDef.rpow_neg_one_eq_inv_self (hQ _), Pi.inv_apply]

theorem Module.Dual.pi.IsFaithfulPosMap.inner_left_conj'
    {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (a b c : ∀ i, Matrix (s i) (s i) ℂ) :
    ⟪a, b * c⟫_ℂ = ⟪a * Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star c), b⟫_ℂ := by
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.sig_apply, neg_neg, Pi.PosDef.rpow_one_eq_self,
    Pi.PosDef.rpow_neg_one_eq_inv_self, ← Module.Dual.pi.matrixBlock_apply, ←
    Module.Dual.pi.IsFaithfulPosMap.inner_left_conj]

theorem Module.Dual.pi.IsFaithfulPosMap.inner_right_conj'
    {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (a b c : ∀ i, Matrix (s i) (s i) ℂ) :
    ⟪a * c, b⟫_ℂ = ⟪a, b * Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star c)⟫_ℂ := by
  rw [← inner_conj_symm, Module.Dual.pi.IsFaithfulPosMap.inner_left_conj', inner_conj_symm]

theorem Moudle.Dual.Pi.IsFaithfulPosMap.sig_trans_sig [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x y : ℝ) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ y).trans (Module.Dual.pi.IsFaithfulPosMap.sig hψ x) =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ (x + y) :=
  by
  ext1
  simp_rw [AlgEquiv.trans_apply, Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_comp_sig [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x y : ℝ) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ x).toLinearMap.comp
        (Module.Dual.pi.IsFaithfulPosMap.sig hψ y).toLinearMap =
      (Module.Dual.pi.IsFaithfulPosMap.sig hψ (x + y)).toLinearMap :=
  by
  rw [LinearMap.ext_iff]
  intro x_1
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_zero' [hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
    Module.Dual.pi.IsFaithfulPosMap.sig hψ 0 = 1 :=
  by
  rw [AlgEquiv.ext_iff]
  intros
  rw [Module.Dual.pi.IsFaithfulPosMap.sig_zero]
  rfl

theorem Pi.comp_sig_eq_iff [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (t : ℝ) (f g : PiMat k s →ₗ[ℂ] PiMat k s) :
    f ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ t).toLinearMap = g ↔
      f = g ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-t)).toLinearMap :=
  by
  constructor <;> rintro rfl
  all_goals rw [LinearMap.comp_assoc, Module.Dual.pi.IsFaithfulPosMap.sig_comp_sig]
  on_goal 1 => rw [add_neg_self]
  on_goal 2 => rw [neg_add_self]
  all_goals
    rw [Module.Dual.pi.IsFaithfulPosMap.sig_zero', AlgEquiv.one_toLinearMap, LinearMap.comp_one]

theorem Pi.sig_comp_eq_iff [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (t : ℝ) (f g : PiMat k s →ₗ[ℂ] PiMat k s) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ t).toLinearMap ∘ₗ f = g ↔
      f = (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-t)).toLinearMap ∘ₗ g :=
  by
  constructor <;> rintro rfl
  all_goals rw [← LinearMap.comp_assoc, Module.Dual.pi.IsFaithfulPosMap.sig_comp_sig]
  on_goal 1 => rw [neg_add_self]
  on_goal 2 => rw [add_neg_self]
  all_goals
    rw [Module.Dual.pi.IsFaithfulPosMap.sig_zero', AlgEquiv.one_toLinearMap, LinearMap.one_comp]

theorem rankOneLm_eq_rankOne {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x y : E) : (rankOneLm x y : E →ₗ[𝕜] E) = (rankOne x y : E →L[𝕜] E) :=
  rfl

theorem LinearMap.pi.adjoint_real_eq {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (f : PiMat k s →ₗ[ℂ] PiMat k s) :
    (LinearMap.adjoint f).real =
      (Module.Dual.pi.IsFaithfulPosMap.sig hψ 1).toLinearMap ∘ₗ
        (LinearMap.adjoint f.real) ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1)).toLinearMap :=
  by
  rw [← ext_inner_map]
  intro u
  nth_rw 1 [Pi.inner_symm]
  simp_rw [LinearMap.real_apply, star_star, LinearMap.adjoint_inner_right]
  nth_rw 1 [Pi.inner_symm]
  simp_rw [star_star, ← Module.Dual.pi.IsFaithfulPosMap.sig_star, ← LinearMap.real_apply f,
    LinearMap.comp_apply, ← LinearMap.adjoint_inner_left f.real, ← AlgEquiv.toLinearMap_apply, ←
    LinearMap.adjoint_inner_left (Module.Dual.pi.IsFaithfulPosMap.sig hψ 1).toLinearMap,
    Module.Dual.pi.IsFaithfulPosMap.sig_adjoint]

end DirectSum
