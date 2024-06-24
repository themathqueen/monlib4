/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Ips.RankOne
-- import Monlib.LinearAlgebra.MyIps.Functional
import Monlib.LinearAlgebra.Nacgor
import Mathlib.RingTheory.Coalgebra.Basic
import Monlib.LinearAlgebra.Ips.MulOp
import Monlib.LinearAlgebra.Ips.TensorHilbert
import Monlib.LinearAlgebra.CoalgebraFiniteDimensional
import Monlib.LinearAlgebra.LmulRmul
import Monlib.LinearAlgebra.IsReal
import Monlib.LinearAlgebra.TensorFinite
import Monlib.LinearAlgebra.tensorProduct
import Mathlib.LinearAlgebra.Trace

#align_import linear_algebra.my_ips.quantum_set

/-!

# Quantum Set

This file defines the structure of a quantum set.

A quantum set is defined as a star-algebra `A` over `ℂ` with a positive element `Q` such that
  `Q` is invertible and a sum of rank-one operators (in other words, positive definite).
The quantum set is also equipped with a faithful positive linear functional `φ` on `A`,
  which is used to define the inner product on `A`, i.e., `⟪x, y⟫_ℂ = φ (star x * y)`.
The quantum set is also equipped with a `trace` functional on `A` such that `φ x = trace (Q * x)`.

## Main definitions

* `quantum_set A` is a structure that defines a quantum set.
* `quantum_set.mod_aut A t` defines the modular automorphism of a quantum set, which is
  a family of automorphisms of `A` parameterized by `t : ℝ`, given by `x ↦ Q^(-t) * x * Q^t`,
  where `Q` is the unique positive definite element in `A` given by the quantum set structure.

-/

@[reducible]
class InnerProductAlgebra (A : Type*) [NormedAddCommGroupOfRing A]
  extends InnerProductSpace ℂ A, Algebra ℂ A where --Module.Finite ℂ A where
attribute [instance] InnerProductAlgebra.toInnerProductSpace
attribute [instance] InnerProductAlgebra.toAlgebra
-- attribute [instance] InnerProductAlgebra.toFinite

@[reducible]
class InnerProductStarAlgebra (A : Type*) [NormedAddCommGroupOfRing A]
  extends InnerProductAlgebra A, StarRing A, StarModule ℂ A where
attribute [instance] InnerProductStarAlgebra.toInnerProductAlgebra
attribute [instance] InnerProductStarAlgebra.toStarRing
attribute [instance] InnerProductStarAlgebra.toStarModule

-- attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass
open Coalgebra in
@[reducible]
class QuantumSet (A : Type _) [NormedAddCommGroupOfRing A]
  extends
    InnerProductStarAlgebra A,
    Module.Finite ℂ A
    -- NormedAddCommGroupOfRing A,
    -- InnerProductSpace ℂ A,
    -- -- Algebra ℂ A,
    -- StarRing A,
    -- StarModule ℂ A,
    -- SMulCommClass ℂ A A,
    -- IsScalarTower ℂ A A,
    -- Module.Finite ℂ A
    -- PartialOrder A,
    -- Coalgebra ℂ A,
    -- Semiring A,
    -- StarOrderedRing A,
    -- Algebra ℂ A,
      where
    -- isScalarTower ℂ A A
    -- /-- the inner product is given by `⟪·,·⟫ := counit (star · * ·)` -/
    -- inner_eq : ∀ x y : A, ⟪x, y⟫_ℂ = Coalgebra.counit (star x * y)
    /-- the modular automorphism `σ _` as a linear isomorphism `A ≃ₗ[ℂ] A` -/
    modAut : Π _ : ℝ, A ≃ₐ[ℂ] A
    -- /-- the module automorphism is also an algebra isomorphism -/
    -- modAut_map_mul : ∀ (r : ℝ) (x y : A), modAut r (x * y) = modAut r x * modAut r y
    -- modAut_map_one : ∀ r, modAut r 1 = 1
    -- modAux :=
    /-- the modular automorphism is an additive homomorphism from `ℝ` to
      `(A ≃ₐ[ℂ] A, add := · * ·, zero := 1)` -/
    modAut_trans : ∀ r s, (modAut r).trans (modAut s) = modAut (r + s)
    modAut_zero : modAut 0 = 1
    /-- applying star to `modAut r x` will give `modAut (-r) (star x)` -/
    modAut_star : ∀ r x, star (modAut r x) = modAut (-r) (star x)
    /-- the modular automorphism is also a coalgebra homomorphism -/
    modAut_isCoalgHom : ∀ r, (modAut r).toLinearMap.IsCoalgHom
    /-- the modular automorphism is symmetric with respect to the inner product,
      in other words, it is self-adjoint -/
    modAut_isSymmetric : ∀ r x y, ⟪modAut r x, y⟫_ℂ = ⟪x, modAut r y⟫_ℂ
    inner_star_left : ∀ x y z : A, ⟪x * y, z⟫_ℂ = ⟪y, star x * z⟫_ℂ
    inner_conj_left : ∀ x y z : A, ⟪x * y, z⟫_ℂ = ⟪x, z * modAut (-1) (star y)⟫_ℂ
    n : Type*
    n_isFintype : Fintype n
    n_isDecidableEq : DecidableEq n
    /-- fix an orthonormal basis on `A` -/
    onb : OrthonormalBasis n ℂ A

-- attribute [instance] QuantumSet.toNormedAddCommGroupOfRing
-- attribute [instance] QuantumSet.toInnerProductSpace
-- attribute [instance] QuantumSet.toPartialOrder
-- attribute [instance] QuantumSet.toStarOrderedRing
-- attribute [instance] QuantumSet.toSMulCommClass
-- attribute [instance] QuantumSet.toIsScalarTower
attribute [instance] QuantumSet.toInnerProductStarAlgebra
attribute [instance] QuantumSet.n_isFintype
attribute [instance] QuantumSet.n_isDecidableEq
attribute [instance] QuantumSet.toFinite
-- attribute [instance] QuantumSet.toCoalgebra
-- attribute [simp] QuantumSet.inner_eq
attribute [simp] QuantumSet.modAut_trans
-- attribute [simp] QuantumSet.modAut_map_mul
-- attribute [simp] QuantumSet.modAut_map_one
attribute [simp] QuantumSet.modAut_zero
attribute [simp] QuantumSet.inner_star_left
attribute [simp] QuantumSet.inner_conj_left
attribute [simp] QuantumSet.modAut_isSymmetric

export QuantumSet (modAut n onb)

-- instance QuantumSet.toAlgebra {A : Type*} [NormedAddCommGroupOfRing A] [QuantumSet A] :
--   Algebra ℂ A :=
-- Algebra.ofIsScalarTowerSmulCommClass

-- instance QuantumSet.toFiniteDimensionalHilbertAlgebra {A : Type*} [QuantumSet A] :
--   FiniteDimensionalHilbertAlgebra ℂ A :=
-- by infer_instance

variable {A B : Type _} [NormedAddCommGroupOfRing B] [NormedAddCommGroupOfRing A]
  [hA : QuantumSet A] [hB : QuantumSet B]
theorem lmul_adjoint (a : B) :
    LinearMap.adjoint (lmul a : B →ₗ[ℂ] B) = lmul (star a) :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro u
  simp_rw [LinearMap.adjoint_inner_left, lmul_apply, hB.inner_star_left, star_star]

lemma QuantumSet.inner_eq_counit' :
  (⟪(1 : B), ·⟫_ℂ) = Coalgebra.counit :=
by
  simp_rw [Coalgebra.counit]
  ext
  apply ext_inner_left ℂ
  intro a
  simp_rw [LinearMap.adjoint_inner_right, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, inner_smul_left, inner]

lemma QuantumSet.inner_eq_counit (x y : B) :
  ⟪x, y⟫_ℂ = Coalgebra.counit (star x * y) :=
calc ⟪x, y⟫_ℂ = ⟪x * 1, y⟫_ℂ := by rw [mul_one]
  _ = ⟪(1 : B), star x * y⟫_ℂ := hB.inner_star_left x 1 y
  _ = Coalgebra.counit (star x * y) := by rw [← inner_eq_counit']

theorem rmul_adjoint (a : B) :
    LinearMap.adjoint (rmul a : B →ₗ[ℂ] B) = rmul (hB.modAut (-1) (star a)) :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro u
  simp_rw [LinearMap.adjoint_inner_left, rmul_apply]
  nth_rw 1 [← inner_conj_symm]
  rw [hB.inner_conj_left, inner_conj_symm]

@[simp]
theorem QuantumSet.modAut_apply_modAut (t r : ℝ) (a : A) :
  hA.modAut t (hA.modAut r a) = hA.modAut (t + r) a :=
by
  rw [← AlgEquiv.trans_apply, modAut_trans, add_comm]

lemma QuantumSet.inner_conj (a b : A) :
  ⟪a, b⟫_ℂ = ⟪star b, (hA.modAut (-1) (star a))⟫_ℂ :=
calc ⟪a, b⟫_ℂ = ⟪1 * a, b⟫_ℂ := by rw [one_mul]
  _ = ⟪1, b * hA.modAut (-1) (star a)⟫_ℂ := by rw [inner_conj_left]
  _ = starRingEnd ℂ ⟪b * hA.modAut (-1) (star a), 1⟫_ℂ := by rw [inner_conj_symm]
  _ = starRingEnd ℂ ⟪hA.modAut (-1) (star a), star b⟫_ℂ := by rw [inner_star_left, mul_one]
  _ = ⟪star b, hA.modAut (-1) (star a)⟫_ℂ := by rw [inner_conj_symm]
lemma QuantumSet.inner_conj' (a b : A) :
  ⟪a, b⟫_ℂ = ⟪hA.modAut (-1) (star b), star a⟫_ℂ :=
calc ⟪a, b⟫_ℂ = starRingEnd ℂ ⟪b, a⟫_ℂ := by rw [inner_conj_symm]
  _ = starRingEnd ℂ ⟪star a, hA.modAut (-1) (star b)⟫_ℂ := by rw [inner_conj]
  _ = ⟪hA.modAut (-1) (star b), star a⟫_ℂ := by rw [inner_conj_symm]
lemma QuantumSet.inner_conj'' (a b : A) :
  ⟪a, b⟫_ℂ = ⟪hA.modAut (- (1/2)) (star b), hA.modAut (- (1 / 2)) (star a)⟫_ℂ :=
calc ⟪a, b⟫_ℂ = starRingEnd ℂ ⟪b, a⟫_ℂ := by rw [inner_conj_symm]
  _ = starRingEnd ℂ ⟪star a, hA.modAut (-1) (star b)⟫_ℂ := by rw [inner_conj]
  _ = ⟪hA.modAut (-1) (star b), star a⟫_ℂ := by rw [inner_conj_symm]
  _ = ⟪hA.modAut (-(1/2)) (hA.modAut (-(1/2)) (star b)), star a⟫_ℂ := by
    rw [modAut_apply_modAut]; norm_num
  _ = ⟪hA.modAut (- (1/2)) (star b), hA.modAut (- (1 / 2)) (star a)⟫_ℂ := by rw [modAut_isSymmetric]

namespace QuantumSet
open scoped TensorProduct
noncomputable
def Psi_toFun
  (t r : ℝ) :
  (A →ₗ[ℂ] B) →ₗ[ℂ] (B ⊗[ℂ] Aᵐᵒᵖ) where
  toFun x :=
    ∑ a, ∑ b,
      (LinearMap.toMatrix hA.onb.toBasis hB.onb.toBasis) x a b •
        hB.modAut t (hB.onb a) ⊗ₜ[ℂ] MulOpposite.op (star (hA.modAut r (hA.onb b)))
  map_add' x y := by simp_rw [map_add, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [_root_.map_smul, Matrix.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

theorem Psi_toFun_apply
    (t r : ℝ) (b : A) (a : B) :
    Psi_toFun t r (rankOne ℂ a b).toLinearMap =
      hB.modAut t a ⊗ₜ[ℂ] MulOpposite.op (star (hA.modAut r b)) :=
  by
  simp_rw [Psi_toFun, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_right, OrthonormalBasis.coe_toBasis,
    mul_comm ⟪b, _⟫_ℂ, ← TensorProduct.smul_tmul_smul, ← MulOpposite.op_smul,
    ← inner_conj_symm b, starRingEnd_apply, ← star_smul,
    ← _root_.map_smul, ← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul,
    ← Finset.op_sum, ← star_sum, ← map_sum, ← OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.sum_repr]

local notation "|" a "⟩⟨" b "|" => @rankOne ℂ _ _ _ _ _ _ _ a b
noncomputable
def Psi_invFun (t r : ℝ) :
  (A ⊗[ℂ] Bᵐᵒᵖ) →ₗ[ℂ] (B →ₗ[ℂ] A)
  where
  toFun x :=
    ∑ a, ∑ b,
      (hA.onb.toBasis.tensorProduct hB.onb.toBasis.mulOpposite).repr x (a, b) •
        (↑|hA.modAut (-t) (hA.onb a)⟩⟨hB.modAut (-r) (star (hB.onb b))|)
  map_add' x y := by simp_rw [_root_.map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [_root_.map_smul, Finsupp.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

theorem Psi_invFun_apply (t r : ℝ) (x : A) (y : Bᵐᵒᵖ) :
    Psi_invFun t r (x ⊗ₜ[ℂ] y) =
      |hA.modAut (-t) x⟩⟨hB.modAut (-r) (star (MulOpposite.unop y))| :=
  by
  simp_rw [Psi_invFun, LinearMap.coe_mk, AddHom.coe_mk,
    Basis.tensorProduct_repr_tmul_apply, ← rankOne_lm_smul_smul, ← rankOne_lm_sum_sum, ←
    _root_.map_smul, ← star_smul, Basis.mulOpposite_repr_apply, ← map_sum, ← star_sum,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.sum_repr]

theorem Psi_left_inv (t r : ℝ) (x : A) (y : B) :
    Psi_invFun t r (Psi_toFun t r |x⟩⟨y|) = (|x⟩⟨y|).toLinearMap :=
  by
  simp_rw [Psi_toFun_apply, Psi_invFun_apply, MulOpposite.unop_op, star_star, modAut_apply_modAut,
    add_left_neg, modAut_zero]
  simp only [AlgEquiv.one_apply]

theorem Psi_right_inv (t r : ℝ) (x : A) (y : Bᵐᵒᵖ) :
    Psi_toFun t r (Psi_invFun t r (x ⊗ₜ[ℂ] y)) = x ⊗ₜ[ℂ] y :=
  by
  rw [Psi_invFun_apply, Psi_toFun_apply]
  simp_rw [modAut_apply_modAut, add_neg_self, modAut_zero]
  simp only [AlgEquiv.one_apply, star_star, MulOpposite.op_unop]

@[simps]
noncomputable def Psi
    (t r : ℝ) : (A →ₗ[ℂ] B) ≃ₗ[ℂ] (B ⊗[ℂ] Aᵐᵒᵖ) :=
{ toFun := fun x => Psi_toFun t r x
  invFun := fun x => Psi_invFun t r x
  left_inv := fun x => by
    obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
    simp only [map_sum, Psi_left_inv]
  right_inv := fun x => by
    obtain ⟨α, β, rfl⟩ := x.eq_span
    simp only [Psi_right_inv, map_sum]
  map_add' := fun x y => by simp_rw [map_add]
  map_smul' := fun r x => by
    simp_rw [_root_.map_smul]
    rfl }

end QuantumSet

open QuantumSet
theorem LinearMap.adjoint_real_eq (f : A →ₗ[ℂ] B) :
    (LinearMap.adjoint f).real =
      (hA.modAut 1).toLinearMap ∘ₗ
        (LinearMap.adjoint f.real) ∘ₗ (hB.modAut (-1)).toLinearMap :=
  by
  rw [LinearMap.ext_iff]
  intro x
  apply ext_inner_right ℂ
  intro u
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
  nth_rw 1 [inner_conj']
  simp_rw [LinearMap.real_apply, star_star, LinearMap.adjoint_inner_right, modAut_isSymmetric,
    LinearMap.adjoint_inner_left, LinearMap.real_apply, modAut_star]
  nth_rw 1 [inner_conj']
  rw [star_star]

local notation "|" a "⟩⟨" b "|" => @rankOne ℂ _ _ _ _ _ _ _ a b

lemma rankOne_real (a : A) (b : B) :
  LinearMap.real |a⟩⟨b| = (|star a⟩⟨hB.modAut (-1) (star b)|).toLinearMap :=
by
  ext x
  simp only [ContinuousLinearMap.coe_coe, LinearMap.real_apply, rankOne_apply, star_smul]
  rw [QuantumSet.inner_conj, star_star]
  simp only [← starRingEnd_apply, inner_conj_symm]

open LinearMap in
lemma _root_.QuantumSet.rTensor_mul_comp_lTensor_comul_eq_comul_comp_mul :
  rTensor A (mul' ℂ A) ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap ∘ₗ lTensor A (Coalgebra.comul)
   = Coalgebra.comul ∘ₗ mul' ℂ A :=
by
  rw [Coalgebra.comul_eq_mul_adjoint, Coalgebra.rTensor_mul_comp_lTensor_mul_adjoint]
  exact fun x y z ↦ inner_star_left x y z
open LinearMap in
lemma _root_.QuantumSet.lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul :
  lTensor A (mul' ℂ A) ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ rTensor A (Coalgebra.comul)
   = Coalgebra.comul ∘ₗ mul' ℂ A :=
by
  rw [Coalgebra.comul_eq_mul_adjoint, Coalgebra.lTensor_mul_comp_rTensor_mul_adjoint_of]
  exact fun x y z ↦ inner_star_left x y z

noncomputable def _root_.QuantumSet.isFrobeniusAlgebra :
    FrobeniusAlgebra ℂ A where
  lTensor_mul_comp_rTensor_comul_commute := by
    rw [lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul,
      rTensor_mul_comp_lTensor_comul_eq_comul_comp_mul]

open scoped TensorProduct
open LinearMap in
-- set_option synthInstance.maxHeartbeats 200000 in
theorem _root_.QuantumSet.rTensor_counit_mul_comp_comm_comp_rTensor_comul_unit_eq_modAut_one :
  (TensorProduct.lid ℂ A).toLinearMap
    ∘ₗ rTensor A (Coalgebra.counit ∘ₗ mul' ℂ A)
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
    ∘ₗ lTensor A (TensorProduct.comm ℂ _ _).toLinearMap
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap
    ∘ₗ rTensor A (Coalgebra.comul ∘ₗ Algebra.linearMap ℂ A)
    ∘ₗ (TensorProduct.lid ℂ A).symm.toLinearMap
  = (hA.modAut 1).toLinearMap :=
by
  ext
  apply ext_inner_left ℂ
  intro
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.lid_symm_apply,
    rTensor_tmul, Algebra.linearMap_apply, map_one, AlgEquiv.toLinearMap_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul 1 : A ⊗[ℂ] A)
  simp_rw [← h, TensorProduct.sum_tmul, map_sum, inner_sum]
  simp only [TensorProduct.assoc_tmul, lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul, rTensor_tmul,
    LinearMap.comp_apply, mul'_apply, ← inner_eq_counit', TensorProduct.lid_tmul,
    inner_smul_right, ← inner_conj_symm (1 : A), inner_conj_left, one_mul]
  simp_rw [inner_conj_symm, ← TensorProduct.inner_tmul, ← inner_sum, h,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_right, mul'_apply,
    inner_star_left, modAut_star, neg_neg, mul_one, star_star]

open LinearMap in
theorem _root_.QuantumSet.lTensor_counit_mul_comp_comm_comp_lTensor_comul_unit_eq_modAut_neg_one :
  (TensorProduct.rid ℂ A).toLinearMap
    ∘ₗ lTensor A (Coalgebra.counit ∘ₗ mul' ℂ A)
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap
    ∘ₗ rTensor A (TensorProduct.comm ℂ _ _).toLinearMap
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
    ∘ₗ lTensor A (Coalgebra.comul ∘ₗ Algebra.linearMap ℂ A)
    ∘ₗ (TensorProduct.rid ℂ A).symm.toLinearMap
  = (hA.modAut (-1)).toLinearMap :=
by
  ext
  apply ext_inner_left ℂ
  intro
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.rid_symm_apply,
    lTensor_tmul, Algebra.linearMap_apply, map_one, AlgEquiv.toLinearMap_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul 1 : A ⊗[ℂ] A)
  simp_rw [← h, TensorProduct.tmul_sum, map_sum, inner_sum]
  simp only [TensorProduct.assoc_tmul, lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul, rTensor_tmul,
    LinearMap.comp_apply, mul'_apply, ← inner_eq_counit', TensorProduct.rid_tmul,
    inner_smul_right, ← inner_conj_symm (1 : A), inner_star_left, mul_one]
  simp_rw [inner_conj_symm, mul_comm, ← TensorProduct.inner_tmul, ← inner_sum, h,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_right, mul'_apply,
    inner_conj_left, one_mul, star_star]

open LinearMap in
lemma _root_.QuantumSet.counit_tensor_star_left_eq_bra (x : A) :
  Coalgebra.counit ∘ mul' ℂ A ∘ (star x ⊗ₜ[ℂ] ·) = bra ℂ x :=
by
  ext
  simp only [Function.comp_apply, mul'_apply, innerSL_apply]
  exact Eq.symm (inner_eq_counit _ _)
open LinearMap in
lemma _root_.QuantumSet.mul_comp_tensor_left_unit_eq_ket (x : A) :
  mul' ℂ A ∘ (x ⊗ₜ[ℂ] ·) ∘ Algebra.linearMap ℂ A = ket ℂ x :=
by
  ext
  simp only [Function.comp_apply, Algebra.linearMap_apply, mul'_apply, ket_toFun_toFun,
    Algebra.algebraMap_eq_smul_one, mul_smul_one]
open LinearMap in
lemma _root_.QuantumSet.rTensor_bra_comul_unit_eq_ket_star (x : A) :
  (TensorProduct.lid ℂ _).toLinearMap
    ∘ₗ (rTensor A (bra ℂ x)) ∘ₗ Coalgebra.comul ∘ₗ Algebra.linearMap ℂ A
  = ket ℂ (star x) :=
by
  ext
  apply ext_inner_left ℂ
  intro
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Algebra.linearMap_apply, map_one,
    ContinuousLinearMap.coe_coe, ket_toFun_toFun, one_smul]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul 1 : A ⊗[ℂ] A)
  simp_rw [← h, map_sum, inner_sum, rTensor_tmul, ContinuousLinearMap.coe_coe, bra_apply_apply,
    TensorProduct.lid_tmul, inner_smul_right, ← TensorProduct.inner_tmul, ← inner_sum,
    h, Coalgebra.comul_eq_mul_adjoint, adjoint_inner_right, mul'_apply, inner_star_left, mul_one]
open LinearMap in

open LinearMap in
lemma _root_.QuantumSet.counit_mul_rTensor_ket_eq_bra_star (x : A) :
  Coalgebra.counit ∘ₗ mul' ℂ A ∘ₗ (rTensor A (ket ℂ x)) ∘ₗ (TensorProduct.lid ℂ _).symm.toLinearMap
  = bra ℂ (star x) :=
by
  rw [← ket_adjoint_eq_bra, ← ContinuousLinearMap.linearMap_adjoint,
    ← rTensor_bra_comul_unit_eq_ket_star]
  simp_rw [adjoint_comp, Coalgebra.counit_eq_unit_adjoint, Coalgebra.comul_eq_mul_adjoint,
    LinearMap.adjoint_adjoint, TensorProduct.lid_adjoint, rTensor_adjoint,
    ContinuousLinearMap.linearMap_adjoint, bra_adjoint_eq_ket, comp_assoc]
  congr
  ext; rfl

theorem ket_real {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
  [StarAddMonoid A] [StarModule 𝕜 A] (x : A) :
  LinearMap.real (ket 𝕜 x) = (ket 𝕜 (star x)).toLinearMap :=
by
  ext
  simp only [LinearMap.real_apply, star_one, ContinuousLinearMap.coe_coe,
    ket_one_apply]
theorem bra_real (x : A) :
  LinearMap.real (bra ℂ x) = (bra ℂ (hA.modAut (-1) (star x))).toLinearMap :=
by
  ext
  simp only [LinearMap.real_apply, ContinuousLinearMap.coe_coe,
    bra_apply_apply, RCLike.star_def, inner_conj_symm]
  rw [QuantumSet.inner_conj, star_star, modAut_isSymmetric]

theorem ket_toMatrix {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
  {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 A) (x : A) :
  LinearMap.toMatrix (Basis.singleton Unit 𝕜) b (ket 𝕜 x) = Matrix.col (b.repr x) :=
by
  ext
  simp only [Matrix.col_apply, LinearMap.toMatrix_apply,
    Basis.singleton_apply, ContinuousLinearMap.coe_coe, ket_toFun_toFun, one_smul]
open scoped Matrix
theorem bra_toMatrix {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 A) (x : A) :
  LinearMap.toMatrix b.toBasis (Basis.singleton Unit 𝕜) (bra 𝕜 x) = (Matrix.col (b.repr x))ᴴ :=
by
  ext
  simp only [Matrix.conjTranspose_col, Matrix.row_apply, Pi.star_apply, RCLike.star_def,
    LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,
    innerSL_apply, Basis.singleton_repr, OrthonormalBasis.repr_apply_apply, inner_conj_symm]

open Matrix in
theorem lmul_toMatrix_apply {n : Type*} [Fintype n] [DecidableEq n]
  (x : n → ℂ) (i j : n) :
  LinearMap.toMatrix' (LinearMap.mulLeft ℂ x) i j
    = ite (i = j) (x i) 0 :=
by
  simp_rw [LinearMap.toMatrix'_apply, LinearMap.mulLeft_apply, Pi.mul_apply, mul_boole]

theorem rankOne_trace {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
  [Module.Finite 𝕜 A] (x y : A) :
  LinearMap.trace 𝕜 A (rankOne 𝕜 x y).toLinearMap = ⟪y, x⟫_𝕜 :=
by
  rw [← ket_bra_eq_rankOne, ContinuousLinearMap.coe_comp, LinearMap.trace_comp_comm',
    ← ContinuousLinearMap.coe_comp, bra_ket_apply]
  rw [LinearMap.trace_eq_matrix_trace 𝕜 (Basis.singleton Unit 𝕜),
    ket_toMatrix, Matrix.trace]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Matrix.diag_apply, Matrix.col_apply,
    Basis.singleton_repr, Finset.sum_const, Finset.card_singleton, one_smul]

lemma _root_.LinearMap.apply_eq_id {R M : Type*} [Semiring R] [AddCommMonoid M]
  [Module R M] {f : M →ₗ[R] M} :
  (∀ x, f x = x) ↔ f = 1 :=
by simp_rw [LinearMap.ext_iff, LinearMap.one_apply]

theorem _root_.QuantumSet.starAlgEquiv_is_isometry_tfae
    (f : B ≃⋆ₐ[ℂ] B) :
    List.TFAE
      [LinearMap.adjoint f.toLinearMap =
          f.symm.toLinearMap,
        Coalgebra.counit ∘ₗ f.toLinearMap = Coalgebra.counit,
        ∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ,
        ∀ x : B, ‖f x‖ = ‖x‖] :=
by
  tfae_have 4 ↔ 1
  · have : ∀ x : B, ‖x‖ = Real.sqrt (RCLike.re ⟪x, x⟫_ℂ) :=
    fun x => norm_eq_sqrt_inner _
    have this' : ∀ x : B, (RCLike.re ⟪x, x⟫_ℂ : ℂ) = ⟪x, x⟫_ℂ :=
    fun x => inner_self_re _
    simp_rw [this, Real.sqrt_inj inner_self_nonneg inner_self_nonneg,
      ← Complex.ofReal_inj, this', ← @sub_eq_zero _ _ _ ⟪_, _⟫_ℂ]
    have :
      ∀ x y,
        ⟪f x, f y⟫_ℂ - ⟪x, y⟫_ℂ =
          ⟪(LinearMap.adjoint f.toLinearMap ∘ₗ f.toLinearMap - 1) x, y⟫_ℂ :=
      by
      intro x y
      simp only [LinearMap.sub_apply, LinearMap.one_apply, inner_sub_left, LinearMap.comp_apply,
        LinearMap.adjoint_inner_left, StarAlgEquiv.toLinearMap_apply]
    simp_rw [this, inner_map_self_eq_zero, sub_eq_zero, StarAlgEquiv.comp_eq_iff,
      LinearMap.one_comp]
  rw [tfae_4_iff_1]
  tfae_have 3 ↔ 2
  · simp_rw [QuantumSet.inner_eq_counit, ← map_star f, ← _root_.map_mul f,
      LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply]
    refine' ⟨fun h x => _, fun h x y => h _⟩
    rw [← one_mul x, ← star_one]
    exact h _ _
  rw [← tfae_3_iff_2]
  simp_rw [← StarAlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_left,
    ← ext_inner_left_iff, ← LinearMap.comp_apply, _root_.LinearMap.apply_eq_id,
    StarAlgEquiv.comp_eq_iff, LinearMap.one_comp]
  tfae_finish


open scoped TensorProduct
-- noncomputable instance {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B] [QuantumSet A]
--   [QuantumSet B] :
--     NormedAddCommGroupOfRing (A ⊗[ℂ] B) where

-- noncomputable instance TensorProduct.innerProductAlgebra {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B] [QuantumSet A]
--   [QuantumSet B] :
--     InnerProductAlgebra (A ⊗[ℂ] B) where
--   toFun x := Algebra.toRingHom x
--   map_one' := RingHom.map_one Algebra.toRingHom
--   map_mul' x y := RingHom.map_mul Algebra.toRingHom x y
--   map_zero' := RingHom.map_zero Algebra.toRingHom
--   map_add' x y := RingHom.map_add Algebra.toRingHom x y
--   commutes' _ _ := Algebra.commutes' _ _
--   smul_def' _ _ := Algebra.smul_def' _ _

-- -- not `rfl`... need to change the def of `InnerProductAlgebra` so that it
-- -- takes in the algebra and extends the inner product only
--nvm... just changed the above instance
-- example {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B] [QuantumSet A]
--   [QuantumSet B] :
--   (TensorProduct.innerProductAlgebra.toAlgebra : Algebra ℂ (A ⊗[ℂ] B))
--   = (Algebra.TensorProduct.instAlgebra : Algebra ℂ (A ⊗[ℂ] B)) :=
-- rfl
-- by ext; simp only

-- noncomputable instance {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B] [QuantumSet A]
--   [QuantumSet B] :
--     StarRing (A ⊗[ℂ] B) where
--   star_add x y := TensorProduct.star_add _ _
--   star_mul x y :=
--     x.induction_on
--       (by simp only [zero_mul, star_zero, mul_zero])
--       (fun a b => y.induction_on
--         (by simp only [star_zero, zero_mul, mul_zero])
--         (fun c d => by simp only [Algebra.TensorProduct.tmul_mul_tmul,
--           TensorProduct.star_tmul, star_mul])
--         (fun c d h h2 => by simp only [mul_add, star_add, h, h2, add_mul]))
--       (fun x y hx hy => by
--         simp only [add_mul, mul_add, star_add, hx, hy])

local notation
  f " ⊗ₘ " g => TensorProduct.map f g

lemma AlgEquiv.TensorProduct.map_toLinearMap
    {R : Type _} [CommSemiring R] {A B C D : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) :
  (AlgEquiv.TensorProduct.map f g).toLinearMap = f.toLinearMap ⊗ₘ g.toLinearMap :=
rfl
lemma AlgEquiv.TensorProduct.map_map_toLinearMap
  {R : Type _} [CommSemiring R] {A B C D E F : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Semiring E] [Semiring F]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R F]
    (h : B ≃ₐ[R] E) (i : D ≃ₐ[R] F) (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x : A ⊗[R] C) :
  (AlgEquiv.TensorProduct.map h i) ((AlgEquiv.TensorProduct.map f g) x)
    = (AlgEquiv.TensorProduct.map (f.trans h) (g.trans i)) x :=
by
  simp only [TensorProduct.map, toAlgHom_eq_coe, coe_mk, Algebra.TensorProduct.map_apply_map_apply]
  rfl

lemma AlgEquiv.op_trans {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
  (AlgEquiv.op f).trans (AlgEquiv.op g) = AlgEquiv.op (f.trans g) :=
rfl
@[simp]
lemma AlgEquiv.op_one {R A : Type*} [CommSemiring R] [Semiring A]
  [Algebra R A] :
  AlgEquiv.op (1 : A ≃ₐ[R] A) = 1 :=
rfl

@[simp]
lemma AlgEquiv.TensorProduct.map_one {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] :
  AlgEquiv.TensorProduct.map (1 : A ≃ₐ[R] A) (1 : B ≃ₐ[R] B) = 1 :=
by
  rw [AlgEquiv.ext_iff]
  simp_rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.ext_iff]
  simp only [map_toLinearMap, one_toLinearMap, _root_.TensorProduct.map_one]

-- noncomputable instance {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B] [hA : QuantumSet A]
--   [hB : QuantumSet B] :
--     QuantumSet (A ⊗[ℂ] B) where
--   out := by
--     refine Module.finite_def.mp ?_
--     exact Module.Finite.tensorProduct ℂ A B
--   modAut r := AlgEquiv.TensorProduct.map (hA.modAut r) (hB.modAut r)
--   modAut_trans r s := by
--     simp only [AlgEquiv.ext_iff, ← AlgEquiv.toLinearMap_apply, ← LinearMap.ext_iff]
--     rw [TensorProduct.ext_iff]
--     intro a b
--     simp only [AlgEquiv.trans_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.TensorProduct.map]
--     simp only [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_mk, Algebra.TensorProduct.map_tmul,
--       AlgHom.coe_coe, modAut_apply_modAut, add_comm]
--   modAut_zero := by
--     simp only [modAut_zero, AlgEquiv.TensorProduct.map_one]
--   modAut_star r x :=
--     x.induction_on
--       (by simp only [map_zero, star_zero])
--       (fun c d => by simp only [AlgEquiv.TensorProduct.map]; simp only [AlgEquiv.toAlgHom_eq_coe,
--         AlgEquiv.coe_mk, Algebra.TensorProduct.map_tmul, AlgHom.coe_coe,
--         TensorProduct.star_tmul, QuantumSet.modAut_star])
--       (fun x y hx hy => by
--         simp only [map_add, hx, hy, star_add])
  -- onb := hA.onb.tensorProduct hB.onb


-- attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass
-- open QuantumSet

-- instance (A : Type _) [QuantumSet A] :
--   AddZeroClass (A ≃ₐ[ℂ] A) :=
-- { zero := (1 : A ≃ₐ[ℂ] A)
--   add := (· * ·)
--   zero_add := λ x => by rfl
--   add_zero := λ x => by rfl }

-- -- @[simps]
-- def modAut' (A : Type _) [QuantumSet A] :
--   ℝ →+ (A ≃ₐ[ℂ] A) :=
-- { toFun := modAut
--   map_zero' := by simp only [modAut_zero]; rfl
--   map_add' := λ _ _ => modAut_mul _ _ }

--   let A_pos := QuantumSet.APos A
--   let Q : A_pos := QuantumSet.q
--   { toFun := fun x => ((Q ^ (-t) : A_pos) : A) * x * ((Q ^ t : A_pos) : A)
--     invFun := fun x => (Q ^ t : A_pos) * x * (Q ^ (-t) : A_pos)
--     left_inv := fun x => by
--       calc
--         ↑(Q ^ t) * ((Q ^ (-t) : A_pos) * x * (Q ^ t : A_pos)) * ↑(Q ^ (-t) : A_pos) =
--             (Q ^ t : A_pos) * (Q ^ t : A_pos)⁻¹ * x * (↑(Q ^ t) * ↑(Q ^ t)⁻¹) :=
--           by simp_rw [mul_assoc, APos_pow_neg Q]
--         _ = ↑(Q ^ (t + -t)) * x * ↑(Q ^ (t + -t)) := by rw [← APos_pow_neg, APos_pow_mul]
--         _ = x := by simp_rw [add_neg_self, APos_pow_zero Q, one_mul, mul_one]
--     right_inv := fun x => by
--       calc
--         ↑(Q ^ (-t)) * (↑(Q ^ t) * x * ↑(Q ^ (-t))) * ↑(Q ^ t) =
--             ↑(Q ^ t)⁻¹ * ↑(Q ^ t) * x * (↑(Q ^ t)⁻¹ * ↑(Q ^ t)) :=
--           by simp only [mul_assoc, APos_pow_neg Q]
--         _ = ↑(Q ^ (-t + t)) * x * ↑(Q ^ (-t + t)) := by simp_rw [← APos_pow_neg Q, APos_pow_mul Q]
--         _ = x := by simp_rw [neg_add_self, APos_pow_zero Q, one_mul, mul_one]
--     map_mul' := fun x y => by
--       calc
--         ↑(Q ^ (-t) : A_pos) * (x * y) * ↑(Q ^ t : A_pos) =
--             ↑(Q ^ (-t)) * x * (↑(Q ^ t) * ↑(Q ^ (-t))) * y * ↑(Q ^ t) :=
--           by simp_rw [APos_pow_mul Q, add_neg_self, APos_pow_zero Q, mul_one, mul_assoc]
--         _ = ↑(Q ^ (-t)) * x * ↑(Q ^ t) * (↑(Q ^ (-t)) * y * ↑(Q ^ t)) := by simp_rw [mul_assoc]
--     map_add' := fun x y => by simp_rw [mul_add, add_mul]
--     commutes' := fun r => by
--       simp_rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc,
--         APos_pow_mul Q, neg_add_self, APos_pow_zero] }

-- variable {A : Type _} [QuantumSet A]

-- theorem modAut_trans (t s : ℝ) : (modAut A t).trans (modAut A s) = modAut A (t + s) :=
--   by
--   ext x
--   simp_rw [AlgEquiv.trans_apply, modAut_apply, mul_assoc, APos_pow_mul, ← mul_assoc,
--     APos_pow_mul, neg_add, add_comm]

-- theorem modAut_neg (t : ℝ) : modAut A (-t) = (modAut A t).symm :=
--   by
--   ext
--   simp_rw [modAut_apply, modAut_symm_apply, neg_neg]

-- end QuantumSet
