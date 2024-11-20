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
import Monlib.LinearAlgebra.Coalgebra.FiniteDimensional
import Monlib.LinearAlgebra.LmulRmul
import Monlib.LinearAlgebra.IsReal
import Monlib.LinearAlgebra.TensorProduct.FiniteDimensional
import Monlib.LinearAlgebra.TensorProduct.Lemmas
import Mathlib.LinearAlgebra.Trace
import Monlib.LinearAlgebra.Mul''
import Monlib.RepTheory.AutMat
import Monlib.LinearAlgebra.LinearMapOp

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
set_option allowUnsafeReducibility true in
@[reducible]
class starAlgebra (A : Type _) extends
  Ring A, Algebra ℂ A, StarRing A, StarModule ℂ A where
    /-- the modular automorphism `σ _` as a linear isomorphism `A ≃ₗ[ℂ] A` -/
    modAut : Π _ : ℝ, A ≃ₐ[ℂ] A
    /-- the modular automorphism is an additive homomorphism from `ℝ` to
      `(A ≃ₐ[ℂ] A, add := · * ·, zero := 1)` -/
    modAut_trans : ∀ r s, (modAut r).trans (modAut s) = modAut (r + s)
    -- modAut_zero : modAut 0 = 1
    /-- applying star to `modAut r x` will give `modAut (-r) (star x)` -/
    modAut_star : ∀ r x, star (modAut r x) = modAut (-r) (star x)
attribute [instance] starAlgebra.toRing
attribute [instance] starAlgebra.toAlgebra
attribute [instance] starAlgebra.toStarRing
attribute [instance] starAlgebra.toStarModule
attribute [simp] starAlgebra.modAut_trans
attribute [simp] starAlgebra.modAut_star
export starAlgebra (modAut)

theorem starAlgebra.modAut_zero {A : Type*} [hA : starAlgebra A] :
  hA.modAut 0 = 1 :=
by
  ext x
  have := hA.modAut_trans 0 1
  rw [zero_add, AlgEquiv.ext_iff] at this
  specialize this x
  apply_fun (modAut 1).symm at this
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at this
  exact this

@[simp]
theorem starAlgebra.modAut_apply_modAut {A : Type*} [ha : starAlgebra A]
  (t r : ℝ) (a : A) :
  ha.modAut t (ha.modAut r a) = ha.modAut (t + r) a :=
by
  rw [← AlgEquiv.trans_apply, starAlgebra.modAut_trans, add_comm]

@[simp]
theorem starAlgebra.modAut_symm {A : Type*} [ha : starAlgebra A] (r : ℝ) :
  (ha.modAut r).symm = ha.modAut (-r) :=
by
  ext
  apply_fun (ha.modAut r) using AlgEquiv.injective _
  simp only [AlgEquiv.apply_symm_apply, modAut_apply_modAut, add_neg_cancel, ha.modAut_zero]
  rfl

attribute [simp] starAlgebra.modAut_zero

-- @[instance] def starAlgebra.toStarAddMonoid {A : Type*} [starAlgebra A] :
--   StarAddMonoid A :=
-- by infer_instance
open scoped ComplexOrder ComplexConjugate
-- set_option allowUnsafeReducibility true in
-- @[reducible]
class InnerProductAlgebra (A : Type*) [starAlgebra A]
  extends
    Norm A, MetricSpace A,
    Inner ℂ A, BoundedSMul ℂ A where
  dist x y := ‖x - y‖
  -- norm x := (inner x x).re
  norm_sq_eq_inner x : ‖x‖ ^ 2 = RCLike.re (inner x x)
  -- := by aesop
  dist_eq x y : dist x y = ‖x - y‖ := by aesop
  --  ‖x‖ ^ 2 = RCLike.re (inner x x)
  conj_symm : ∀ x y, starRingEnd ℂ (inner y x) = inner x y
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  smul_left : ∀ x y r, inner (r • x) y = starRingEnd ℂ r * inner x y
  -- norm_smul_le : ∀ (a : ℂ) (b : A), ‖a • b‖ ≤ ‖a‖ * ‖b‖
  -- InnerProductSpace.Core ℂ A where


-- attribute [instance] InnerProductAlgebra.toNormedAddCommGroup
-- attribute [instance] InnerProductAlgebra.toInnerProductSpace
  -- where
  -- toInner :

-- noncomputable instance InnerProductAlgebra.toNormedAddCommGroup {A : Type*}
--   [starAlgebra A]
--   [InnerProductAlgebra A] :
--     NormedAddCommGroup A where
--   dist_eq := InnerProductAlgebra.dist_eq
noncomputable instance InnerProductAlgebra.toNormedAddCommGroupOfRing {A : Type*}
  [starAlgebra A] [InnerProductAlgebra A] :
    NormedAddCommGroupOfRing A where
  dist_eq := InnerProductAlgebra.dist_eq
noncomputable instance InnerProductAlgebra.toInnerProductSpace {A : Type*}
  [starAlgebra A] [InnerProductAlgebra A] :
    InnerProductSpace ℂ A where
  norm_smul_le _ _ := by
    rw [norm_smul]

  norm_sq_eq_inner := InnerProductAlgebra.norm_sq_eq_inner
  conj_symm := InnerProductAlgebra.conj_symm
  add_left := InnerProductAlgebra.add_left
  smul_left := InnerProductAlgebra.smul_left

open scoped InnerProductSpace
-- attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass
open Coalgebra in
class QuantumSet (A : Type _) [ha : starAlgebra A]
  extends
    InnerProductAlgebra A
      where
    /-- the modular automorphism is symmetric with respect to the inner product,
      in other words, it is self-adjoint -/
    modAut_isSymmetric : ∀ r x y, ⟪ha.modAut r x, y⟫_ℂ = ⟪x, ha.modAut r y⟫_ℂ
    k : ℝ
    inner_star_left : ∀ x y z : A, ⟪x * y, z⟫_ℂ = ⟪y, ha.modAut (-k) (star x) * z⟫_ℂ
    inner_conj_left : ∀ x y z : A, ⟪x * y, z⟫_ℂ = ⟪x, z * ha.modAut (-k-1) (star y)⟫_ℂ
    n : Type*
    n_isFintype : Fintype n
    n_isDecidableEq : DecidableEq n
    /-- fix an orthonormal basis on `A` -/
    onb : OrthonormalBasis n ℂ A

attribute [instance] QuantumSet.toInnerProductAlgebra
attribute [instance] QuantumSet.n_isFintype
attribute [instance] QuantumSet.n_isDecidableEq
-- attribute [simp] QuantumSet.modAut_trans
-- attribute [simp] QuantumSet.modAut_star
-- attribute [simp] QuantumSet.modAut_zero
attribute [simp] QuantumSet.inner_star_left
attribute [simp] QuantumSet.inner_conj_left
attribute [simp] QuantumSet.modAut_isSymmetric

export QuantumSet (n onb k)

variable {A : Type*} [ha : _root_.starAlgebra A]

instance n_isFinite
  [QuantumSet A] : Finite (n A) :=
by infer_instance

instance QuantumSet.toFinite [hA : QuantumSet A] :
  Module.Finite ℂ A :=
by
  let b := hA.onb.toBasis
  exact @Module.Finite.of_basis ℂ A (n A) _ _ _ _ b

lemma QuantumSet.modAut_isSelfAdjoint
  [hA : QuantumSet A] (r : ℝ) :
  IsSelfAdjoint (ha.modAut r).toLinearMap :=
by
  rw [← LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact modAut_isSymmetric _

alias QuantumSet.modAut_apply_modAut := starAlgebra.modAut_apply_modAut

attribute [simp] TensorProduct.inner_tmul

section Complex
  noncomputable instance Complex.starAlgebra :
    starAlgebra ℂ where
  modAut _ := 1
  modAut_trans _ _ := rfl
  modAut_star _ _ := rfl

  noncomputable instance :
    InnerProductAlgebra ℂ where
  conj_symm := inner_conj_symm
  add_left := inner_add_left
  smul_left := inner_smul_left
  norm_sq_eq_inner := norm_sq_eq_inner
  dist_eq _ _ := rfl

  noncomputable instance Complex.quantumSet :
    QuantumSet ℂ where
  modAut_isSymmetric _ _ _ := rfl
  k := 0
  inner_star_left _ _ _ := by
    simp_rw [RCLike.inner_apply, modAut, RCLike.star_def, ← mul_assoc, mul_comm, map_mul,
      AlgEquiv.one_apply]
  inner_conj_left x y z := by
    simp_rw [RCLike.inner_apply, modAut, map_mul, RCLike.star_def, AlgEquiv.one_apply, mul_comm z,
      ← mul_assoc]
  n := Fin 1
  n_isFintype := Fin.fintype 1
  n_isDecidableEq := instDecidableEqFin 1
  onb := by
    refine Basis.toOrthonormalBasis (Basis.singleton (Fin 1) ℂ) (orthonormal_iff_ite.mpr ?_)
    . intro i j
      simp_rw [Fin.fin_one_eq_zero, Basis.singleton_apply,
        RCLike.inner_apply, map_one, mul_one, if_true]
  @[simp]
  theorem RCLike.inner_tmul {𝕜 : Type*} [RCLike 𝕜] (x y z w : 𝕜) :
    ⟪x ⊗ₜ[𝕜] y, z ⊗ₜ[𝕜] w⟫_𝕜 = ⟪x * y, z * w⟫_𝕜 :=
  by
    simp only [TensorProduct.inner_tmul, inner_apply, map_mul]
    rw [mul_mul_mul_comm]
  open scoped TensorProduct
  theorem TensorProduct.singleton_tmul
    {R : Type _} {E : Type _} {F : Type _} [CommSemiring R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (x : E ⊗[R] F) (b₁ : Basis (Fin 1) R E) (b₂ : Basis (Fin 1) R F) :
    ∃ (a : E) (b : F), x = a ⊗ₜ[R] b :=
  by
    use (b₁.tensorProduct b₂).repr x (0,0) • b₁ 0, b₂ 0
    have := TensorProduct.of_basis_eq_span x b₁ b₂
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton] at this
    rw [← TensorProduct.smul_tmul']
    exact this

  theorem RCLike.inner_tensor_apply {𝕜 : Type*} [RCLike 𝕜] (x y : 𝕜 ⊗[𝕜] 𝕜) :
    ⟪x, y⟫_𝕜 = ⟪LinearMap.mul' 𝕜 _ x, LinearMap.mul' 𝕜 _ y⟫_𝕜 :=
  by
    obtain ⟨α,β,rfl⟩ := x.singleton_tmul (Basis.singleton (Fin 1) 𝕜) (Basis.singleton (Fin 1) 𝕜)
    obtain ⟨α2,β2,rfl⟩ := y.singleton_tmul (Basis.singleton (Fin 1) 𝕜) (Basis.singleton (Fin 1) 𝕜)
    simp only [LinearMap.mul'_apply, RCLike.inner_tmul]

  @[simp]
  theorem QuantumSet.complex_modAut :
    Complex.starAlgebra.modAut = 1 :=
  rfl
  theorem QuantumSet.complex_comul :
    (Coalgebra.comul : ℂ →ₗ[ℂ] ℂ ⊗[ℂ] ℂ) = (TensorProduct.lid ℂ ℂ).symm.toLinearMap :=
  by
    ext
    rw [TensorProduct.inner_ext_iff']
    intro a b
    simp_rw [Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_left, LinearMap.mul'_apply,
      LinearEquiv.coe_toLinearMap, TensorProduct.lid_symm_apply,
      TensorProduct.inner_tmul, RCLike.inner_apply, starRingEnd_apply, star_one, one_mul]

end Complex

set_option maxHeartbeats 0 in
def QuantumSet.modAut_isCoalgHom
  {A : Type*} [hA : starAlgebra A] [QuantumSet A] (r : ℝ) :
  LinearMap.IsCoalgHom (AlgEquiv.toLinearMap (hA.modAut r)) :=
by
  rw [← modAut_isSelfAdjoint, LinearMap.star_eq_adjoint]
  simp_rw [LinearMap.isCoalgHom_iff, Coalgebra.counit_eq_unit_adjoint,
    Coalgebra.comul_eq_mul_adjoint,
    ← TensorProduct.map_adjoint, ← LinearMap.adjoint_comp,
    Function.Injective.eq_iff (LinearEquiv.injective _),
    TensorProduct.ext_iff', LinearMap.ext_iff, LinearMap.comp_apply,
    TensorProduct.map_tmul, LinearMap.mul'_apply]
  simp only [Algebra.linearMap_apply, AlgEquiv.toLinearMap_apply, map_mul, implies_true, and_true,
    Algebra.algebraMap_eq_smul_one, map_smul, map_one]

-- instance QuantumSet.toAlgebra {A : Type*} [NormedAddCommGroupOfRing A] [QuantumSet A] :
--   Algebra ℂ A :=
-- Algebra.ofIsScalarTowerSmulCommClass

-- instance QuantumSet.toFiniteDimensionalHilbertAlgebra {A : Type*} [QuantumSet A] :
--   FiniteDimensionalHilbertAlgebra ℂ A :=
-- by infer_instance

variable {A B : Type _} [hb : starAlgebra B] [ha : starAlgebra A]
  [hA:QuantumSet A] [hB:QuantumSet B]
theorem lmul_adjoint (a : B) :
    LinearMap.adjoint (lmul a : B →ₗ[ℂ] B) = lmul (modAut (- hB.k) (star a)) :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro u
  simp_rw [LinearMap.adjoint_inner_left, lmul_apply,
    QuantumSet.inner_star_left,
    starAlgebra.modAut_star, star_star, neg_neg, QuantumSet.modAut_apply_modAut, neg_add_cancel,
    starAlgebra.modAut_zero, AlgEquiv.one_apply]

lemma QuantumSet.inner_eq_counit' :
  (⟪(1 : B), ·⟫_ℂ) = Coalgebra.counit :=
by
  simp_rw [Coalgebra.counit]
  ext
  apply ext_inner_left ℂ
  intro a
  simp_rw [LinearMap.adjoint_inner_right, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, inner_smul_left]
  rfl

lemma QuantumSet.inner_conj (a b : A) :
  ⟪a, b⟫_ℂ = ⟪star b, (ha.modAut (-(2 * hA.k) - 1) (star a))⟫_ℂ :=
calc ⟪a, b⟫_ℂ = ⟪1 * a, b⟫_ℂ := by rw [one_mul]
  _ = ⟪1, b * ha.modAut (-hA.k-1) (star a)⟫_ℂ := by rw [inner_conj_left]
  _ = starRingEnd ℂ ⟪b * ha.modAut (-hA.k-1) (star a), 1⟫_ℂ := by rw [inner_conj_symm]
  _ = starRingEnd ℂ ⟪ha.modAut (-hA.k-1) (star a), ha.modAut (-hA.k) (star b)⟫_ℂ :=
    by rw [inner_star_left, mul_one]
  _ = ⟪star b, ha.modAut (- (2* hA.k) -1) (star a)⟫_ℂ :=
    by rw [inner_conj_symm, modAut_isSymmetric, modAut_apply_modAut]; ring_nf
lemma QuantumSet.inner_conj' (a b : A) :
  ⟪a, b⟫_ℂ = ⟪ha.modAut (-(2 * hA.k) - 1) (star b), star a⟫_ℂ :=
by
  rw [inner_conj, modAut_isSymmetric]
lemma QuantumSet.inner_modAut_right_conj (a b : A) :
  ⟪a, ha.modAut (-hA.k) (star b)⟫_ℂ
    = ⟪b, ha.modAut (-hA.k-1) (star a)⟫_ℂ :=
by
  nth_rw 1 [← one_mul a]
  rw [inner_conj_left, ← inner_star_left, mul_one]
lemma QuantumSet.inner_conj'' (a b : A) :
  ⟪a, b⟫_ℂ = ⟪modAut ((-(2 * hA.k) - 1) / 2) (star b), modAut ((-(2*hA.k) - 1) / 2) (star a)⟫_ℂ :=
calc ⟪a, b⟫_ℂ = ⟪modAut (-(2 * hA.k) - 1) (star b), star a⟫_ℂ := by rw [inner_conj']
  _ = ⟪modAut ((-(2 * hA.k)-1) / 2) (modAut (((-(2 * hA.k)-1) / 2)) (star b)), star a⟫_ℂ := by
    rw [modAut_apply_modAut]; norm_num
  _ = ⟪modAut ((-(2 * hA.k)-1) / 2) (star b), modAut ((-(2 * hA.k)-1) / 2) (star a)⟫_ℂ := by
    rw [modAut_isSymmetric]

lemma QuantumSet.inner_eq_counit (x y : B) :
  ⟪x, y⟫_ℂ = Coalgebra.counit (star x * modAut hB.k y) :=
by
  simp_rw [← inner_eq_counit']
  nth_rw 2 [← inner_conj_symm]
  rw [inner_star_left, star_star, inner_conj_symm, mul_one,
    modAut_isSymmetric, modAut_apply_modAut, neg_add_cancel, hb.modAut_zero,
    AlgEquiv.one_apply]

open Coalgebra in
theorem counit_mul_modAut_symm' (a b : A) (r : ℝ) :
  counit (a * ha.modAut r b) = (counit (ha.modAut (r + 1) b * a) : ℂ) :=
by
  simp_rw [← inner_eq_counit']
  nth_rw 1 [← inner_conj_symm]
  simp_rw [hA.inner_conj_left, one_mul, ha.modAut_star, QuantumSet.modAut_apply_modAut, inner_conj_symm,
    ← neg_add_eq_sub, ← neg_add, ← ha.modAut_star, inner_eq_counit',
    hA.inner_eq_counit, star_star]
  calc counit ((modAut (1 + k A + r)) b * (modAut (k A)) a)
      = counit (modAut (k A) (modAut (1 + r) b * a)) :=
      by simp_rw [map_mul, QuantumSet.modAut_apply_modAut]; ring_nf
    _ = counit (modAut (r + 1) b * a) :=
      by rw [← AlgEquiv.toLinearMap_apply,
        ← LinearMap.comp_apply, (QuantumSet.modAut_isCoalgHom _).1, add_comm]

-- theorem QuantumSet.linearMap_adjoint_toGNS (x y : A) :
--   LinearMap.adjoint (toGNS x y) = toGNS (modAut (-hA.k) (star y)) (star x) :=

theorem rmul_adjoint (a : B) :
    LinearMap.adjoint (rmul a : B →ₗ[ℂ] B) = rmul (modAut (-hB.k-1) (star a)) :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro u
  simp_rw [LinearMap.adjoint_inner_left, rmul_apply]
  nth_rw 1 [← inner_conj_symm]
  rw [hB.inner_conj_left, inner_conj_symm]

theorem counit_comp_mul_comp_rTensor_modAut :
  Coalgebra.counit ∘ₗ LinearMap.mul' ℂ A ∘ₗ LinearMap.rTensor A (modAut 1).toLinearMap
    = Coalgebra.counit ∘ₗ LinearMap.mul' ℂ A ∘ₗ (TensorProduct.comm ℂ _ _).toLinearMap :=
by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, LinearMap.mul'_apply, AlgEquiv.toLinearMap_apply]
  have := counit_mul_modAut_symm' y x 0
  rw [zero_add, ha.modAut_zero, AlgEquiv.one_apply] at this
  exact this.symm

theorem counit_comp_mul_comp_lTensor_modAut :
  Coalgebra.counit ∘ₗ LinearMap.mul' ℂ A ∘ₗ LinearMap.lTensor A (modAut (-1)).toLinearMap
    = Coalgebra.counit ∘ₗ LinearMap.mul' ℂ A ∘ₗ (TensorProduct.comm ℂ _ _).toLinearMap :=
by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, LinearMap.mul'_apply, AlgEquiv.toLinearMap_apply,
    counit_mul_modAut_symm', neg_add_cancel, ha.modAut_zero, AlgEquiv.one_apply]

example (kms : k A = - (1 / 2)) (x : A) :
  ‖star x‖ = ‖x‖ :=
by
  simp only [norm_eq_sqrt_inner (𝕜 := ℂ)]
  congr 2
  rw [QuantumSet.inner_conj'', star_star]
  simp [kms]

namespace QuantumSet
open scoped TensorProduct
noncomputable
def Psi_toFun
  (t r : ℝ) :
  (A →ₗ[ℂ] B) →ₗ[ℂ] (B ⊗[ℂ] Aᵐᵒᵖ) where
  toFun x :=
    ∑ a, ∑ b,
      (LinearMap.toMatrix hA.onb.toBasis hB.onb.toBasis) x a b •
        hb.modAut t (hB.onb a) ⊗ₜ[ℂ] MulOpposite.op (star (ha.modAut r (hA.onb b)))
  map_add' x y := by simp_rw [map_add, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [_root_.map_smul, Matrix.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

theorem Psi_toFun_apply
    (t r : ℝ) (b : A) (a : B) :
    Psi_toFun t r (rankOne ℂ a b).toLinearMap =
      hb.modAut t a ⊗ₜ[ℂ] MulOpposite.op (star (ha.modAut r b)) :=
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
set_option synthInstance.maxHeartbeats 80000 in
noncomputable
def Psi_invFun (t r : ℝ) :
  (A ⊗[ℂ] Bᵐᵒᵖ) →ₗ[ℂ] (B →ₗ[ℂ] A)
  where
  toFun x :=
    ∑ a, ∑ b,
      (hA.onb.toBasis.tensorProduct hB.onb.toBasis.mulOpposite).repr x (a, b) •
        (↑|ha.modAut (-t) (hA.onb a)⟩⟨hb.modAut (-r) (star (hB.onb b))|)
  map_add' x y := by simp_rw [_root_.map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [_root_.map_smul, Finsupp.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

theorem Psi_invFun_apply (t r : ℝ) (x : A) (y : Bᵐᵒᵖ) :
    Psi_invFun t r (x ⊗ₜ[ℂ] y) =
      |ha.modAut (-t) x⟩⟨hb.modAut (-r) (star (MulOpposite.unop y))| :=
  by
  simp_rw [Psi_invFun, LinearMap.coe_mk, AddHom.coe_mk,
    Basis.tensorProduct_repr_tmul_apply,
    smul_eq_mul, mul_comm,
    ← rankOne_lm_smul_smul, ← rankOne_lm_sum_sum, ←
    _root_.map_smul, ← star_smul, Basis.mulOpposite_repr_apply, ← map_sum, ← star_sum,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.sum_repr]

theorem Psi_left_inv (t r : ℝ) (x : A) (y : B) :
    Psi_invFun t r (Psi_toFun t r |x⟩⟨y|) = (|x⟩⟨y|).toLinearMap :=
  by
  simp_rw [Psi_toFun_apply, Psi_invFun_apply, MulOpposite.unop_op, star_star, modAut_apply_modAut,
    neg_add_cancel, starAlgebra.modAut_zero]
  simp only [AlgEquiv.one_apply]

theorem Psi_right_inv (t r : ℝ) (x : A) (y : Bᵐᵒᵖ) :
    Psi_toFun t r (Psi_invFun t r (x ⊗ₜ[ℂ] y)) = x ⊗ₜ[ℂ] y :=
  by
  rw [Psi_invFun_apply, Psi_toFun_apply]
  simp_rw [modAut_apply_modAut, add_neg_cancel, starAlgebra.modAut_zero]
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
      (ha.modAut (2 * hA.k + 1)).toLinearMap ∘ₗ
        (LinearMap.adjoint f.real) ∘ₗ (hb.modAut (- (2 * hB.k) - 1)).toLinearMap :=
by
  rw [LinearMap.ext_iff]
  intro x
  apply ext_inner_right ℂ
  intro u
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
  nth_rw 1 [inner_conj']
  simp_rw [LinearMap.real_apply, star_star, LinearMap.adjoint_inner_right, modAut_isSymmetric,
    LinearMap.adjoint_inner_left, LinearMap.real_apply, starAlgebra.modAut_star]
  nth_rw 1 [inner_conj']
  rw [star_star, neg_add, ← sub_eq_add_neg]

local notation "|" a "⟩⟨" b "|" => @rankOne ℂ _ _ _ _ _ _ _ a b

lemma rankOne_real (a : A) (b : B) :
  LinearMap.real |a⟩⟨b| = (|star a⟩⟨hb.modAut (-(2 * hB.k)-1) (star b)|).toLinearMap :=
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
  exact ⟨modAut _, fun x y z ↦ inner_star_left x y z⟩
open LinearMap in
lemma _root_.QuantumSet.lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul :
  lTensor A (mul' ℂ A) ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ rTensor A (Coalgebra.comul)
   = Coalgebra.comul ∘ₗ mul' ℂ A :=
by
  rw [Coalgebra.comul_eq_mul_adjoint, Coalgebra.lTensor_mul_comp_rTensor_mul_adjoint_of]
  exact ⟨modAut _, fun x y z ↦ inner_star_left x y z⟩

noncomputable def _root_.QuantumSet.isFrobeniusAlgebra :
    FrobeniusAlgebra ℂ A where
  lTensor_mul_comp_rTensor_comul_commute := by
    rw [lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul,
      rTensor_mul_comp_lTensor_comul_eq_comul_comp_mul]

open scoped TensorProduct
open LinearMap in
set_option synthInstance.maxHeartbeats 200000 in
theorem _root_.QuantumSet.rTensor_counit_mul_comp_comm_comp_rTensor_comul_unit_eq_modAut_one :
  (TensorProduct.lid ℂ A).toLinearMap
    ∘ₗ rTensor A (Coalgebra.counit ∘ₗ mul' ℂ A)
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
    ∘ₗ lTensor A (TensorProduct.comm ℂ _ _).toLinearMap
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap
    ∘ₗ rTensor A (Coalgebra.comul ∘ₗ Algebra.linearMap ℂ A)
    ∘ₗ (TensorProduct.lid ℂ A).symm.toLinearMap
  = (ha.modAut 1).toLinearMap :=
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
    inner_star_left, starAlgebra.modAut_star, modAut_apply_modAut, neg_sub, sub_neg_eq_add, mul_one, star_star]
  ring_nf

set_option synthInstance.maxHeartbeats 200000 in
open LinearMap in
theorem _root_.QuantumSet.lTensor_counit_mul_comp_comm_comp_lTensor_comul_unit_eq_modAut_neg_one :
  (TensorProduct.rid ℂ A).toLinearMap
    ∘ₗ lTensor A (Coalgebra.counit ∘ₗ mul' ℂ A)
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap
    ∘ₗ rTensor A (TensorProduct.comm ℂ _ _).toLinearMap
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
    ∘ₗ lTensor A (Coalgebra.comul ∘ₗ Algebra.linearMap ℂ A)
    ∘ₗ (TensorProduct.rid ℂ A).symm.toLinearMap
  = (ha.modAut (-1)).toLinearMap :=
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
    inner_conj_left, one_mul, starAlgebra.modAut_star, neg_neg, modAut_apply_modAut, star_star]
  ring_nf

open LinearMap in
lemma _root_.QuantumSet.counit_tensor_star_left_eq_bra (x : A) :
  Coalgebra.counit ∘ mul' ℂ A ∘ ((modAut (-hA.k)) (star x) ⊗ₜ[ℂ] ·) = bra ℂ x :=
by
  ext
  simp only [Function.comp_apply, mul'_apply, innerSL_apply]
  nth_rw 1 [← (modAut_isCoalgHom hA.k).1]
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul, modAut_apply_modAut, add_neg_cancel, starAlgebra.modAut_zero, AlgEquiv.one_apply]
  exact Eq.symm (inner_eq_counit _ _)
open LinearMap in
lemma _root_.QuantumSet.mul_comp_tensor_left_unit_eq_ket (x : A) :
  mul' ℂ A ∘ (x ⊗ₜ[ℂ] ·) ∘ Algebra.linearMap ℂ A = ket ℂ x :=
by
  ext
  simp only [Function.comp_apply, Algebra.linearMap_apply, mul'_apply, ket_toFun_toFun,
    Algebra.algebraMap_eq_smul_one, mul_smul_one]
open LinearMap starAlgebra in
lemma _root_.QuantumSet.rTensor_bra_comul_unit_eq_ket_star (x : A) :
  (TensorProduct.lid ℂ _).toLinearMap
    ∘ₗ (rTensor A (bra ℂ x)) ∘ₗ Coalgebra.comul ∘ₗ Algebra.linearMap ℂ A
  = ket ℂ (modAut (- hA.k) (star x)) :=
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
open LinearMap starAlgebra in
lemma _root_.QuantumSet.rTensor_bra_comul_unit_eq_ket_star' (x : A) :
  (TensorProduct.lid ℂ _).toLinearMap
    ∘ₗ (rTensor A (bra ℂ (modAut (-hA.k) x))) ∘ₗ Coalgebra.comul ∘ₗ Algebra.linearMap ℂ A
  = ket ℂ (star x) :=
by
  rw [rTensor_bra_comul_unit_eq_ket_star, modAut_star, starAlgebra.modAut_apply_modAut,
    neg_neg, neg_add_cancel, modAut_zero]
  rfl

open LinearMap in
lemma _root_.QuantumSet.counit_mul_rTensor_ket_eq_bra_star (x : A) :
  Coalgebra.counit ∘ₗ mul' ℂ A ∘ₗ (rTensor A (ket ℂ x)) ∘ₗ (TensorProduct.lid ℂ _).symm.toLinearMap
  = bra ℂ (modAut (-hA.k) (star x)) :=
by
  apply_fun LinearMap.adjoint using LinearEquiv.injective _
  simp only [adjoint_comp, TensorProduct.lid_symm_adjoint, rTensor_adjoint]
  simp only [ContinuousLinearMap.linearMap_adjoint, ket_adjoint_eq_bra,
    bra_adjoint_eq_ket, ← Coalgebra.comul_eq_mul_adjoint,
    Coalgebra.counit_eq_unit_adjoint, adjoint_adjoint, comp_assoc]
  rw [← rTensor_bra_comul_unit_eq_ket_star x]
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
  LinearMap.real (bra ℂ x) = (bra ℂ (ha.modAut (-(2*hA.k)-1) (star x))).toLinearMap :=
by
  ext
  simp only [LinearMap.real_apply, ContinuousLinearMap.coe_coe,
    bra_apply_apply, RCLike.star_def, inner_conj_symm]
  rw [QuantumSet.inner_conj, star_star, modAut_isSymmetric]

theorem ket_toMatrix {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
  {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 A) (x : A) :
  LinearMap.toMatrix (Basis.singleton Unit 𝕜) b (ket 𝕜 x)
    = Matrix.col Unit (b.repr x) :=
by
  ext
  simp only [Matrix.col_apply, LinearMap.toMatrix_apply,
    Basis.singleton_apply, ContinuousLinearMap.coe_coe, ket_toFun_toFun, one_smul]
open scoped Matrix
theorem bra_toMatrix {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 A) (x : A) :
  LinearMap.toMatrix b.toBasis (Basis.singleton Unit 𝕜) (bra 𝕜 x) = (Matrix.col Unit (b.repr x))ᴴ :=
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
    -- (gns₁ : hA.k = 0) (gns₂ : hB.k = 0)
    (f : A ≃⋆ₐ[ℂ] B) :
    List.TFAE
      [LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap,

        ∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ,
        ∀ x, ‖f x‖ = ‖x‖,
        Isometry f] :=
by
  tfae_have 3 ↔ 1 := by
    simp_rw [@norm_eq_sqrt_inner ℂ, Real.sqrt_inj inner_self_nonneg inner_self_nonneg,
      ← @RCLike.ofReal_inj ℂ, @inner_self_re ℂ, ← @sub_eq_zero _ _ _ ⟪_, _⟫_ℂ]
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
  rw [tfae_3_iff_1]
  -- tfae_have 3 ↔ 2
  -- ·
  --
  simp_rw [← StarAlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_left,
    ← ext_inner_left_iff, ← LinearMap.comp_apply, _root_.LinearMap.apply_eq_id,
    StarAlgEquiv.comp_eq_iff, LinearMap.one_comp]
  rw [AddMonoidHomClass.isometry_iff_norm]
  tfae_finish

theorem _root_.QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm
    {f : A ≃⋆ₐ[ℂ] B} :
    Isometry f ↔ LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap :=
List.TFAE.out (starAlgEquiv_is_isometry_tfae f) 3 0

theorem QuantumSet.starAlgEquiv_isometry_iff_coalgHom
  (gns₁ : hA.k = 0) (gns₂ : hB.k = 0)
  {f : A ≃⋆ₐ[ℂ] B} :
  Isometry f ↔
  Coalgebra.counit ∘ₗ f.toLinearMap = Coalgebra.counit :=
by
  simp_rw [isometry_iff_inner,
    QuantumSet.inner_eq_counit, ← map_star f,
    LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,
    gns₁, gns₂, starAlgebra.modAut_zero, AlgEquiv.one_apply, ← map_mul]
  refine' ⟨fun h x => _, fun h x y => h _⟩
  rw [← one_mul x, ← star_one]
  exact h _ _

theorem _root_.StarAlgEquiv.isReal {R A B : Type*} [Semiring R]
  [AddCommMonoid A] [AddCommMonoid B] [Mul A] [Mul B] [Module R A]
  [Module R B] [Star A] [Star B] (f : A ≃⋆ₐ[R] B) :
    LinearMap.IsReal f.toLinearMap :=
by
  intro
  simp only [StarAlgEquiv.toLinearMap_apply, map_star]

omit hA in
theorem QuantumSet.modAut_real (r : ℝ) :
    (ha.modAut r).toLinearMap.real = (ha.modAut (-r)).toLinearMap :=
by
  rw [LinearMap.ext_iff]
  intro
  simp_rw [LinearMap.real_apply, AlgEquiv.toLinearMap_apply, ha.modAut_star, star_star]

theorem _root_.AlgEquiv.linearMap_comp_eq_iff {R E₁ E₂ E₃ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
    [AddCommMonoid E₃] [Algebra R E₁] [Algebra R E₂] [Module R E₃]
    (f : E₁ ≃ₐ[R] E₂) (x : E₂ →ₗ[R] E₃) (y : E₁ →ₗ[R] E₃) :
    x ∘ₗ f.toLinearMap = y ↔ x = y ∘ₗ f.symm.toLinearMap :=
by aesop
theorem _root_.AlgEquiv.comp_linearMap_eq_iff
  {R E₁ E₂ E₃ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
  [AddCommMonoid E₃] [Algebra R E₁] [Algebra R E₂] [Module R E₃]
  (f : E₁ ≃ₐ[R] E₂) (x : E₃ →ₗ[R] E₁) (y : E₃ →ₗ[R] E₂) :
  f.toLinearMap ∘ₗ x = y ↔ x = f.symm.toLinearMap ∘ₗ y :=
by aesop

lemma QuantumSet.modAut_adjoint (r : ℝ) :
  LinearMap.adjoint (ha.modAut r).toLinearMap = (ha.modAut r).toLinearMap :=
by
  rw [← LinearMap.isSelfAdjoint_iff']
  exact modAut_isSelfAdjoint r

theorem _root_.QuantumSet.starAlgEquiv_commutes_with_modAut_of_isometry
  {f : A ≃⋆ₐ[ℂ] B} (hf : Isometry f) :
  (modAut ((2 * k A) + 1)).trans f.toAlgEquiv = f.toAlgEquiv.trans (modAut ((2 * k B) + 1)) :=
by
  rw [starAlgEquiv_isometry_iff_adjoint_eq_symm] at hf
  have := LinearMap.adjoint_real_eq f.toLinearMap
  rw [← neg_sub] at this
  simp only [sub_neg_eq_add,
    LinearMap.real_of_isReal (_root_.StarAlgEquiv.isReal _), hf] at this
  simp only [← LinearMap.comp_assoc, ← starAlgebra.modAut_symm,
    ← AlgEquiv.linearMap_comp_eq_iff] at this
  apply_fun LinearMap.adjoint at this
  simp only [LinearMap.adjoint_comp, ← hf, LinearMap.adjoint_adjoint,
    QuantumSet.modAut_adjoint] at this
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,
    AlgEquiv.toLinearMap_apply] at this
  simp only [AlgEquiv.ext_iff, AlgEquiv.trans_apply, StarAlgEquiv.coe_toAlgEquiv]
  nth_rw 2 [add_comm]
  exact λ _ => (this _).symm

theorem _root_.QuantumSet.starAlgEquiv_commutes_with_modAut_of_isometry'
  {f : A ≃⋆ₐ[ℂ] B} (hf : Isometry f) :
  f.toLinearMap.comp (modAut ((2 * k A) + 1)).toLinearMap =
    (modAut ((2 * k B) + 1)).toLinearMap.comp f.toLinearMap :=
by
  have := _root_.QuantumSet.starAlgEquiv_commutes_with_modAut_of_isometry hf
  simp only [AlgEquiv.ext_iff, AlgEquiv.trans_apply,
    LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.coe_toAlgEquiv,
    StarAlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply] at this ⊢
  exact this

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
private noncomputable def tenSwap_Psi_aux :
  (A →ₗ[ℂ] B) →ₗ[ℂ] (B ⊗[ℂ] Aᵐᵒᵖ) where
  toFun f := tenSwap ℂ ((LinearMap.lTensor A ((op ℂ).toLinearMap ∘ₗ f)) (Coalgebra.comul 1))
  map_add' x y := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.TensorProduct.map_apply,
      LinearMap.comp_add, LinearMap.lTensor_add, map_add, LinearMap.add_apply]
  map_smul' r x := by
    simp only [RingHom.id_apply, LinearMap.comp_smul, LinearMap.lTensor_smul,
      LinearMap.smul_apply, map_smul]
private lemma tenSwap_Psi_aux_apply (f : A →ₗ[ℂ] B) :
  tenSwap_Psi_aux f = tenSwap ℂ
    ((LinearMap.lTensor A ((op ℂ).toLinearMap ∘ₗ f)) (Coalgebra.comul 1)) :=
rfl

theorem tenSwap_lTensor_comul_one_eq_Psi (f : A →ₗ[ℂ] B) :
  tenSwap ℂ ((LinearMap.lTensor A ((op ℂ).toLinearMap ∘ₗ f)) (Coalgebra.comul 1))
    = Psi 0 (k A + 1) f :=
by
  rw [← tenSwap_Psi_aux_apply, ← LinearEquiv.coe_toLinearMap]
  revert f
  rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro x y
  rw [TensorProduct.inner_ext_iff']
  intro a b
  simp only [LinearEquiv.coe_coe, Psi_apply, Psi_toFun_apply,
    tenSwap_Psi_aux_apply, starAlgebra.modAut_zero, AlgEquiv.one_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul 1 : A ⊗[ℂ] A)
  rw [← h]
  simp_rw [map_sum, LinearMap.lTensor_tmul, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,
    op_apply, tenSwap_apply', ContinuousLinearMap.coe_coe, rankOne_apply,
    ← TensorProduct.smul_tmul', sum_inner, inner_smul_left, inner_conj_symm,
    TensorProduct.inner_tmul, MulOpposite.inner_eq, MulOpposite.unop_op,
    mul_comm _ (_ * _), mul_assoc, ← Finset.mul_sum,
    ← TensorProduct.inner_tmul, ← sum_inner, h,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_left,
    LinearMap.mul'_apply, TensorProduct.inner_tmul,
    inner_eq_counit, star_star, star_one, one_mul, map_mul, ← counit_mul_modAut_symm']

private noncomputable def map_op_comul_one_aux :
  (A →ₗ[ℂ] B) →ₗ[ℂ] (B ⊗[ℂ] Aᵐᵒᵖ) where
  toFun f := (TensorProduct.map f (op ℂ).toLinearMap) (Coalgebra.comul 1)
  map_add' x y := by
    simp only [TensorProduct.map_add_left, LinearMap.add_apply]
  map_smul' r x := by
    simp only [TensorProduct.map_smul_left, LinearMap.smul_apply]
    rfl

private lemma map_op_comul_one_aux_apply (f : A →ₗ[ℂ] B) :
  map_op_comul_one_aux f = (TensorProduct.map f (op ℂ).toLinearMap) (Coalgebra.comul 1) :=
rfl

theorem map_op_comul_one_eq_Psi (f : A →ₗ[ℂ] B) :
  (TensorProduct.map f (op ℂ).toLinearMap) (Coalgebra.comul 1) = Psi 0 (k A) f :=
by
  rw [← map_op_comul_one_aux_apply, ← LinearEquiv.coe_toLinearMap]
  revert f
  rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro x y
  rw [TensorProduct.inner_ext_iff']
  intro a b
  simp only [LinearEquiv.coe_coe, Psi_apply, Psi_toFun_apply,
    map_op_comul_one_aux_apply, starAlgebra.modAut_zero, AlgEquiv.one_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul 1 : A ⊗[ℂ] A)
  rw [← h]
  simp_rw [map_sum, sum_inner, TensorProduct.map_tmul,
    TensorProduct.inner_tmul, ContinuousLinearMap.coe_coe, rankOne_apply,
    inner_smul_left, inner_conj_symm, MulOpposite.inner_eq,
    LinearEquiv.coe_toLinearMap, op_apply,
    MulOpposite.unop_op, mul_assoc, mul_comm ⟪x, _⟫_ℂ,
    ← mul_assoc, ← Finset.sum_mul, ← TensorProduct.inner_tmul,
    ← sum_inner, h, Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_left,
    LinearMap.mul'_apply, TensorProduct.inner_tmul,
    inner_eq_counit, star_star, star_one, one_mul, map_mul]

theorem _root_.tenSwap_apply_lTensor {R A B C : Type*}
  [CommSemiring R] [AddCommMonoid A] [AddCommMonoid C] [Module R A]
  [AddCommMonoid B] [Module R B] [Module R C] (f : B →ₗ[R] C) (x : A ⊗[R] Bᵐᵒᵖ) :
  (tenSwap R) ((LinearMap.lTensor A f.op) x) =
   (LinearMap.rTensor _ f) (tenSwap R x) :=
x.induction_on (by simp only [map_zero])
  (λ _ _ => by
    simp only [LinearMap.lTensor_tmul, LinearMap.op_apply, tenSwap_apply,
      LinearMap.rTensor_tmul]; rfl)
  (λ _ _ h1 h2 => by simp only [map_add, LinearMap.add_apply, h1, h2])

theorem Psi_inv_comp_swap_lTensor_op_comp_comul_eq_rmul :
  (Psi 0 (k A + 1)).symm.toLinearMap
    ∘ₗ (tenSwap ℂ).toLinearMap
    ∘ₗ (LinearMap.lTensor A (op ℂ).toLinearMap)
    ∘ₗ Coalgebra.comul
  = rmul :=
by
  ext x y
  apply ext_inner_left ℂ
  intro z
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Psi_symm_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul x : A ⊗[ℂ] A)
  rw [← h]
  simp_rw [map_sum, LinearMap.sum_apply, inner_sum, LinearMap.lTensor_tmul,
    LinearEquiv.coe_toLinearMap,
    op_apply, tenSwap_apply', Psi_invFun_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, neg_zero, starAlgebra.modAut_zero, AlgEquiv.one_apply,
    MulOpposite.unop_op, inner_smul_right, neg_add,
    ← inner_conj_symm _ y,
    ← sub_eq_add_neg, ← QuantumSet.inner_modAut_right_conj,
    inner_conj_symm, ← TensorProduct.inner_tmul, ← inner_sum, h,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_right,
    LinearMap.mul'_apply, rmul_apply, inner_star_left, starAlgebra.modAut_star,
    modAut_apply_modAut, add_neg_cancel, starAlgebra.modAut_zero, star_star,
    AlgEquiv.one_apply]

theorem QuantumSet.Psi_apply_one_one (t r : ℝ) :
  QuantumSet.Psi t r (rankOne ℂ (1 : B) (1 : A)) = (1 : B ⊗[ℂ] Aᵐᵒᵖ) :=
by
  simp only [Psi_apply, Psi_toFun_apply, _root_.map_one,
    star_one, MulOpposite.op_one, Algebra.TensorProduct.one_def]
theorem QuantumSet.Psi_symm_apply_one (t r : ℝ) :
  (QuantumSet.Psi t r).symm (1 : A ⊗[ℂ] Bᵐᵒᵖ) = rankOne ℂ (1 : A) (1 : B) :=
by
  rw [← QuantumSet.Psi_apply_one_one t r, LinearEquiv.symm_apply_apply]

@[simps!]
noncomputable abbrev Upsilon :
  (A →ₗ[ℂ] B) ≃ₗ[ℂ] (A ⊗[ℂ] B) :=
(Psi 0 (k A + 1)).trans ((tenSwap ℂ).trans (LinearEquiv.lTensor _ (unop ℂ)))

theorem Upsilon_apply_one_one :
  Upsilon (rankOne ℂ (1 : B) (1 : A)) = (1 : A ⊗[ℂ] B) :=
by
  rw [Upsilon, LinearEquiv.trans_apply, Psi_apply_one_one]
  rfl
theorem Upsilon_symm_apply_one :
  Upsilon.symm (1 : A ⊗[ℂ] B) = rankOne ℂ (1 : B) (1 : A) :=
by
  rw [← Upsilon_apply_one_one, LinearEquiv.symm_apply_apply]

private noncomputable def rmulMapLmul_apply_Upsilon_aux :
  (A →ₗ[ℂ] B) →ₗ[ℂ] ((A ⊗[ℂ] B) →ₗ[ℂ] (A ⊗[ℂ] B)) where
  toFun x := (LinearMap.lTensor _ (LinearMap.mul' ℂ B))
      ∘ₗ (TensorProduct.assoc _ _ _ _).toLinearMap
      ∘ₗ (LinearMap.rTensor _ (LinearMap.lTensor _ x))
      ∘ₗ LinearMap.rTensor _ (Coalgebra.comul)
  map_add' _ _ := by simp only [LinearMap.lTensor_add, LinearMap.rTensor_add,
    LinearMap.comp_add, LinearMap.add_comp]
  map_smul' _ _ := by
    simp only [LinearMap.lTensor_smul, LinearMap.rTensor_smul,
      LinearMap.comp_smul, LinearMap.smul_comp]
    rfl

private lemma rmulMapLmul_apply_Upsilon_aux_apply (x : A →ₗ[ℂ] B) :
  rmulMapLmul_apply_Upsilon_aux x =
    (LinearMap.lTensor _ (LinearMap.mul' ℂ B))
      ∘ₗ (TensorProduct.assoc _ _ _ _).toLinearMap
      ∘ₗ (LinearMap.rTensor _ (LinearMap.lTensor _ x))
      ∘ₗ LinearMap.rTensor _ (Coalgebra.comul) :=
rfl

lemma Upsilon_rankOne (a : A) (b : B) :
  Upsilon (rankOne ℂ a b).toLinearMap = (modAut (- k B - 1) (star b)) ⊗ₜ[ℂ] a :=
by
  rw [Upsilon_apply, QuantumSet.Psi_toFun_apply, TensorProduct.comm_tmul,
    TensorProduct.map_tmul, LinearEquiv.lTensor_tmul, starAlgebra.modAut_star,
    starAlgebra.modAut_zero]
  ring_nf
  rfl
lemma Upsilon_symm_tmul (a : A) (b : B) :
  Upsilon.symm (a ⊗ₜ[ℂ] b) = (rankOne ℂ b (modAut (- k A - 1) (star a))).toLinearMap :=
by
  rw [Upsilon_symm_apply]
  simp only [LinearEquiv.lTensor_symm_tmul, LinearEquiv.symm_symm, op_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, unop_apply, MulOpposite.unop_op, TensorProduct.comm_symm_tmul, QuantumSet.Psi_invFun_apply,
    starAlgebra.modAut_zero, neg_zero]
  ring_nf
  rfl

set_option synthInstance.maxHeartbeats 0 in
lemma rmulMapLmul_apply_Upsilon_eq (x : A →ₗ[ℂ] B) :
  rmulMapLmul (Upsilon x) =
    (LinearMap.lTensor _ (LinearMap.mul' ℂ B))
      ∘ₗ (TensorProduct.assoc _ _ _ _).toLinearMap
      ∘ₗ (LinearMap.rTensor _ (LinearMap.lTensor _ x))
      ∘ₗ LinearMap.rTensor _ (Coalgebra.comul) :=
by
  symm
  rw [← rmulMapLmul_apply_Upsilon_aux_apply, ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
  revert x
  rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro x y
  rw [TensorProduct.ext_iff']
  intro a b
  rw [TensorProduct.inner_ext_iff', rmulMapLmul_apply_Upsilon_aux_apply]
  intro c d
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul a : A ⊗[ℂ] A)
  simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply,
    Psi_apply, LinearEquiv.TensorProduct.map_apply, LinearMap.rTensor_tmul,
    Psi_toFun_apply, TensorProduct.comm_tmul,
    TensorProduct.map_tmul, ← h, map_sum, TensorProduct.sum_tmul,
    map_sum, sum_inner]
  simp only [LinearMap.lTensor_tmul, ContinuousLinearMap.coe_coe, rankOne_apply_apply_toFun,
    TensorProduct.tmul_smul, starAlgebra.modAut_star, neg_add_rev,
    LinearEquiv.coe_coe, unop_apply, MulOpposite.unop_op, starAlgebra.modAut_zero,
    AlgEquiv.one_apply, op_apply, LinearEquiv.lTensor_tmul,
    ← TensorProduct.smul_tmul', map_smul, inner_smul_left, inner_conj_symm,
    TensorProduct.assoc_tmul, TensorProduct.inner_tmul]
  simp_rw [← mul_assoc, ← Finset.sum_mul, mul_comm ⟪β _, _⟫_ℂ,
    ← TensorProduct.inner_tmul, ← sum_inner, h,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_left,
    LinearMap.mul'_apply, rmulMapLmul_apply, TensorProduct.map_tmul,
    TensorProduct.inner_tmul, rmul_apply, neg_add_eq_sub]
  nth_rw 2 [inner_conj_left]
  simp_rw [starAlgebra.modAut_star, modAut_apply_modAut, star_star,
    add_neg_cancel, starAlgebra.modAut_zero]
  rfl
