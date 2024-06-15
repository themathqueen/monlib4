/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.MyIps.RankOne
-- import Monlib.LinearAlgebra.MyIps.Functional
import Monlib.LinearAlgebra.Nacgor
import Mathlib.RingTheory.Coalgebra.Basic
import Monlib.LinearAlgebra.MyIps.MulOp
import Monlib.LinearAlgebra.MyIps.TensorHilbert
import Monlib.LinearAlgebra.CoalgebraFiniteDimensional
import Monlib.LinearAlgebra.LmulRmul
import Monlib.LinearAlgebra.IsReal

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

-- attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass
open Coalgebra in
@[reducible]
class QuantumSet (A : Type _)
  extends
    NormedAddCommGroupOfRing A,
    InnerProductSpace ℂ A,
    StarRing A,
    StarModule ℂ A,
    SMulCommClass ℂ A A,
    IsScalarTower ℂ A A,
    Module.Finite ℂ A
    -- PartialOrder A,
    -- Algebra ℂ A,
    -- Coalgebra ℂ A,
    -- Semiring A,
    -- StarOrderedRing A,
    -- Algebra ℂ A,
      where
    -- isScalarTower ℂ A A
    -- /-- the inner product is given by `⟪·,·⟫ := counit (star · * ·)` -/
    -- inner_eq : ∀ x y : A, ⟪x, y⟫_ℂ = Coalgebra.counit (star x * y)
    /-- the modular automorphism `σ _` as a linear isomorphism `A ≃ₗ[ℂ] A` -/
    modAut : Π _ : ℝ, A ≃ₗ[ℂ] A
    /-- the module automorphism is also an algebra isomorphism -/
    modAut_map_mul : ∀ (r : ℝ) (x y : A), modAut r (x * y) = modAut r x * modAut r y
    modAut_map_one : ∀ r, modAut r 1 = 1
    -- modAux :=
    /-- the modular automorphism is an additive homomorphism from `ℝ` to
      `(A ≃ₐ[ℂ] A, add := · * ·, zero := 1)` -/
    modAut_trans : ∀ r s, modAut r ≪≫ₗ modAut s = modAut (r + s)
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

attribute [instance] QuantumSet.toNormedAddCommGroupOfRing
attribute [instance] QuantumSet.toInnerProductSpace
-- attribute [instance] QuantumSet.toPartialOrder
-- attribute [instance] QuantumSet.toStarOrderedRing
attribute [instance] QuantumSet.toSMulCommClass
attribute [instance] QuantumSet.toIsScalarTower
attribute [instance] QuantumSet.n_isFintype
attribute [instance] QuantumSet.n_isDecidableEq
-- attribute [instance] QuantumSet.toCoalgebra
-- attribute [simp] QuantumSet.inner_eq
attribute [simp] QuantumSet.modAut_trans
attribute [simp] QuantumSet.modAut_map_mul
attribute [simp] QuantumSet.modAut_map_one
attribute [simp] QuantumSet.modAut_zero
attribute [simp] QuantumSet.inner_star_left
attribute [simp] QuantumSet.inner_conj_left
attribute [simp] QuantumSet.modAut_isSymmetric

export QuantumSet (modAut n onb)

instance QuantumSet.toAlgebra {A : Type*} [QuantumSet A] :
  Algebra ℂ A :=
Algebra.ofIsScalarTowerSmulCommClass

-- instance QuantumSet.toFiniteDimensionalHilbertAlgebra {A : Type*} [QuantumSet A] :
--   FiniteDimensionalHilbertAlgebra ℂ A :=
-- by infer_instance

theorem lmul_adjoint {B : Type _} [hB : QuantumSet B] [FiniteDimensional ℂ B] (a : B) :
    LinearMap.adjoint (lmul a : B →ₗ[ℂ] B) = lmul (star a) :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro u
  simp_rw [LinearMap.adjoint_inner_left, lmul_apply, hB.inner_star_left, star_star]

lemma QuantumSet.inner_eq_counit' {B : Type*} [hB : QuantumSet B] :
  (⟪(1 : B), ·⟫_ℂ) = Coalgebra.counit :=
by
  simp_rw [Coalgebra.counit]
  ext
  apply ext_inner_left ℂ
  intro a
  simp_rw [LinearMap.adjoint_inner_right, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, inner_smul_left, inner]

lemma QuantumSet.inner_eq_counit {B : Type*} [hB : QuantumSet B] (x y : B) :
  ⟪x, y⟫_ℂ = Coalgebra.counit (star x * y) :=
calc ⟪x, y⟫_ℂ = ⟪x * 1, y⟫_ℂ := by rw [mul_one]
  _ = ⟪(1 : B), star x * y⟫_ℂ := hB.inner_star_left x 1 y
  _ = Coalgebra.counit (star x * y) := by rw [← inner_eq_counit']

theorem rmul_adjoint {B : Type*} [hB : QuantumSet B] (a : B) :
    LinearMap.adjoint (rmul a : B →ₗ[ℂ] B) = rmul (hB.modAut (-1) (star a)) :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro u
  simp_rw [LinearMap.adjoint_inner_left, rmul_apply]
  nth_rw 1 [← inner_conj_symm]
  rw [hB.inner_conj_left, inner_conj_symm]

lemma QuantumSet.inner_conj {A : Type*} [hA : QuantumSet A] (a b : A) :
  ⟪a, b⟫_ℂ = ⟪star b, (hA.modAut (-1) (star a))⟫_ℂ :=
calc ⟪a, b⟫_ℂ = ⟪1 * a, b⟫_ℂ := by rw [one_mul]
  _ = ⟪1, b * hA.modAut (-1) (star a)⟫_ℂ := by rw [inner_conj_left]
  _ = starRingEnd ℂ ⟪b * hA.modAut (-1) (star a), 1⟫_ℂ := by rw [inner_conj_symm]
  _ = starRingEnd ℂ ⟪hA.modAut (-1) (star a), star b⟫_ℂ := by rw [inner_star_left, mul_one]
  _ = ⟪star b, hA.modAut (-1) (star a)⟫_ℂ := by rw [inner_conj_symm]
lemma QuantumSet.inner_conj' {A : Type*} [hA : QuantumSet A] (a b : A) :
  ⟪a, b⟫_ℂ = ⟪hA.modAut (-1) (star b), star a⟫_ℂ :=
calc ⟪a, b⟫_ℂ = starRingEnd ℂ ⟪b, a⟫_ℂ := by rw [inner_conj_symm]
  _ = starRingEnd ℂ ⟪star a, hA.modAut (-1) (star b)⟫_ℂ := by rw [inner_conj]
  _ = ⟪hA.modAut (-1) (star b), star a⟫_ℂ := by rw [inner_conj_symm]

namespace QuantumSet
variable {A B : Type*} [hA : QuantumSet A] [hB : QuantumSet B]
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
    Psi_toFun t r (rankOne a b : _ →L[ℂ] _).toLinearMap =
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

@[simp]
theorem modAut_apply_modAut (t r : ℝ) (a : A) :
  hA.modAut t (hA.modAut r a) = hA.modAut (t + r) a :=
by
  simp only [modAut_trans, ← LinearMap.comp_apply, ← LinearEquiv.coe_toLinearMap,
    LinearEquiv.comp_coe, add_comm]

theorem Psi_left_inv (t r : ℝ) (x : A) (y : B) :
    Psi_invFun t r (Psi_toFun t r |x⟩⟨y|) = (|x⟩⟨y|).toLinearMap :=
  by
  simp_rw [Psi_toFun_apply, Psi_invFun_apply, MulOpposite.unop_op, star_star, modAut_apply_modAut,
    add_left_neg, modAut_zero]
  simp only [LinearEquiv.coe_one, id_eq]

theorem Psi_right_inv (t r : ℝ) (x : A) (y : Bᵐᵒᵖ) :
    Psi_toFun t r (Psi_invFun t r (x ⊗ₜ[ℂ] y)) = x ⊗ₜ[ℂ] y :=
  by
  rw [Psi_invFun_apply, Psi_toFun_apply]
  simp_rw [modAut_apply_modAut, add_neg_self, modAut_zero]
  simp only [LinearEquiv.coe_one, id_eq, star_star, MulOpposite.op_unop]

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

variable {A B : Type*} [hA : QuantumSet A] [hB : QuantumSet B]
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
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
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

lemma _root_.LinearMap.apply_eq_id {R M : Type*} [Semiring R] [AddCommMonoid M]
  [Module R M] {f : M →ₗ[R] M} :
  (∀ x, f x = x) ↔ f = 1 :=
by simp_rw [LinearMap.ext_iff, LinearMap.one_apply]

theorem _root_.QuantumSet.starAlgEquiv_is_isometry_tfae
    (f : B ≃⋆ₐ[ℂ] B) :
    List.TFAE
      [LinearMap.adjoint f.toAlgEquiv.toLinearMap =
          f.symm.toAlgEquiv.toLinearMap,
        Coalgebra.counit ∘ₗ f.toAlgEquiv.toLinearMap = Coalgebra.counit,
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
          ⟪(LinearMap.adjoint f.toAlgEquiv.toLinearMap ∘ₗ f.toAlgEquiv.toLinearMap - 1) x, y⟫_ℂ :=
      by
      intro x y
      simp only [LinearMap.sub_apply, LinearMap.one_apply, inner_sub_left, LinearMap.comp_apply,
        LinearMap.adjoint_inner_left, StarAlgEquiv.coe_toAlgEquiv, AlgEquiv.toLinearMap_apply]
    simp_rw [this, inner_map_self_eq_zero, sub_eq_zero, StarAlgEquiv.comp_eq_iff,
      LinearMap.one_comp]
  rw [tfae_4_iff_1]
  tfae_have 3 ↔ 2
  · simp_rw [QuantumSet.inner_eq_counit, ← map_star f, ← _root_.map_mul f,
      LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      StarAlgEquiv.coe_toAlgEquiv]
    refine' ⟨fun h x => _, fun h x y => h _⟩
    rw [← one_mul x, ← star_one]
    exact h _ _
  rw [← tfae_3_iff_2]
  simp_rw [← StarAlgEquiv.coe_toAlgEquiv, ← AlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_left,
    ← ext_inner_left_iff, ← LinearMap.comp_apply, _root_.LinearMap.apply_eq_id,
    StarAlgEquiv.comp_eq_iff, LinearMap.one_comp]
  tfae_finish

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
