import Monlib.LinearAlgebra.Coalgebra.Lemmas
import Mathlib.RingTheory.Coalgebra.Equiv
import Mathlib.Analysis.InnerProductSpace.Basic
import Monlib.LinearAlgebra.Nacgor
import Monlib.LinearAlgebra.Ips.TensorHilbert
import Monlib.LinearAlgebra.Ips.RankOne
import Monlib.LinearAlgebra.Mul''

variable {R A : Type*}
local notation "lT" => LinearMap.lTensor
local notation "rT" => LinearMap.rTensor
local notation "m" => LinearMap.mul' R
local notation "ϰ" => TensorProduct.assoc R
local notation "τ" => TensorProduct.lid R
local notation "η" => Algebra.linearMap R

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass
open scoped TensorProduct

lemma algebraMapCLM_eq_ket_one {R A : Type*} [RCLike R] [NormedAddCommGroupOfRing A]
  [InnerProductSpace R A] [SMulCommClass R A A] [IsScalarTower R A A] :
  algebraMapCLM R A = ket R 1 :=
rfl

lemma algebraMapCLM_adjoint_eq_bra_one {R A : Type*} [RCLike R] [NormedAddCommGroupOfRing A]
  [InnerProductSpace R A] [SMulCommClass R A A] [IsScalarTower R A A] [CompleteSpace A] :
  ContinuousLinearMap.adjoint (algebraMapCLM R A) = bra R 1 :=
by
  rw [algebraMapCLM_eq_ket_one, ← bra_adjoint_eq_ket, ContinuousLinearMap.adjoint_adjoint]

lemma LinearMap.adjoint_id {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A]
  [InnerProductSpace 𝕜 A] [FiniteDimensional 𝕜 A] :
  adjoint (id : A →ₗ[𝕜] A) = id :=
by rw [← one_eq_id, adjoint_one]

lemma LinearMap.rTensor_adjoint {𝕜 A B C : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C]
  (f : A →ₗ[𝕜] B) :
  adjoint (rTensor C f) = rTensor C (adjoint f) :=
by
  simp_rw [rTensor, TensorProduct.map_adjoint, adjoint_id]
lemma LinearMap.lTensor_adjoint {𝕜 A B C : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C]
  (f : A →ₗ[𝕜] B) :
  adjoint (lTensor C f) = lTensor C (adjoint f) :=
by
  simp_rw [lTensor, TensorProduct.map_adjoint, adjoint_id]

lemma TensorProduct.rid_adjoint {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
  LinearMap.adjoint (TensorProduct.rid 𝕜 E).toLinearMap = (TensorProduct.rid 𝕜 E).symm.toLinearMap :=
  by
  ext1
  apply @ext_inner_right 𝕜
  intro y
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.rid_symm_apply]
  exact y.induction_on
    (by simp only [inner_zero_right, map_zero])
    (fun α z => by
      simp only [TensorProduct.rid_tmul, TensorProduct.inner_tmul, RCLike.inner_apply,
        starRingEnd_apply, star_one, one_mul, inner_smul_right, mul_comm, mul_one])
    (fun z w hz hw => by simp only [_root_.map_add, inner_add_right, hz, hw])

-- @[reducible]
-- structure FiniteDimensionalHilbertAlgebra (R A : Type*) [RCLike R] extends
--   NormedAddCommGroupOfRing A, InnerProductSpace R A, SMulCommClass R A A,
--   IsScalarTower R A A, Finite R A where

@[reducible, instance]
noncomputable
def Coalgebra.ofFiniteDimensionalHilbertAlgebra
  [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  Coalgebra R A :=
{ comul := (LinearMap.adjoint (LinearMap.mul' R A : (A ⊗[R] A) →ₗ[R] A) : A →ₗ[R] A ⊗[R] A)
  counit := (LinearMap.adjoint (Algebra.linearMap R A : R →ₗ[R] A) : A →ₗ[R] R)
  coassoc := by
    simp only
    rw [← LinearMap.rTensor_adjoint, ← LinearMap.lTensor_adjoint, ← TensorProduct.assoc_symm_adjoint]
    simp_rw [← LinearMap.adjoint_comp, Algebra.mul_comp_rTensor_mul]
    simp_rw [LinearMap.comp_assoc]
    simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      LinearMap.id_comp]
    rfl
  rTensor_counit_comp_comul := by
    simp only
    rw [← LinearMap.rTensor_adjoint, ← LinearMap.adjoint_comp, Algebra.mul_comp_rTensor_unit,
      TensorProduct.lid_adjoint]
    rfl
  lTensor_counit_comp_comul := by
    simp only
    rw [← LinearMap.lTensor_adjoint, ← LinearMap.adjoint_comp, Algebra.mul_comp_lTensor_unit,
      TensorProduct.rid_adjoint]
    rfl }
-- scoped[ofFiniteDimensionalHilbertAlgebra] attribute [instance] Coalgebra.ofFiniteDimensionalHilbertAlgebra
-- def NormedAddCommGroup.ofFiniteDimensionalCoAlgebra
--   [RCLike R] [Ring A] [Algebra R A] [Coalgebra R A] [FiniteDimensional R A] :
--   NormedAddCommGroup A :=
-- @InnerProductSpace.Core.toNormedAddCommGroup R A _ _ _
--     { inner := counit () }

-- open scoped ofFiniteDimensionalHilbertAlgebra in
lemma Coalgebra.comul_eq_mul_adjoint
  [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  Coalgebra.comul = (LinearMap.adjoint (LinearMap.mul' R A : (A ⊗[R] A) →ₗ[R] A) : A →ₗ[R] A ⊗[R] A) :=
rfl
-- open scoped ofFiniteDimensionalHilbertAlgebra in
lemma Coalgebra.counit_eq_unit_adjoint
  [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  Coalgebra.counit = (LinearMap.adjoint (Algebra.linearMap R A : R →ₗ[R] A) : A →ₗ[R] R) :=
rfl

open scoped InnerProductSpace
-- open scoped ofFiniteDimensionalHilbertAlgebra in
lemma Coalgebra.inner_eq_counit' [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  (⟪(1 : A), ·⟫_R) = Coalgebra.counit :=
by
  simp_rw [Coalgebra.counit]
  ext
  apply ext_inner_left R
  intro a
  simp_rw [LinearMap.adjoint_inner_right, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, inner_smul_left, inner]
-- @[reducible]
-- class NormedAddCommGroupOfStarRing (B : Type _) extends
--   NormedAddCommGroupOfRing B, StarRing B

lemma Coalgebra.counit_eq_bra_one [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  Coalgebra.counit = (bra R (1 : A)).toLinearMap :=
by
  haveI := FiniteDimensional.complete R A
  rw [counit_eq_unit_adjoint, ← algebraMapCLM_adjoint_eq_bra_one]
  rfl

open Coalgebra LinearMap TensorProduct in
theorem Coalgebra.rTensor_mul_comp_lTensor_comul
  [RCLike R] [NormedAddCommGroupOfRing A] [Star A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
  (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ (star x) * z⟫_R) :
  (rT A (m A)) ∘ₗ (ϰ A A A).symm.toLinearMap ∘ₗ (lT A comul) = comul ∘ₗ (m A) :=
by
  rw [TensorProduct.ext_iff']
  intro x y
  rw [TensorProduct.inner_ext_iff']
  intro a b
  simp_rw [comp_apply, lTensor_tmul]
  obtain ⟨σ, h⟩ := h
  obtain ⟨α, β, hy⟩ := TensorProduct.eq_span (comul y : A ⊗[R] A)
  simp_rw [← hy, tmul_sum, _root_.map_sum, sum_inner, LinearEquiv.coe_coe, assoc_symm_tmul,
    rTensor_tmul, mul'_apply, inner_tmul, h, ← inner_tmul, ← sum_inner, hy,
    comul_eq_mul_adjoint, LinearMap.adjoint_inner_left, mul'_apply, mul_assoc, h]

-- open scoped ofFiniteDimensionalHilbertAlgebra in
theorem Coalgebra.rTensor_mul_comp_lTensor_mul_adjoint
  [RCLike R] [NormedAddCommGroupOfRing A] [Star A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
  (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ (star x) * z⟫_R) :
  (rT A (m A)) ∘ₗ (ϰ A A A).symm.toLinearMap ∘ₗ (lT A (LinearMap.adjoint (m A))) = (LinearMap.adjoint (m A)) ∘ₗ (m A) :=
Coalgebra.rTensor_mul_comp_lTensor_comul h

-- /-- An equivalence between structures that are both co-algebras and algebras -/
-- structure CoAlgEquiv (R A B : Type*) [CommSemiring R]
--     [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [Coalgebra R A] [Coalgebra R B] extends
--     A ≃ₗc[R] B, A ≃ₐ[R] B where

-- attribute [nolint docBlame] CoAlgEquiv.toCoalgEquiv
-- attribute [nolint docBlame] CoAlgEquiv.toAlgEquiv

-- @[inherit_doc CoAlgEquiv]
-- infixr:25 " ≃ₐc " => CoAlgEquiv _
-- @[inherit_doc CoAlgEquiv]
-- notation:50 A " ≃ₐc[" R "] " B => CoAlgEquiv R A B

-- class CoAlgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
--     [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [Coalgebra R A] [Coalgebra R B]
--     [EquivLike F A B] extends CoalgEquivClass F R A B, AlgEquivClass F R A B :
--     Prop

-- namespace CoAlgEquivClass

-- variable {F R A B : Type*} [CommSemiring R]
--     [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [Coalgebra R A] [Coalgebra R B]

-- @[coe]
-- def toCoAlgEquiv [EquivLike F A B] [CoAlgEquivClass F R A B] (f : F) : A ≃ₐc[R] B :=
--   { (f : A ≃ₐ[R] B), (f : A →ₗc[R] B) with }

-- instance instCoeToCoAlgEquiv
--     [EquivLike F A B] [CoAlgEquivClass F R A B] : CoeHead F (A ≃ₐc[R] B) where
--   coe f := toCoAlgEquiv f

-- end CoAlgEquivClass

-- namespace CoAlgEquiv
-- variable {F R A B : Type*} [CommSemiring R]
--     [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [Coalgebra R A] [Coalgebra R B]

-- def toEquiv : (A ≃ₐc[R] B) → A ≃ B := fun f => f.toAlgEquiv.toEquiv

-- theorem toEquiv_injective : Function.Injective (toEquiv : (A ≃ₐc[R] B) → A ≃ B) :=
--   fun ⟨_, _, _⟩ ⟨_, _, _⟩ h =>
--     (CoAlgEquiv.mk.injEq _ _ _ _ _ _).mpr
--       (CoalgEquiv.toEquiv_inj.mp h)

-- @[simp]
-- theorem toEquiv_inj {e₁ e₂ : A ≃ₐc[R] B} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
--   toEquiv_injective.eq_iff

-- theorem toCoalgEquiv_injective : Function.Injective (toCoalgEquiv : (A ≃ₐc[R] B) → A ≃ₗc[R] B) :=
--   fun _ _ H => toEquiv_injective <| Equiv.ext <| CoalgEquiv.congr_fun H

-- instance : EquivLike (A ≃ₐc[R] B) A B where
--   inv := CoAlgEquiv.invFun
--   left_inv := CoAlgEquiv.left_inv
--   right_inv := CoAlgEquiv.right_inv
--   coe_injective' _ _ h _ := toCoalgEquiv_injective (DFunLike.coe_injective h)
--   -- left_inv := _
--   -- right_inv := _

-- instance : FunLike (A ≃ₐc[R] B) A B where
--   coe := DFunLike.coe
--   coe_injective' := DFunLike.coe_injective

-- instance : CoAlgEquivClass (A ≃ₐc[R] B) R A B where
--   map_add := (·.map_add')
--   map_smulₛₗ := (·.map_smul')
--   counit_comp := (·.counit_comp)
--   map_comp_comul := (·.map_comp_comul)

-- -- @[simp, norm_cast]
-- -- theorem coe_coe {e : A ≃ₐc[R] B} : (e : A → B) = e :=
-- --   rfl

open Coalgebra LinearMap TensorProduct in
theorem Coalgebra.lTensor_mul_comp_rTensor_comul_of
  [RCLike R] [NormedAddCommGroupOfRing A] [Star A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
  (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ (star x) * z⟫_R) :
  (lT A (m A)) ∘ₗ (ϰ A A A).toLinearMap ∘ₗ (rT A comul) = comul ∘ₗ (m A) :=
by
  apply_fun adjoint using LinearEquiv.injective _
  simp_rw [comul_eq_mul_adjoint]
  letI : NormedAddCommGroup (A ⊗[R] A) := by infer_instance
  letI : InnerProductSpace R (A ⊗[R] A) := by infer_instance
  simp_rw [LinearMap.adjoint_comp]
  simp_rw [lTensor_adjoint, rTensor_adjoint,adjoint_adjoint,
    TensorProduct.assoc_adjoint, LinearMap.comp_assoc]
  exact Coalgebra.rTensor_mul_comp_lTensor_mul_adjoint h

open Coalgebra LinearMap TensorProduct in
theorem Coalgebra.lTensor_mul_comp_rTensor_mul_adjoint_of
  [RCLike R] [NormedAddCommGroupOfRing A] [Star A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
  (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ (star x) * z⟫_R) :
  (lT A (m A)) ∘ₗ (ϰ A A A).toLinearMap ∘ₗ (rT A (LinearMap.adjoint (m A))) = LinearMap.adjoint (m A) ∘ₗ (m A) :=
Coalgebra.lTensor_mul_comp_rTensor_comul_of h

noncomputable def FiniteDimensionalCoAlgebra_isFrobeniusAlgebra_of
  [RCLike R] [NormedAddCommGroupOfRing A] [Star A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
  (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ (star x) * z⟫_R) :
    FrobeniusAlgebra R A where
  lTensor_mul_comp_rTensor_comul_commute := by
    rw [Coalgebra.lTensor_mul_comp_rTensor_comul_of h, Coalgebra.rTensor_mul_comp_lTensor_comul h]

open CoalgebraStruct
structure LinearMap.IsCoalgHom {R A B : Type*}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] (x : A →ₗ[R] B) : Prop :=
    counit_comp : counit ∘ₗ x = counit
    map_comp_comul : TensorProduct.map x x ∘ₗ comul = comul ∘ₗ x
lemma LinearMap.isCoalgHom_iff {R A B : Type*}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] (x : A →ₗ[R] B) :
    x.IsCoalgHom ↔ counit ∘ₗ x = counit ∧ TensorProduct.map x x ∘ₗ comul = comul ∘ₗ x :=
⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

structure LinearMap.IsAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] (x : A →ₗ[R] B) : Prop :=
    comp_unit : x ∘ₗ Algebra.linearMap R A = Algebra.linearMap R B
    mul'_comp_map : (mul' R B) ∘ₗ (TensorProduct.map x x) = x ∘ₗ (mul' R A)
lemma LinearMap.isAlgHom_iff {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] (x : A →ₗ[R] B) :
    x.IsAlgHom ↔
      x ∘ₗ Algebra.linearMap R A = Algebra.linearMap R B
      ∧
      (mul' R B) ∘ₗ (TensorProduct.map x x) = x ∘ₗ (mul' R A) :=
⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

lemma AlgHom.isAlgHom
  {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B]
  (x : A →ₐ[R] B) :
  x.toLinearMap.IsAlgHom :=
by
  rw [LinearMap.isAlgHom_iff, commutes_with_mul'_iff, commutes_with_unit_iff]
  simp only [toLinearMap_apply, map_one, map_mul, implies_true, and_self]
lemma AlgEquiv.isAlgHom
  {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B]
  (x : A ≃ₐ[R] B) :
  x.toLinearMap.IsAlgHom :=
AlgHom.isAlgHom _

variable {B : Type*} [RCLike R] [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [InnerProductSpace R A] [InnerProductSpace R B]
  [SMulCommClass R A A] [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B]
  [FiniteDimensional R A] [FiniteDimensional R B]
  (x : A →ₗ[R] B)

theorem LinearMap.isAlgHom_iff_adjoint_isCoalgHom :
  x.IsAlgHom ↔ (LinearMap.adjoint x).IsCoalgHom :=
by
  simp_rw [isAlgHom_iff, isCoalgHom_iff, Coalgebra.counit_eq_unit_adjoint,
    Coalgebra.comul_eq_mul_adjoint, ← TensorProduct.map_adjoint, ← LinearMap.adjoint_comp]
  constructor
  . rintro ⟨h1, h2⟩
    simp_rw [h1, h2, and_self]
  . rintro ⟨h1, h2⟩
    apply_fun adjoint at h1 h2
    simp_rw [adjoint_adjoint] at h1 h2
    exact ⟨h1, h2⟩

theorem LinearMap.isCoalgHom_iff_adjoint_isAlgHom :
  x.IsCoalgHom ↔ (LinearMap.adjoint x).IsAlgHom :=
by
  rw [isAlgHom_iff_adjoint_isCoalgHom, adjoint_adjoint]
