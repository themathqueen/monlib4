/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
-- import Monlib.LinearAlgebra.MyIps.Nontracial
-- import Monlib.LinearAlgebra.MyIps.MatIps
import Monlib.LinearAlgebra.QuantumSet.Basic
import Monlib.LinearAlgebra.Ips.TensorHilbert
import Monlib.LinearAlgebra.IsReal
-- import Monlib.LinearAlgebra.MyIps.Frob
import Monlib.LinearAlgebra.TensorProduct.FiniteDimensional
import Monlib.LinearAlgebra.Ips.OpUnop
import Monlib.LinearAlgebra.LmulRmul
import Monlib.LinearAlgebra.Nacgor
import Monlib.LinearAlgebra.Coalgebra.FiniteDimensional

/-!
 # Schur product operator

 In this file we define the Schur product operator and prove some basic properties.
-/

open scoped TensorProduct BigOperators

local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" x => LinearMap.mul' ℂ x

local notation x " ⊗ₘ " y => TensorProduct.map x y

open Coalgebra
/-- Schur product `⬝ •ₛ ⬝ : (B → C) → (B → C) → (B → C)` given by
  `x •ₛ y := m ∘ (x ⊗ y) ∘ comul`  -/
@[simps]
noncomputable def schurMul {B C : Type _}
  [AddCommMonoid B] [NonUnitalNonAssocSemiring C]
  [Module ℂ B] [Module ℂ C]
  [CoalgebraStruct ℂ B]
  [SMulCommClass ℂ C C]
  [IsScalarTower ℂ C C]
   :
  (B →ₗ[ℂ] C) →ₗ[ℂ] (B →ₗ[ℂ] C) →ₗ[ℂ] (B →ₗ[ℂ] C)
    where
  toFun x :=
    { toFun := fun y => (m C) ∘ₗ (x ⊗ₘ y) ∘ₗ comul
      map_add' := fun x y => by
        simp only [TensorProduct.map_apply, TensorProduct.map_add_right, LinearMap.add_comp,
          LinearMap.comp_add]
      map_smul' := fun r x => by
        simp only [TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul,
          RingHom.id_apply] }
  map_add' x y :=
    by
    simp only [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.ext_iff, LinearMap.add_apply, LinearMap.coe_mk]
    intro _ _; rfl
  map_smul' r x :=
    by
    simp only [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.coe_mk, RingHom.id_apply]
    intro _ _; rfl

@[inherit_doc schurMul]
-- scoped[schurMul] infix:100 " •ₛ " => schurMul
notation3:80 (name := schurMulNotation) x:81 " •ₛ " y:80 => schurMul x y
-- open scoped schurMul

variable {A B C : Type _}
  [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B] [NormedAddCommGroupOfRing C]
  [InnerProductSpace ℂ A] [InnerProductSpace ℂ B] [InnerProductSpace ℂ C]
  [SMulCommClass ℂ A A] [SMulCommClass ℂ B B]
  [SMulCommClass ℂ C C] [IsScalarTower ℂ A A]
  [IsScalarTower ℂ B B] [IsScalarTower ℂ C C]
  [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
  [FiniteDimensional ℂ C]

omit [FiniteDimensional ℂ B] in
theorem schurMul.apply_rankOne
  (a : B) (b : C) (c : B) (d : C) : (↑|a⟩⟨b|) •ₛ (↑|c⟩⟨d|) = (|a * c⟩⟨b * d| : C →ₗ[ℂ] B) :=
  by
  rw [schurMul, LinearMap.ext_iff]
  intro x
  apply ext_inner_right ℂ
  intro u
  simp only [ContinuousLinearMap.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
    rankOne_apply, LinearMap.comp_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (comul x : _ ⊗[ℂ] _)
  rw [← h]
  simp_rw [map_sum, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, rankOne_apply,
    LinearMap.mul'_apply, smul_mul_smul_comm, ← TensorProduct.inner_tmul, ← Finset.sum_smul, ← inner_sum,
    h, comul_eq_mul_adjoint, LinearMap.adjoint_inner_right, LinearMap.mul'_apply]

omit [FiniteDimensional ℂ B] in
theorem schurMul.apply_ket
  (a b : B) :
  (ket ℂ a) •ₛ (ket ℂ b) = (ket ℂ (a * b)).toLinearMap :=
by
  simp only [schurMul_apply_apply, QuantumSet.complex_comul]
  ext
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.lid_symm_apply, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    ket_apply_apply, one_smul, LinearMap.mul'_apply]

section

variable {𝕜 B C : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [NormedAddCommGroup C]
  [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C]
  [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C]
theorem bra_tmul
  (a : B) (b : C) :
  (bra 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap =
  (TensorProduct.lid 𝕜 _).toLinearMap ∘ₗ TensorProduct.map (bra 𝕜 a).toLinearMap (bra 𝕜 b).toLinearMap :=
by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    innerSL_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, innerSL_apply_coe, Function.comp_apply,
    TensorProduct.inner_tmul, TensorProduct.lid_tmul]
  rfl
theorem bra_map_bra (a : B) (b : C) :
  TensorProduct.map (bra 𝕜 a).toLinearMap (bra 𝕜 b).toLinearMap =
    (TensorProduct.lid 𝕜 _).symm.toLinearMap ∘ₗ (bra 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap :=
by
  rw [bra_tmul, ← LinearMap.comp_assoc]
  simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp]

theorem ket_tmul (a : B) (b : C) :
  (ket 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap =
  TensorProduct.map (ket 𝕜 a).toLinearMap (ket 𝕜 b).toLinearMap
  ∘ₗ (TensorProduct.lid 𝕜 _).symm.toLinearMap :=
by
  ext
  simp only [ContinuousLinearMap.coe_coe, ket_one_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, TensorProduct.lid_symm_apply, TensorProduct.map_tmul]

theorem ket_map_ket (a : B) (b : C) :
  TensorProduct.map (ket 𝕜 a).toLinearMap (ket 𝕜 b).toLinearMap
    =  ((ket 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap) ∘ₗ (TensorProduct.lid 𝕜 _).toLinearMap :=
by
  rw [ket_tmul, LinearMap.comp_assoc]
  simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id]

theorem rankOne_tmul {A D : Type*} [NormedAddCommGroup A] [NormedAddCommGroup D]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 D] [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 D]
  (a : A) (b : B) (c : C) (d : D) :
  (rankOne 𝕜 (a ⊗ₜ[𝕜] c) (b ⊗ₜ[𝕜] d)).toLinearMap
    = TensorProduct.map (rankOne 𝕜 a b).toLinearMap
      (rankOne 𝕜 c d).toLinearMap :=
by
  simp_rw [← ket_bra_eq_rankOne, ContinuousLinearMap.coe_comp,
    TensorProduct.map_comp, ket_map_ket, bra_map_bra]
  rw [← LinearMap.comp_assoc, LinearMap.comp_assoc (TensorProduct.lid 𝕜 _).symm.toLinearMap]
  simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id]
end

theorem bra_comp_linearMap {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
  (x : E₂) (f : E₁ →ₗ[𝕜] E₂) :
  ((bra 𝕜) x).toLinearMap.comp f = ((bra 𝕜) ((LinearMap.adjoint f) x)).toLinearMap :=
letI := FiniteDimensional.complete 𝕜 E₁
letI := FiniteDimensional.complete 𝕜 E₂
calc (bra 𝕜 x).toLinearMap ∘ₗ f
    = ((bra 𝕜 x) ∘L LinearMap.toContinuousLinearMap f).toLinearMap := rfl
  _ = (bra 𝕜 ((ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap f)) x)).toLinearMap :=
    by rw [bra_comp_continuousLinearMap]
  _ = (bra 𝕜 ((LinearMap.adjoint f) x)).toLinearMap := rfl
theorem linearMap_comp_ket {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace 𝕜 E₂] (x : E₁) (f : E₁ →ₗ[𝕜] E₂) :
  f ∘ₗ (ket 𝕜 x).toLinearMap = (ket 𝕜 (f x)).toLinearMap :=
by
  ext
  simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, ket_apply_apply,
    one_smul]

theorem mul_comp_lid_symm {R : Type*} [CommSemiring R] :
  LinearMap.mul' R R ∘ₗ (TensorProduct.lid R R).symm.toLinearMap = LinearMap.id :=
by aesop

theorem schurMul.apply_bra
  (a b : C) :
  (bra ℂ a) •ₛ (bra ℂ b) = (bra ℂ (a * b)).toLinearMap :=
by
  rw [schurMul_apply_apply, bra_map_bra, LinearMap.comp_assoc, bra_comp_linearMap,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_adjoint, LinearMap.mul'_apply,
    ← LinearMap.comp_assoc, mul_comp_lid_symm]
  rfl

omit [FiniteDimensional ℂ B] in
theorem schurMul.comp_apply_of
  (δ : ℂ)
  (hAδ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • LinearMap.id)
  (a b : A →ₗ[ℂ] B) (c d : C →ₗ[ℂ] A) :
  (a •ₛ b) ∘ₗ (c •ₛ d) = δ • ((a ∘ₗ c) •ₛ (b ∘ₗ d)) :=
by
  calc (a •ₛ b) ∘ₗ (c •ₛ d)
      = (m _) ∘ₗ (a ⊗ₘ b) ∘ₗ (comul ∘ₗ (m A)) ∘ₗ (c ⊗ₘ d) ∘ₗ comul :=
        by simp_rw [schurMul_apply_apply, LinearMap.comp_assoc]
    _ = δ • (m _ ) ∘ₗ ((a ⊗ₘ b) ∘ₗ (c ⊗ₘ d)) ∘ₗ comul :=
        by simp_rw [hAδ, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
          LinearMap.comp_assoc]
    _ = δ • (a ∘ₗ c) •ₛ (b ∘ₗ d) :=
        by rw [← TensorProduct.map_comp]; rfl


theorem schurMul_one_one_right
    (A : C →ₗ[ℂ] B) : A •ₛ (|(1 : B)⟩⟨(1 : C)| : C →ₗ[ℂ] B) = A :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp_rw [map_sum, LinearMap.sum_apply, schurMul.apply_rankOne, mul_one]

theorem schurMul_one_one_left
    (A : C →ₗ[ℂ] B) : (|(1 : B)⟩⟨(1 : C)| : C →ₗ[ℂ] B) •ₛ A = A :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp_rw [map_sum, schurMul.apply_rankOne, one_mul]

theorem schurMul_adjoint (x y : B →ₗ[ℂ] C) :
    LinearMap.adjoint (x •ₛ y) = (LinearMap.adjoint x) •ₛ (LinearMap.adjoint y) :=
  by
  simp_rw [schurMul, comul_eq_mul_adjoint]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    TensorProduct.map_adjoint, LinearMap.comp_assoc]

theorem schurMul_real
  {A B : Type*} [starAlgebra A] [starAlgebra B]
  [QuantumSet A] [QuantumSet B]
  (x y : A →ₗ[ℂ] B) :
    LinearMap.real (x •ₛ y : A →ₗ[ℂ] B) = (LinearMap.real y) •ₛ (LinearMap.real x) :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  obtain ⟨γ, ζ, rfl⟩ := y.exists_sum_rankOne
  simp only [map_sum, LinearMap.real_sum, LinearMap.sum_apply, schurMul.apply_rankOne]
  simp_rw [rankOne_real, schurMul.apply_rankOne, ← map_mul, ← StarMul.star_mul]
  rw [Finset.sum_comm]

theorem schurMul_one_right_rankOne
  {B : Type*} [starAlgebra B] [hB : QuantumSet B]
  (a b : B) :
    (↑|a⟩⟨b|) •ₛ 1 = lmul a * (LinearMap.adjoint (lmul b : l(B))) :=
  by
  simp_rw [LinearMap.ext_iff_inner_map]
  intro u
  let f := stdOrthonormalBasis ℂ B
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm f]
  simp_rw [map_sum, LinearMap.sum_apply, schurMul.apply_rankOne, ContinuousLinearMap.coe_coe,
    rankOne_apply, Module.End.mul_apply, lmul_apply, sum_inner, inner_smul_left,
    hB.inner_star_left,
    inner_conj_symm, OrthonormalBasis.sum_inner_mul_inner, lmul_adjoint, lmul_apply]

theorem schurMul_one_left_rankOne
  {B : Type*} [starAlgebra B] [hB : QuantumSet B]
  (a b : B) :
    (1 : l(B)) •ₛ (|a⟩⟨b|) = (rmul a : l(B)) * (LinearMap.adjoint (rmul b : l(B))) :=
  by
  simp_rw [← ext_inner_map]
  intro u
  let f := stdOrthonormalBasis ℂ B
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm f, map_sum, LinearMap.sum_apply]
  simp_rw [schurMul.apply_rankOne, LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, Module.End.mul_apply, rmul_apply, sum_inner, inner_smul_left,
    QuantumSet.inner_conj_left, inner_conj_symm,
    OrthonormalBasis.sum_inner_mul_inner, ← QuantumSet.inner_conj_left,
    rmul_adjoint, rmul_apply]

theorem Psi.schurMul
  {A B : Type*} [starAlgebra A] [starAlgebra B]
  [hA : QuantumSet A] [QuantumSet B]
  (r₁ r₂ : ℝ)
    (f g : A →ₗ[ℂ] B) :
    hA.Psi r₁ r₂ (f •ₛ g) = hA.Psi r₁ r₂ f * hA.Psi r₁ r₂ g :=
  by
  suffices
    ∀ (a c : B) (b d : A),
      hA.Psi r₁ r₂ ((↑|a⟩⟨b|) •ₛ |c⟩⟨d|) = hA.Psi r₁ r₂ (|a⟩⟨b|).toLinearMap * hA.Psi r₁ r₂ (|c⟩⟨d|)
    by
    obtain ⟨α, β, rfl⟩ := f.exists_sum_rankOne
    obtain ⟨γ, δ, rfl⟩ := g.exists_sum_rankOne
    simp_rw [map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_mul, map_sum, this]
  intro a b c d
  simp_rw [hA.Psi_apply, hA.Psi_toFun_apply, schurMul.apply_rankOne,
    hA.Psi_toFun_apply, Algebra.TensorProduct.tmul_mul_tmul,
    ← MulOpposite.op_mul, ← StarMul.star_mul, ← map_mul]

theorem schurMul_assoc {A B : Type*}
  [starAlgebra A] [starAlgebra B]
  [hA : QuantumSet A] [QuantumSet B]
  (f g h : A →ₗ[ℂ] B) :
  (f •ₛ g) •ₛ h = f •ₛ (g •ₛ h) :=
by
  apply_fun hA.Psi 0 0 using LinearEquiv.injective _
  simp_rw [Psi.schurMul, mul_assoc]

set_option linter.deprecated false in
theorem nonUnitalAlgHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] (f : A →ₙₐ[R] B) :
    f.toLinearMap ∘ₗ LinearMap.mul' R A = (LinearMap.mul' R B) ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap) :=
by
  rw [TensorProduct.ext_iff']
  intro a b
  simp only [LinearMap.comp_apply, LinearMap.mul'_apply, map_mul,
    TensorProduct.map_tmul]
  simp [DistribMulActionHom.toLinearMap]

theorem algHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    f.toLinearMap ∘ₗ LinearMap.mul' R A = (LinearMap.mul' R B) ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap) :=
nonUnitalAlgHom_comp_mul f.toNonUnitalAlgHom

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

set_option linter.deprecated false in
theorem comul_comp_nonUnitalAlgHom_adjoint (f : A →ₙₐ[ℂ] B) :
    Coalgebra.comul ∘ₗ (LinearMap.adjoint f.toLinearMap)
      = ((LinearMap.adjoint f.toLinearMap) ⊗ₘ (LinearMap.adjoint f.toLinearMap)) ∘ₗ Coalgebra.comul :=
by
  simp_rw [comul_eq_mul_adjoint, ← TensorProduct.map_adjoint, ← LinearMap.adjoint_comp,
    nonUnitalAlgHom_comp_mul f]

theorem comul_comp_algHom_adjoint (f : A →ₐ[ℂ] B) :
  Coalgebra.comul ∘ₗ (LinearMap.adjoint f.toLinearMap)
    = ((LinearMap.adjoint f.toLinearMap) ⊗ₘ (LinearMap.adjoint f.toLinearMap)) ∘ₗ Coalgebra.comul :=
comul_comp_nonUnitalAlgHom_adjoint f.toNonUnitalAlgHom

set_option linter.deprecated false in
theorem schurMul_nonUnitalAlgHom_comp_coalgHom {C D : Type*}
  [Semiring C] [Semiring D]
  [Module ℂ C] [Module ℂ D]
  [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
  [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
  (g : C →ₙₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
  (g.toLinearMap ∘ₗ x ∘ₗ f.toLinearMap) •ₛ (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap)
    = g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ f.toLinearMap :=
by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, nonUnitalAlgHom_comp_mul, LinearMap.comp_assoc,
    ← f.map_comp_comul]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]

theorem schurMul_algHom_comp_coalgHom {C D : Type*}
  [Semiring C] [Semiring D]
  [Module ℂ C] [Module ℂ D]
  [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
  [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
  (g : C →ₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
  (g.toLinearMap ∘ₗ x ∘ₗ f.toLinearMap) •ₛ (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap)
    = g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ f.toLinearMap :=
schurMul_nonUnitalAlgHom_comp_coalgHom (g.toNonUnitalAlgHom) f x y

set_option linter.deprecated false in
theorem schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint {C D : Type*}
  [Semiring C] [Semiring D]
  [Module ℂ C] [Module ℂ D]
  [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
  [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
  (g : C →ₙₐ[ℂ] D) (f : B →ₙₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
  (g.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint f.toLinearMap))
    •ₛ (g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap)
    = g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ LinearMap.adjoint f.toLinearMap :=
by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, nonUnitalAlgHom_comp_mul,
    LinearMap.comp_assoc, comul_comp_nonUnitalAlgHom_adjoint]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]

theorem schurMul_algHom_comp_algHom_adjoint {C D : Type*}
  [Semiring C] [Semiring D]
  [Module ℂ C] [Module ℂ D]
  [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
  [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
  (g : C →ₐ[ℂ] D) (f : B →ₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
  (g.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint f.toLinearMap))
    •ₛ (g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap)
    = g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ LinearMap.adjoint f.toLinearMap :=
schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint g.toNonUnitalAlgHom f.toNonUnitalAlgHom x y

protected lemma QuantumSet.schurMul_algHom_comp_algHom_adjoint {A B C D : Type*}
  [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  [starAlgebra C] [starAlgebra D] [QuantumSet C] [QuantumSet D]
  (g : C →ₐ[ℂ] D) (f : B →ₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
  (g.toLinearMap ∘ₗ x ∘ₗ LinearMap.adjoint f.toLinearMap) •ₛ g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap =
    g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ LinearMap.adjoint f.toLinearMap :=
schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint g.toNonUnitalAlgHom f.toNonUnitalAlgHom x y

theorem schurMul_one_iff_one_schurMul_of_isReal
  {A B : Type*} [starAlgebra A] [starAlgebra B]
  [QuantumSet A] [QuantumSet B]
  {x y z : A →ₗ[ℂ] B}
  (hx : LinearMap.IsReal x) (hy : LinearMap.IsReal y) (hz : LinearMap.IsReal z) :
    x •ₛ y = z ↔ y •ₛ x = z :=
by
  rw [LinearMap.real_inj_eq, schurMul_real, x.isReal_iff.mp hx, y.isReal_iff.mp hy,
    z.isReal_iff.mp hz]

theorem schurMul_reflexive_of_isReal
  {A : Type*} [starAlgebra A] [QuantumSet A]
  {x : A →ₗ[ℂ] A} (hx : LinearMap.IsReal x) :
  x •ₛ 1 = 1 ↔ 1 •ₛ x = 1 :=
schurMul_one_iff_one_schurMul_of_isReal hx LinearMap.isRealOne LinearMap.isRealOne

theorem schurMul_irreflexive_of_isReal
  {A : Type*} [starAlgebra A] [QuantumSet A]
  {x : A →ₗ[ℂ] A} (hx : LinearMap.IsReal x) :
  x •ₛ 1 = 0 ↔ 1 •ₛ x = 0 :=
schurMul_one_iff_one_schurMul_of_isReal hx LinearMap.isRealOne LinearMap.isRealZero

lemma schurIdempotent_iff_Psi_isIdempotentElem {A B : Type*} [starAlgebra A] [starAlgebra B]
    [hA : QuantumSet A] [QuantumSet B] (f : A →ₗ[ℂ] B) (t r : ℝ) :
  f •ₛ f = f ↔ IsIdempotentElem (hA.Psi t r f) :=
by
  simp_rw [IsIdempotentElem, ← Psi.schurMul, Function.Injective.eq_iff (LinearEquiv.injective _)]
