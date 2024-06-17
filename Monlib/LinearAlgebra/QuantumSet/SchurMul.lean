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
import Monlib.LinearAlgebra.TensorFinite
import Monlib.LinearAlgebra.Ips.OpUnop
import Monlib.LinearAlgebra.LmulRmul
import Monlib.LinearAlgebra.Nacgor
import Monlib.LinearAlgebra.CoalgebraFiniteDimensional

#align_import quantum_graph.schur_idempotent

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
  [NormedAddCommGroupOfRing B] [NormedAddCommGroupOfRing C]
  [hB : QuantumSet B] [hC : QuantumSet C] :
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
open scoped schurMul

variable {A B C : Type _}
  [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B] [NormedAddCommGroupOfRing C]
  [hA : QuantumSet A] [hB : QuantumSet B] [hC : QuantumSet C]

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
    LinearMap.mul'_apply, smul_mul_smul, ← TensorProduct.inner_tmul, ← Finset.sum_smul, ← inner_sum,
    h, comul_eq_mul_adjoint, LinearMap.adjoint_inner_right, LinearMap.mul'_apply]

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

theorem schurMul_real (x y : A →ₗ[ℂ] B) :
    LinearMap.real (x •ₛ y : A →ₗ[ℂ] B) = (LinearMap.real y) •ₛ (LinearMap.real x) :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rankOne
  obtain ⟨γ, ζ, rfl⟩ := y.exists_sum_rankOne
  simp only [map_sum, LinearMap.real_sum, LinearMap.sum_apply, schurMul.apply_rankOne]
  simp_rw [rankOne_real, schurMul.apply_rankOne, ← map_mul, ← StarMul.star_mul]
  rw [Finset.sum_comm]

theorem schurMul_one_right_rankOne (a b : B) :
    (↑|a⟩⟨b|) •ₛ 1 = lmul a * (LinearMap.adjoint (lmul b : l(B))) :=
  by
  simp_rw [LinearMap.ext_iff_inner_map]
  intro u
  let f := stdOrthonormalBasis ℂ B
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm f]
  simp_rw [map_sum, LinearMap.sum_apply, schurMul.apply_rankOne, ContinuousLinearMap.coe_coe,
    rankOne_apply, LinearMap.mul_apply, lmul_apply, sum_inner, inner_smul_left,
    hB.inner_star_left,
    inner_conj_symm, OrthonormalBasis.sum_inner_mul_inner, lmul_adjoint, lmul_apply]

theorem schurMul_one_left_rankOne (a b : B) :
    (1 : l(B)) •ₛ (|a⟩⟨b|) = (rmul a : l(B)) * (LinearMap.adjoint (rmul b : l(B))) :=
  by
  simp_rw [← ext_inner_map]
  intro u
  let f := stdOrthonormalBasis ℂ B
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm f, map_sum, LinearMap.sum_apply]
  simp_rw [schurMul.apply_rankOne, LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, LinearMap.mul_apply, rmul_apply, sum_inner, inner_smul_left,
    QuantumSet.inner_conj_left, inner_conj_symm,
    OrthonormalBasis.sum_inner_mul_inner, ← QuantumSet.inner_conj_left,
    rmul_adjoint, rmul_apply]

theorem Psi.schurMul (r₁ r₂ : ℝ)
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

theorem schurMul_assoc (f g h : A →ₗ[ℂ] B) :
  (f •ₛ g) •ₛ h = f •ₛ (g •ₛ h) :=
by
  apply_fun hA.Psi 0 0 using LinearEquiv.injective _
  simp_rw [Psi.schurMul, mul_assoc]

theorem algHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    f.toLinearMap ∘ₗ LinearMap.mul' R A = (LinearMap.mul' R B) ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap) :=
by
  rw [TensorProduct.ext_iff]
  intro a b
  simp only [LinearMap.comp_apply, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, map_mul,
    TensorProduct.map_tmul]

theorem comul_comp_algHom_adjoint (f : A →ₐ[ℂ] B) :
    Coalgebra.comul ∘ₗ (LinearMap.adjoint f.toLinearMap)
      = ((LinearMap.adjoint f.toLinearMap) ⊗ₘ (LinearMap.adjoint f.toLinearMap)) ∘ₗ Coalgebra.comul :=
by
  simp_rw [comul_eq_mul_adjoint, ← TensorProduct.map_adjoint, ← LinearMap.adjoint_comp,
    algHom_comp_mul]

theorem schurMul_algHom_comp_coalgHom {D : Type*} [NormedAddCommGroupOfRing D]
  [hD : QuantumSet D] (g : C →ₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
  (g.toLinearMap ∘ₗ x ∘ₗ f.toLinearMap) •ₛ (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap)
    = g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ f.toLinearMap :=
by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, algHom_comp_mul, LinearMap.comp_assoc,
    ← f.map_comp_comul]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]

theorem schurMul_algHom_comp_algHom_adjoint {D : Type*} [NormedAddCommGroupOfRing D]
  [hD : QuantumSet D] (g : C →ₐ[ℂ] D) (f : B →ₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
  (g.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint f.toLinearMap))
    •ₛ (g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap)
    = g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ LinearMap.adjoint f.toLinearMap :=
by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, algHom_comp_mul,
    LinearMap.comp_assoc, comul_comp_algHom_adjoint]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]
