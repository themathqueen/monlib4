/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Algebra.Bilinear
import Monlib.LinearAlgebra.KroneckerToTensor
import Monlib.LinearAlgebra.MyTensorProduct
import Monlib.LinearAlgebra.Nacgor

#align_import linear_algebra.mul''

/-!

# linear_map.mul''

this defines the multiplication map $M_{n\times n} \to M_n$

-/


open Matrix

open scoped Matrix Kronecker BigOperators

variable {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem commutes_with_unit_iff (f : A →ₗ[R] B) :
    f ∘ₗ Algebra.linearMap R A = Algebra.linearMap R B ↔ f 1 = 1 :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, _root_.map_smul]
  refine' ⟨fun h => _, fun h x => by rw [h]⟩
  · specialize h 1
    simp_rw [one_smul] at h
    exact h

theorem commutes_with_mul'_iff (f : A →ₗ[R] B) :
    LinearMap.mul' R B ∘ₗ TensorProduct.map f f = f ∘ₗ LinearMap.mul' R A ↔
      ∀ x y : A, f (x * y) = f x * f y :=
  by
  simp_rw [TensorProduct.ext_iff, LinearMap.comp_apply, TensorProduct.map_apply,
    LinearMap.mul'_apply, eq_comm]

-- MOVE:
theorem Matrix.KroneckerProduct.ext_iff {R P n₁ n₂ : Type _} [Fintype n₁] [Fintype n₂]
    [CommSemiring R] [AddCommMonoid P] [Module R P] [DecidableEq n₁] [DecidableEq n₂]
    {g h : Matrix (n₁ × n₂) (n₁ × n₂) R →ₗ[R] P} :
    g = h ↔ ∀ (x : Matrix n₁ n₁ R) (y : Matrix n₂ n₂ R), g (x ⊗ₖ y) = h (x ⊗ₖ y) :=
  by
  refine' ⟨fun h x y => by rw [h], fun h => _⟩
  rw [LinearMap.ext_iff]
  intro x
  rw [kmul_representation x]
  simp_rw [map_sum, _root_.map_smul, h _ _]

private def mul_map_aux (𝕜 X : Type _) [RCLike 𝕜] [NormedAddCommGroupOfRing X] [NormedSpace 𝕜 X]
    [SMulCommClass 𝕜 X X] [IsScalarTower 𝕜 X X] [FiniteDimensional 𝕜 X] : X →ₗ[𝕜] X →L[𝕜] X
    where
  toFun x :=
    { toFun := LinearMap.mul 𝕜 X x
      map_add' := map_add _
      map_smul' := map_smul _ }
  map_add' x y := by
    ext;
    simp_rw [map_add, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      ContinuousLinearMap.add_apply]
    rfl
  map_smul' r x := by
    ext
    simp_rw [_root_.map_smul, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rfl

def LinearMap.mulToClm (𝕜 X : Type _) [RCLike 𝕜] [NormedAddCommGroupOfRing X] [NormedSpace 𝕜 X]
    [SMulCommClass 𝕜 X X] [IsScalarTower 𝕜 X X] [FiniteDimensional 𝕜 X] : X →L[𝕜] X →L[𝕜] X
    where
  toFun := mul_map_aux 𝕜 X
  map_add' := map_add _
  map_smul' := _root_.map_smul _
  cont := by
    simp only [LinearMap.mk_coe]
    exact map_continuous _

theorem LinearMap.mulToClm_apply {𝕜 X : Type _} [RCLike 𝕜] [NormedAddCommGroupOfRing X]
    [NormedSpace 𝕜 X] [SMulCommClass 𝕜 X X] [IsScalarTower 𝕜 X X] [FiniteDimensional 𝕜 X]
    (x y : X) : LinearMap.mulToClm 𝕜 X x y = x * y :=
  rfl
