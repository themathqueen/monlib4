/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Opposites
import Mathlib.Algebra.Star.Basic
import Monlib.LinearAlgebra.TensorProduct.Lemmas

/-!

# The multiplicative opposite linear equivalence

This file defines the multiplicative opposite linear equivalence as linear maps `op` and `unop`. This is essentially `mul_opposite.op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ` but defined as linear maps rather than `linear_equiv`.

We also define `ten_swap` which is the linear automorphisms on `A ⊗[R] Aᵐᵒᵖ` given by swapping the tensor factors while keeping the `ᵒᵖ` in place, i.e., `ten_swap (x ⊗ₜ op y) = y ⊗ₜ op x`.

-/


variable {R A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A]

abbrev op (R : Type*) {A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A] :=
(MulOpposite.opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ)

@[simp]
theorem op_apply (x : A) : op R x = MulOpposite.op x :=
  rfl

abbrev unop (R : Type*) {A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A] :
  Aᵐᵒᵖ ≃ₗ[R] A :=
(op R).symm

@[simp]
theorem unop_apply (x : Aᵐᵒᵖ) : unop R x = MulOpposite.unop x :=
  rfl

@[simp]
theorem unop_op (x : A) : unop R (op R x) = x :=
  rfl

@[simp]
theorem op_unop (x : Aᵐᵒᵖ) : op R (unop R x) = x :=
  rfl

theorem unop_comp_op : (unop R).toLinearMap ∘ₗ (op R).toLinearMap = (1 : A →ₗ[R] A) :=
  rfl

theorem op_comp_unop : (op R).toLinearMap ∘ₗ (unop R).toLinearMap = (1 : Aᵐᵒᵖ →ₗ[R] Aᵐᵒᵖ) :=
  rfl

theorem op_star_apply [Star A] (a : A) :
    op R (star a) = star (op R a) :=
  rfl

theorem unop_star_apply [Star A] (a : Aᵐᵒᵖ) :
    unop R (star a) = star (unop R a) :=
  rfl

open scoped TensorProduct

variable {B : Type*} [AddCommMonoid B] [Module R B]
noncomputable abbrev tenSwap (R : Type*)
  {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
  [CommSemiring R] [Module R A] [Module R B] :
    A ⊗[R] Bᵐᵒᵖ ≃ₗ[R] B ⊗[R] Aᵐᵒᵖ :=
(TensorProduct.comm R A Bᵐᵒᵖ).trans
  (LinearEquiv.TensorProduct.map (unop R) (op R))

@[simp]
theorem tenSwap_apply (x : A) (y : Bᵐᵒᵖ) :
    tenSwap R (x ⊗ₜ[R] y) = MulOpposite.unop y ⊗ₜ[R] MulOpposite.op x :=
  rfl

theorem tenSwap_apply' (x : A) (y : B) : tenSwap R (x ⊗ₜ MulOpposite.op y) = y ⊗ₜ[R] MulOpposite.op x :=
  rfl

@[simp]
theorem tenSwap_symm :
  (tenSwap R).symm = (tenSwap R : B ⊗[R] Aᵐᵒᵖ ≃ₗ[R] A ⊗[R] Bᵐᵒᵖ) :=
by
  rw [← LinearEquiv.toLinearMap_inj]
  rw [TensorProduct.ext_iff']
  intro _ _
  rfl

theorem tenSwap_comp_tenSwap : (tenSwap R).toLinearMap ∘ₗ (tenSwap R).toLinearMap = (1 : A ⊗[R] Bᵐᵒᵖ →ₗ[R] A ⊗[R] Bᵐᵒᵖ) :=
  by
  apply TensorProduct.ext'
  intro _ _
  rfl

@[simp]
theorem tenSwap_apply_tenSwap (x : A ⊗[R] Bᵐᵒᵖ) :
    tenSwap R (tenSwap R x) = x := by
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
    tenSwap_comp_tenSwap]; rfl
