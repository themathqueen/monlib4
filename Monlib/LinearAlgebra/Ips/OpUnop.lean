/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Opposites
import Mathlib.Algebra.Star.Basic

#align_import linear_algebra.my_ips.op_unop

/-!

# The multiplicative opposite linear equivalence

This file defines the multiplicative opposite linear equivalence as linear maps `op` and `unop`. This is essentially `mul_opposite.op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ` but defined as linear maps rather than `linear_equiv`.

We also define `ten_swap` which is the linear automorphisms on `A ⊗[R] Aᵐᵒᵖ` given by swapping the tensor factors while keeping the `ᵒᵖ` in place, i.e., `ten_swap (x ⊗ₜ op y) = y ⊗ₜ op x`.

-/


variable {R A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A]

def op : A →ₗ[R] Aᵐᵒᵖ :=
  ((MulOpposite.opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ)

theorem op_apply (x : A) : (op : A →ₗ[R] Aᵐᵒᵖ) x = MulOpposite.op x :=
  rfl

def unop : Aᵐᵒᵖ →ₗ[R] A :=
  ((MulOpposite.opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A)

theorem unop_apply (x : Aᵐᵒᵖ) : (unop : Aᵐᵒᵖ →ₗ[R] A) x = MulOpposite.unop x :=
  rfl

theorem unop_op (x : A) : (unop : Aᵐᵒᵖ →ₗ[R] A) ((op : A →ₗ[R] Aᵐᵒᵖ) x) = x :=
  rfl

theorem op_unop (x : Aᵐᵒᵖ) : (op : A →ₗ[R] Aᵐᵒᵖ) ((unop : Aᵐᵒᵖ →ₗ[R] A) x) = x :=
  rfl

theorem unop_comp_op : unop ∘ₗ op = (1 : A →ₗ[R] A) :=
  rfl

theorem op_comp_unop : op ∘ₗ unop = (1 : Aᵐᵒᵖ →ₗ[R] Aᵐᵒᵖ) :=
  rfl

theorem op_star_apply [Star A] (a : A) :
    (op : A →ₗ[R] Aᵐᵒᵖ) (star a) = star ((op : A →ₗ[R] Aᵐᵒᵖ) a) :=
  rfl

theorem unop_star_apply [Star A] (a : Aᵐᵒᵖ) :
    (unop : Aᵐᵒᵖ →ₗ[R] A) (star a) = star ((unop : Aᵐᵒᵖ →ₗ[R] A) a) :=
  rfl

open scoped TensorProduct

variable {B : Type*} [AddCommMonoid B] [Module R B]
noncomputable def tenSwap : A ⊗[R] Bᵐᵒᵖ →ₗ[R] B ⊗[R] Aᵐᵒᵖ :=
  TensorProduct.map (unop : Bᵐᵒᵖ →ₗ[R] B) (op : A →ₗ[R] Aᵐᵒᵖ) ∘ₗ
    (TensorProduct.comm R A Bᵐᵒᵖ).toLinearMap

theorem tenSwap_apply (x : A) (y : Bᵐᵒᵖ) :
    tenSwap (x ⊗ₜ[R] y) = MulOpposite.unop y ⊗ₜ[R] MulOpposite.op x :=
  rfl

theorem tenSwap_apply' (x : A) (y : B) : tenSwap (x ⊗ₜ MulOpposite.op y) = y ⊗ₜ[R] MulOpposite.op x :=
  rfl

theorem tenSwap_tenSwap : tenSwap ∘ₗ tenSwap = (1 : A ⊗[R] Bᵐᵒᵖ →ₗ[R] A ⊗[R] Bᵐᵒᵖ) :=
  by
  apply TensorProduct.ext'
  intros
  simp only [LinearMap.comp_apply, tenSwap_apply, MulOpposite.unop_op, MulOpposite.op_unop,
    LinearMap.one_apply]

theorem tenSwap_apply_tenSwap (x : A ⊗[R] Bᵐᵒᵖ) : tenSwap (tenSwap x) = x := by
  rw [← LinearMap.comp_apply, tenSwap_tenSwap, LinearMap.one_apply]

def tenSwap_injective : Function.Injective (tenSwap : A ⊗[R] Bᵐᵒᵖ →ₗ[R] B ⊗[R] Aᵐᵒᵖ) :=
  by
  intro a b h
  rw [← tenSwap_apply_tenSwap a, h, tenSwap_apply_tenSwap]
