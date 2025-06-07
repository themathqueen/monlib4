/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Pi
-- import Mathlib.LinearAlgebra.ProjectiveSpace.Basic
import Monlib.Preq.Ites

/-!

# Direct sum from _ to _

 This file includes the definition of `direct_sum_from_to` which is a linear map from `M i` to `M j`.

-/


def directSumFromTo {R : Type*} [Semiring R] {ι₁ : Type*} [DecidableEq ι₁] {M₁ : ι₁ → Type*}
    [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₁ : ι₁, Module R (M₁ i₁)] (i j : ι₁) : M₁ i →ₗ[R] M₁ j :=
  LinearMap.proj j ∘ₗ LinearMap.single _ _ i

theorem directSumFromTo_apply_same {R : Type _} [Semiring R] {ι₁ : Type _} [DecidableEq ι₁]
    {M₁ : ι₁ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₁ : ι₁, Module R (M₁ i₁)] (i : ι₁) :
    directSumFromTo i i = (1 : M₁ i →ₗ[R] M₁ i) :=
  by
  ext1 x
  simp only [directSumFromTo, LinearMap.comp_apply, LinearMap.coe_single, Pi.single,
    LinearMap.coe_proj, Function.eval_apply, Function.update_apply, Pi.zero_apply, ite_apply_lm,
    LinearMap.zero_apply]
  simp

theorem directSumFromTo_apply_ne_same {R : Type _} [Semiring R] {ι₁ : Type _} [DecidableEq ι₁]
    {M₁ : ι₁ → Type _} [∀ i₁ : ι₁, AddCommGroup (M₁ i₁)] [∀ i₁ : ι₁, Module R (M₁ i₁)] {i j : ι₁}
    (h : j ≠ i) : directSumFromTo i j = (0 : M₁ i →ₗ[R] M₁ j) :=
  by
  ext1 x
  simp only [directSumFromTo, LinearMap.comp_apply, LinearMap.coe_single, Pi.single,
    LinearMap.coe_proj, Function.eval_apply, Function.update_apply, Pi.zero_apply, ite_apply_lm,
    LinearMap.zero_apply]
  simp [h]
