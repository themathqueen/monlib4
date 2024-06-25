/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Basic

#align_import linear_algebra.my_tensor_product

/-!
 # Some lemmas about `tensor_product`
-/


open scoped TensorProduct BigOperators

namespace TensorProduct

variable {R M N P Q : Type _} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [AddCommMonoid Q] [Module R M] [Module R N] [Module R P] [Module R Q]

protected theorem ext_iff {g h : M ⊗[R] N →ₗ[R] P} :
    g = h ↔ ∀ (x : M) (y : N), g (x ⊗ₜ[R] y) = h (x ⊗ₜ[R] y) :=
  ⟨fun h x y => by rw [h], TensorProduct.ext'⟩

theorem ext'_iff {g h : (M ⊗[R] N) ⊗[R] Q →ₗ[R] P} :
    (∀ x : (M ⊗[R] N) ⊗[R] Q, g x = h x) ↔
      ∀ (x : M) (y : N) (z : Q), g ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = h ((x ⊗ₜ[R] y) ⊗ₜ[R] z) :=
  by
  refine' ⟨fun h x y z => by rw [h], _⟩
  rw [← LinearMap.ext_iff]
  exact TensorProduct.ext_threefold

@[simp]
theorem map_apply (f : M →ₗ[R] P) (t : N →ₗ[R] Q) (x : M) (y : N) :
    (TensorProduct.map f t) (x ⊗ₜ[R] y) = f x ⊗ₜ t y :=
  rfl

@[simp]
theorem comm_commutes {g : M ⊗[R] N →ₗ[R] P} {h : M ⊗[R] N →ₗ[R] Q} :
    (TensorProduct.comm R P Q).toLinearMap ∘ₗ TensorProduct.map g h =
      TensorProduct.map h g ∘ₗ (TensorProduct.comm R (M ⊗[R] N) (M ⊗[R] N)).toLinearMap :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.map_apply, TensorProduct.comm_tmul]

theorem comm_commutes' {g : M →ₗ[R] M} {h : M →ₗ[R] R} :
    (TensorProduct.comm R M R).toLinearMap ∘ₗ TensorProduct.map g h =
      TensorProduct.map h g ∘ₗ (TensorProduct.comm R M M).toLinearMap :=
  by
  simp_rw [TensorProduct.ext_iff, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, TensorProduct.map_apply, TensorProduct.comm_tmul,
    forall₂_true_iff]

theorem assoc_comp_map {R : Type _} [CommSemiring R] {M N M₂ N₂ P Q : Type _} [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R M₂] [Module R N₂] [Module R P] [Module R Q] (f : M →ₗ[R] P)
    (t : N →ₗ[R] Q) (s : M₂ →ₗ[R] N₂) :
    (TensorProduct.assoc R P Q N₂).toLinearMap ∘ₗ TensorProduct.map (TensorProduct.map f t) s =
      TensorProduct.map f (TensorProduct.map t s) ∘ₗ (TensorProduct.assoc R M N M₂).toLinearMap :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_apply, TensorProduct.assoc_tmul, TensorProduct.map_apply]

theorem ext_threefold' {R : Type _} [CommSemiring R] {M N P Q : Type _} [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P]
    [Module R Q] {g h : M ⊗[R] N ⊗[R] P →ₗ[R] Q}
    (H : ∀ (x : M) (y : N) (z : P), g (x ⊗ₜ[R] y ⊗ₜ[R] z) = h (x ⊗ₜ[R] y ⊗ₜ[R] z)) : g = h :=
  by
  apply TensorProduct.ext
  ext1 x
  rw [TensorProduct.mk, TensorProduct.ext_iff]
  intro y z
  exact H x y z

theorem assoc_symm_comp_map {R : Type _} [CommSemiring R] {M N M₂ N₂ P Q : Type _} [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R M₂] [Module R N₂] [Module R P] [Module R Q] (f : M →ₗ[R] P)
    (t : N →ₗ[R] Q) (s : M₂ →ₗ[R] N₂) :
    (TensorProduct.assoc R P Q N₂).symm.toLinearMap ∘ₗ TensorProduct.map f (TensorProduct.map t s) =
      TensorProduct.map (TensorProduct.map f t) s ∘ₗ
        (TensorProduct.assoc R M N M₂).symm.toLinearMap :=
  by
  apply TensorProduct.ext_threefold'
  intro x y z
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_apply, TensorProduct.assoc_symm_tmul, TensorProduct.map_apply]

theorem comm_map {R : Type _} [CommSemiring R] {M N P Q : Type _} [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P]
    [Module R Q] (f : M →ₗ[R] P) (t : N →ₗ[R] Q) :
    (TensorProduct.comm R P Q).toLinearMap ∘ₗ TensorProduct.map f t =
      TensorProduct.map t f ∘ₗ (TensorProduct.comm R M N).toLinearMap :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_apply, TensorProduct.comm_tmul, TensorProduct.map_apply]

theorem comm_symm_map {R : Type _} [CommSemiring R] {M N P Q : Type _} [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P]
    [Module R Q] (f : M →ₗ[R] P) (t : N →ₗ[R] Q) :
    (TensorProduct.comm R P Q).symm.toLinearMap ∘ₗ TensorProduct.map t f =
      TensorProduct.map f t ∘ₗ (TensorProduct.comm R M N).symm.toLinearMap :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_apply, TensorProduct.comm_symm_tmul, TensorProduct.map_apply]

protected theorem map_sum {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R M₁] [Module R M₂]
    [Module R N₁] [Module R N₂] (x : M₁ →ₗ[R] M₂) {α : Type _} (s : Finset α)
    (n : α → N₁ →ₗ[R] N₂) : map x (∑ a : α in s, n a) = ∑ a : α in s, map x (n a) := by
  simp_rw [TensorProduct.ext_iff, LinearMap.sum_apply, map_apply, LinearMap.coeFn_sum,
    Finset.sum_apply, tmul_sum, forall₂_true_iff]

theorem sum_map {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R M₁] [Module R M₂]
    [Module R N₁] [Module R N₂] {α : Type _} (s : Finset α) (n : α → N₁ →ₗ[R] N₂)
    (x : M₁ →ₗ[R] M₂) : map (∑ a : α in s, n a) x = ∑ a : α in s, map (n a) x := by
  simp_rw [TensorProduct.ext_iff, LinearMap.sum_apply, map_apply, LinearMap.coeFn_sum,
    Finset.sum_apply, sum_tmul, forall₂_true_iff]

protected theorem map_smul {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R M₁] [Module R M₂]
    [Module R N₁] [Module R N₂] (x : M₁ →ₗ[R] M₂) (y : N₁ →ₗ[R] N₂) (a : R) :
    map x (a • y) = a • map x y := by
  simp_rw [TensorProduct.ext_iff, LinearMap.smul_apply, map_apply, LinearMap.smul_apply, tmul_smul,
    forall₂_true_iff]

theorem smul_map {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R M₁] [Module R M₂]
    [Module R N₁] [Module R N₂] (x : M₁ →ₗ[R] M₂) (y : N₁ →ₗ[R] N₂) (a : R) :
    map (a • x) y = a • map x y := by
  simp_rw [TensorProduct.ext_iff, LinearMap.smul_apply, map_apply, LinearMap.smul_apply, smul_tmul',
    forall₂_true_iff]

-- MOVE:
theorem add_map {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R M₁] [Module R M₂]
    [Module R N₁] [Module R N₂] (x y : M₁ →ₗ[R] M₂) (z : N₁ →ₗ[R] N₂) :
    TensorProduct.map (x + y) z = TensorProduct.map x z + TensorProduct.map y z :=
  by
  apply ext'
  intro u v
  simp only [TensorProduct.map_apply, LinearMap.add_apply, add_tmul]

protected theorem map_zero {R : Type _} [CommSemiring R] {M₁ N₁ M₂ N₂ : Type _} [AddCommMonoid M₁]
    [AddCommMonoid N₁] [AddCommMonoid M₂] [AddCommMonoid N₂] [Module R M₁] [Module R N₁]
    [Module R M₂] [Module R N₂] (x : M₁ →ₗ[R] N₁) : TensorProduct.map x (0 : M₂ →ₗ[R] N₂) = 0 :=
  by
  apply TensorProduct.ext'
  intros
  simp_rw [TensorProduct.map_tmul, LinearMap.zero_apply, TensorProduct.tmul_zero]

protected theorem zero_map {R : Type _} [CommSemiring R] {M₁ N₁ M₂ N₂ : Type _} [AddCommMonoid M₁]
    [AddCommMonoid N₁] [AddCommMonoid M₂] [AddCommMonoid N₂] [Module R M₁] [Module R N₁]
    [Module R M₂] [Module R N₂] (x : M₁ →ₗ[R] N₁) : TensorProduct.map (0 : M₂ →ₗ[R] N₂) x = 0 :=
  by
  apply TensorProduct.ext'
  intros
  simp_rw [TensorProduct.map_tmul, LinearMap.zero_apply, TensorProduct.zero_tmul]

theorem tmul_eq_zero {R : Type _} [Field R] {M N : Type _} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] {x : M} {y : N} : x ⊗ₜ[R] y = 0 ↔ x = 0 ∨ y = 0 :=
  by
  let b₁ := Basis.ofVectorSpace R M
  let b₂ := Basis.ofVectorSpace R N
  constructor
  · intro h
    apply_fun (b₁.tensorProduct b₂).repr at h
    simp only [Basis.tensorProduct_repr_tmul_apply, DFunLike.ext_iff, Prod.forall, map_zero,
      Finsupp.zero_apply, mul_eq_zero] at h
    simp only [Basis.ext_elem_iff b₁, b₂.ext_elem_iff, map_zero, Finsupp.zero_apply, ←
      forall_or_left, ← forall_or_right]
    exact λ _ _ => h _ _
  · rintro (rfl | rfl)
    exact TensorProduct.zero_tmul _ _
    exact TensorProduct.tmul_zero _ _

theorem zero_tmul_zero {R : Type _} [CommSemiring R] {M N : Type _} [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] : (0 : M ⊗[R] N) = 0 ⊗ₜ 0 := by
  rw [TensorProduct.zero_tmul]

theorem map_mul'_commute_iff {R M N : Type _} [CommSemiring R] [NonUnitalNonAssocSemiring M]
    [NonUnitalNonAssocSemiring N] [Module R M] [Module R N] [SMulCommClass R M M]
    [SMulCommClass R N N] [IsScalarTower R M M] [IsScalarTower R N N] {f : M →ₗ[R] N} :
    (LinearMap.mul' R N).comp (TensorProduct.map f f) = f.comp (LinearMap.mul' R M) ↔
      ∀ x y, f (x * y) = f x * f y :=
  by
  simp only [TensorProduct.ext_iff, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, eq_comm]

end TensorProduct

theorem Algebra.TensorProduct.map_toLinearMap {R M N P Q : Type _} [CommSemiring R] [Semiring M]
    [Semiring N] [Semiring P] [Semiring Q] [Algebra R M] [Algebra R N] [Algebra R P] [Algebra R Q]
    (f : M →ₐ[R] N) (g : P →ₐ[R] Q) :
    AlgHom.toLinearMap (Algebra.TensorProduct.map f g)
      = _root_.TensorProduct.map (AlgHom.toLinearMap f) (AlgHom.toLinearMap g) :=
  rfl

theorem AlgHom.commute_map_mul' {R M N : Type _} [CommSemiring R] [Semiring M] [Semiring N]
    [Algebra R M] [Algebra R N] (f : M →ₐ[R] N) :
    (LinearMap.mul' R N).comp (Algebra.TensorProduct.map f f).toLinearMap =
      f.toLinearMap.comp (LinearMap.mul' R M) :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mul'_apply,
    Algebra.TensorProduct.map_tmul, _root_.map_mul]

theorem AlgHom.commute_map_mul'_apply {R M N : Type _} [CommSemiring R] [Semiring M] [Semiring N]
    [Algebra R M] [Algebra R N] (f : M →ₐ[R] N) (x : M ⊗[R] M) :
    (LinearMap.mul' R N) ((Algebra.TensorProduct.map f f) x) = f ((LinearMap.mul' R M) x) :=
  by
  simp only [← LinearMap.comp_apply, ← AlgHom.toLinearMap_apply]
  revert x
  rw [← LinearMap.ext_iff]
  exact AlgHom.commute_map_mul' _

open TensorProduct

theorem TensorProduct.map_add {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R M₁]
    [Module R M₂] [Module R N₁] [Module R N₂] (x y : M₁ →ₗ[R] M₂) (z : N₁ →ₗ[R] N₂) :
    TensorProduct.map z (x + y) = map z x + map z y :=
  by
  rw [TensorProduct.ext_iff]
  intros
  simp only [TensorProduct.map_tmul, tmul_add, add_tmul, LinearMap.add_apply]

theorem TensorProduct.of_basis_eq_span {𝕜 : Type _} {E : Type _} {F : Type _} [CommSemiring 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] (x : TensorProduct 𝕜 E F)
    {ι₁ ι₂ : Type _} [Fintype ι₁] [Fintype ι₂] (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F) :
    x = ∑ i : ι₁, ∑ j : ι₂, (b₁.tensorProduct b₂).repr x (i, j) • b₁ i ⊗ₜ[𝕜] b₂ j :=
  x.induction_on
  (by simp only [map_zero, Finsupp.zero_apply, zero_smul, Finset.sum_const_zero])
  (fun α₁ α₂ => by
    simp_rw [Basis.tensorProduct_repr_tmul_apply, ← TensorProduct.smul_tmul_smul, ←
      TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, Basis.sum_repr])
  (fun a b ha hb => by
    simp_rw [_root_.map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← ha, ← hb])
