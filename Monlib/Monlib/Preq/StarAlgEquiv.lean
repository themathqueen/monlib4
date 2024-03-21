/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Algebra.Star.StarAlgHom
import Algebra.Algebra.Equiv
import Algebra.Ring.Idempotents

#align_import preq.star_alg_equiv

/-!
 # Some stuff on star algebra equivalences

 This file contains some obvious definitions and lemmas on star algebra equivalences.
-/


theorem AlgEquiv.comp_inj {R A B C : Type _} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : B ≃ₐ[R] C) (S T : A →ₗ[R] B) :
    f.toLinearMap ∘ₗ S = f.toLinearMap ∘ₗ T ↔ S = T := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    f.injective.eq_iff]

theorem AlgEquiv.inj_comp {R A B C : Type _} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : C ≃ₐ[R] A) (S T : A →ₗ[R] B) :
    S ∘ₗ f.toLinearMap = T ∘ₗ f.toLinearMap ↔ S = T :=
  by
  refine' ⟨fun h => _, fun h => by rw [h]⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] at h ⊢
  intro x
  specialize h (f.symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

def StarAlgEquiv.toAlgEquiv {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B] (f : A ≃⋆ₐ[R] B) : A ≃ₐ[R] B
    where
  toFun x := f x
  invFun x := f.symm x
  left_inv x := f.left_inv x
  right_inv x := f.right_inv x
  map_add' x y := f.map_add' x y
  map_mul' x y := f.map_mul' x y
  commutes' r := by simp_rw [Algebra.algebraMap_eq_smul_one, SMulHomClass.map_smul, _root_.map_one]

@[simp]
theorem StarAlgEquiv.coe_toAlgEquiv {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B] (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv = f :=
  rfl

@[hint_tactic]
theorem StarAlgEquiv.symm_apply_eq {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B] (f : A ≃⋆ₐ[R] B) (x : A) (y : B) :
    f.symm y = x ↔ y = f x :=
  Equiv.symm_apply_eq _

def StarAlgEquiv.ofAlgEquiv {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B] (f : A ≃ₐ[R] B)
    (hf : ∀ x : A, f (star x) = star (f x)) : A ≃⋆ₐ[R] B
    where
  toFun x := f x
  invFun x := f.symm x
  left_inv x := f.left_inv x
  right_inv x := f.right_inv x
  map_add' x y := f.map_add' x y
  map_mul' x y := f.map_mul' x y
  map_smul' r x := map_smul _ _ _
  map_star' x := hf x

@[simp]
theorem StarAlgEquiv.ofAlgEquiv_coe {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B] (f : A ≃ₐ[R] B)
    (hf : ∀ x : A, f (star x) = star (f x)) : ⇑(StarAlgEquiv.ofAlgEquiv f hf) = f :=
  rfl

@[simp]
theorem StarAlgEquiv.ofAlgEquiv_symm_coe {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Star A] [Star B] (f : A ≃ₐ[R] B)
    (hf : ∀ x : A, f (star x) = star (f x)) : ⇑(StarAlgEquiv.ofAlgEquiv f hf).symm = f.symm :=
  rfl

theorem StarAlgEquiv.comp_eq_iff {R E₁ E₂ E₃ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
    [AddCommGroup E₃] [Algebra R E₁] [Algebra R E₂] [Module R E₃] [Star E₁] [Star E₂]
    (f : E₁ ≃⋆ₐ[R] E₂) (x : E₂ →ₗ[R] E₃) (y : E₁ →ₗ[R] E₃) :
    x ∘ₗ f.toAlgEquiv.toLinearMap = y ↔ x = y ∘ₗ f.symm.toAlgEquiv.toLinearMap :=
  by
  constructor
  · intro h
    ext1
    rw [← h]
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv,
      StarAlgEquiv.apply_symm_apply]
  · rintro rfl
    ext1
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv,
      StarAlgEquiv.symm_apply_apply]

#print AlgEquiv.one_toLinearMap /-
theorem AlgEquiv.one_toLinearMap {R E : Type _} [CommSemiring R] [Semiring E] [Algebra R E] :
    (1 : E ≃ₐ[R] E).toLinearMap = 1 :=
  rfl
-/

theorem AlgEquiv.map_eq_zero_iff {R E₁ E₂ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
    [Algebra R E₁] [Algebra R E₂] (f : E₁ ≃ₐ[R] E₂) (x : E₁) : f x = 0 ↔ x = 0 :=
  RingEquiv.map_eq_zero_iff f.toRingEquiv

theorem StarAlgEquiv.map_eq_zero_iff {R E₁ E₂ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
    [Algebra R E₁] [Algebra R E₂] [Star E₁] [Star E₂] (f : E₁ ≃⋆ₐ[R] E₂) (x : E₁) :
    f x = 0 ↔ x = 0 :=
  AlgEquiv.map_eq_zero_iff f.toAlgEquiv _

theorem IsIdempotentElem.mulEquiv {H₁ H₂ : Type _} [Semiring H₁] [Semiring H₂] (f : H₁ ≃* H₂)
    (x : H₁) : IsIdempotentElem (f x) ↔ IsIdempotentElem x := by
  simp_rw [IsIdempotentElem, ← _root_.map_mul, Function.Injective.eq_iff f.injective]

theorem IsIdempotentElem.algEquiv {R H₁ H₂ : Type _} [CommSemiring R] [Semiring H₁] [Semiring H₂]
    [Algebra R H₁] [Algebra R H₂] (f : H₁ ≃ₐ[R] H₂) (x : H₁) :
    IsIdempotentElem (f x) ↔ IsIdempotentElem x :=
  IsIdempotentElem.mulEquiv f.toMulEquiv x

theorem IsIdempotentElem.starAlgEquiv {R H₁ H₂ : Type _} [CommSemiring R] [Semiring H₁]
    [Semiring H₂] [Algebra R H₁] [Algebra R H₂] [Star H₁] [Star H₂] (f : H₁ ≃⋆ₐ[R] H₂) (x : H₁) :
    IsIdempotentElem (f x) ↔ IsIdempotentElem x :=
  IsIdempotentElem.algEquiv f.toAlgEquiv x

theorem StarAlgEquiv.injective {R α β : Type _} [CommSemiring R] [Semiring α] [Semiring β]
    [Algebra R α] [Algebra R β] [Star α] [Star β] (f : α ≃⋆ₐ[R] β) : Function.Injective f :=
  AlgEquiv.injective f.toAlgEquiv

theorem AlgEquiv.eq_apply_iff_symm_eq {R A B : Type _} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) {a : B} {b : A} : a = f b ↔ f.symm a = b :=
  haveI : ∀ e : A ≃ B, a = e b ↔ e.symm a = b :=
    by
    intro e
    rw [← Equiv.apply_eq_iff_eq e, Equiv.apply_symm_apply]
  -- simp only [iff_self],
    this
    f.to_equiv

theorem StarAlgEquiv.eq_apply_iff_symm_eq {R A B : Type _} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [Star A] [Star B] (f : A ≃⋆ₐ[R] B) {a : B} {b : A} :
    a = f b ↔ f.symm a = b :=
  AlgEquiv.eq_apply_iff_symm_eq f.toAlgEquiv

