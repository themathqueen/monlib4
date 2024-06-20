/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.BigOperators
-- import Monlib.LinearAlgebra.InnerAut
import Mathlib.Algebra.Algebra.Spectrum
import Monlib.LinearAlgebra.End
import Monlib.Preq.StarAlgEquiv
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Basic

#align_import linear_algebra.is_real

/-!
 # real linear maps (a.k.a. star-preserving linear maps)

 This file defines the function `linear_map.real` which maps a linear map `φ.real (x) = star (φ (star x))`; so that `φ` is real (star-preserving) if and only if `φ = φ.real`.
-/


def LinearMap.IsReal {M₁ M₂ : Type*} {F : Type*} [FunLike F M₁ M₂]
  [Star M₁] [Star M₂] (φ : F) : Prop :=
∀ x, φ (star x) = star (φ x)

section Sec

variable {E F K : Type _} [AddCommMonoid E] [StarAddMonoid E] [AddCommMonoid F] [StarAddMonoid F]

@[simps!]
def LinearMap.real
  [Semiring K] [Module K E] [Module K F]
  [InvolutiveStar K] [StarModule K E] [StarModule K F] (φ : E →ₗ[K] F) :
  E →ₗ[K] F :=
{ toFun := λ x => (star (φ (star x)))
  map_add' := λ _ _ => by simp only [star_add, map_add]
  map_smul' := λ _ _ => by simp only [star_smul, _root_.map_smul, star_star, RingHom.id_apply] }

@[simps! apply_apply]
def LinearMap.realSLinearEquiv
  [CommSemiring K] [Module K E] [Module K F]
  [StarRing K] [StarModule K E] [StarModule K F] :
  (E →ₗ[K] F) ≃ₛₗ[starRingEnd K] (E →ₗ[K] F) :=
{ toFun := λ φ => φ.real
  invFun := λ φ => φ.real
  left_inv := λ _ =>
    by ext; simp only [coe_mk, star_star, real_apply, AddHom.coe_mk]
  right_inv := λ _ =>
    by ext; simp only [star_star, real_apply, coe_mk, AddHom.coe_mk]
  map_add' := λ _ _ =>
    by ext; simp only [LinearMap.add_apply, star_add, real_apply]
  map_smul' := λ _ _ =>
    by ext; simp only [LinearMap.smul_apply, star_smul, real_apply]; rfl }

variable [Semiring K] [Module K E] [Module K F]
  [InvolutiveStar K] [StarModule K E] [StarModule K F]

@[simp]
theorem LinearMap.real_add (f g : E →ₗ[K] F) : (f + g).real = f.real + g.real :=
  by
  ext
  simp only [LinearMap.real_apply, LinearMap.add_apply, star_add]
open scoped BigOperators

@[simp]
theorem LinearMap.real_sum {n : Type _} {s : Finset n} (f : n → E →ₗ[K] F) :
    (∑ i : n in s, f i).real = ∑ i : n in s, (f i).real :=
  by
  ext
  simp only [LinearMap.real_apply, LinearMap.sum_apply, star_sum]

@[simp]
theorem LinearMap.real_real (f : E →ₗ[K] F) : f.real.real = f :=
  by
  ext
  simp only [LinearMap.real_apply, star_star]

theorem LinearMap.isReal_iff
  (φ : E →ₗ[K] F) : IsReal φ ↔ real φ = φ := by
  simp_rw [LinearMap.IsReal, LinearMap.ext_iff, LinearMap.real_apply,
    @eq_star_iff_eq_star _ _ (φ (star _)), eq_comm]

open scoped BigOperators

@[simp]
theorem LinearMap.real_comp
  {G : Type _} [AddCommMonoid G] [StarAddMonoid G] [Module K G]
  [StarModule K G] (f : E →ₗ[K] F) (g : G →ₗ[K] E) : (f ∘ₗ g).real = f.real ∘ₗ g.real :=
by
  ext
  simp only [LinearMap.real_apply, LinearMap.comp_apply, star_star]

theorem LinearMap.real_starAlgEquiv_conj {E K : Type _} [CommSemiring K] [Semiring E] [Algebra K E]
    [InvolutiveStar K] [StarAddMonoid E] [StarModule K E] (f : E →ₗ[K] E) (φ : E ≃⋆ₐ[K] E) :
    (φ.toLinearMap ∘ₗ
          f ∘ₗ φ.symm.toLinearMap).real =
      φ.toLinearMap ∘ₗ
        f.real ∘ₗ φ.symm.toLinearMap :=
by
  ext
  simp only [LinearMap.real_apply, LinearMap.comp_apply,
    StarAlgEquiv.toLinearMap_apply, map_star]

theorem LinearMap.real_starAlgEquiv_conj_iff {E K : Type _} [CommSemiring K] [Semiring E]
    [Algebra K E] [InvolutiveStar K] [StarAddMonoid E] [StarModule K E] (f : E →ₗ[K] E)
    (φ : E ≃⋆ₐ[K] E) :
    LinearMap.IsReal (φ.toLinearMap ∘ₗ
      f ∘ₗ φ.symm.toLinearMap) ↔
    LinearMap.IsReal f :=
by
  simp_rw [LinearMap.isReal_iff, LinearMap.real_starAlgEquiv_conj, LinearMap.ext_iff,
    LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,
    ← StarAlgEquiv.symm_apply_eq, StarAlgEquiv.symm_apply_apply]
  refine' ⟨fun h x => _, fun h x => h _⟩
  specialize h (φ x)
  simp_rw [StarAlgEquiv.symm_apply_apply] at h
  exact h

def LinearMap.realRingEquiv {R E : Type _} [Semiring R] [AddCommMonoid E] [StarAddMonoid E]
    [Module R E] [InvolutiveStar R] [StarModule R E] :
      (E →ₗ[R] E) ≃+* (E →ₗ[R] E)
    where
  toFun f := f.real
  invFun f := f.real
  map_add' _ _ := real_add _ _
  map_mul' _ _ := LinearMap.real_comp _ _
  left_inv _ := real_real _
  right_inv _ := real_real _

theorem LinearMap.mulRight_real {E K : Type _} [CommSemiring K] [NonUnitalSemiring E]
    [InvolutiveStar K] [StarRing E] [Module K E] [StarModule K E] [SMulCommClass K E E]
    [IsScalarTower K E E] (x : E) :
      (mulRight K x).real = mulLeft K (star x) :=
  by
  ext u
  simp_rw [LinearMap.real_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, star_mul,
    star_star]

theorem LinearMap.mulLeft_real {E K : Type _} [CommSemiring K] [NonUnitalSemiring E]
    [InvolutiveStar K] [StarRing E] [Module K E] [StarModule K E] [SMulCommClass K E E]
    [IsScalarTower K E E] (x : E) :
      (mulLeft K x).real = mulRight K (star x) :=
  by
  ext u
  simp_rw [LinearMap.real_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, star_mul,
    star_star]

end Sec

variable {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [StarAddMonoid E]
  [StarModule 𝕜 E]

theorem LinearMap.real.spectrum [FiniteDimensional 𝕜 E]
  (φ : E →ₗ[𝕜] E) : spectrum 𝕜 φ.real = star (spectrum 𝕜 φ) :=
by
  ext
  simp_rw [Set.mem_star,
    ← Module.End.hasEigenvalue_iff_mem_spectrum, ←
    Module.End.has_eigenvector_iff_hasEigenvalue, LinearMap.real_apply, star_eq_iff_star_eq, star_smul]
  constructor <;> rintro ⟨v, ⟨h, hv⟩⟩
  · exact ⟨star v, h.symm, star_ne_zero.mpr hv⟩
  · refine' ⟨star v, _, star_ne_zero.mpr hv⟩
    rw [star_star]
    exact h.symm

theorem LinearMap.real.eigenspace {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [StarAddMonoid E] [StarModule 𝕜 E] (φ : E →ₗ[𝕜] E) (α : 𝕜) (x : E) :
    x ∈ Module.End.eigenspace φ.real α ↔ star x ∈ Module.End.eigenspace φ (star α) := by
  simp_rw [Module.End.mem_eigenspace_iff, LinearMap.real_apply, star_eq_iff_star_eq, star_smul,
    eq_comm]

theorem LinearMap.real_neg {E : Type _} {F : Type _} {K : Type _} [AddCommMonoid E]
    [StarAddMonoid E] [AddCommGroup F] [StarAddMonoid F] [Semiring K] [Module K E] [Module K F]
    [InvolutiveStar K] [StarModule K E] [StarModule K F] (f : E →ₗ[K] F) : (-f).real = -f.real :=
  by
  ext
  simp only [LinearMap.neg_apply, LinearMap.real_apply, star_neg]

theorem LinearMap.real_sub {E : Type _} {F : Type _} {K : Type _} [AddCommMonoid E]
    [StarAddMonoid E] [AddCommGroup F] [StarAddMonoid F] [Semiring K] [Module K E] [Module K F]
    [InvolutiveStar K] [StarModule K E] [StarModule K F] (f g : E →ₗ[K] F) :
    (f - g).real = f.real - g.real :=
  by
  simp_rw [sub_eq_add_neg, ← LinearMap.real_neg]
  exact LinearMap.real_add _ _

theorem LinearMap.real_smul {E F K : Type _} [CommSemiring K] [AddCommMonoid E] [AddCommMonoid F]
    [StarRing K] [StarAddMonoid E] [StarAddMonoid F] [Module K E] [Module K F] [StarModule K E]
    [StarModule K F] (f : E →ₗ[K] F) (α : K) : (α • f).real = starRingEnd K α • f.real :=
  by
  ext
  simp_rw [LinearMap.real_apply, LinearMap.smul_apply, star_smul, starRingEnd_apply]
  rfl

theorem LinearMap.real_inj_eq {E F K : Type _} [Semiring K] [AddCommMonoid E] [AddCommMonoid F]
    [InvolutiveStar K] [StarAddMonoid E] [StarAddMonoid F] [Module K E] [Module K F]
    [StarModule K E] [StarModule K F] (f g : E →ₗ[K] F) : f = g ↔ f.real = g.real :=
  by
  refine' ⟨fun h => by rw [h], fun h => _⟩
  rw [← LinearMap.real_real f, h, LinearMap.real_real]

theorem LinearMap.isRealOne {E K : Type _} [Semiring K] [AddCommMonoid E] [Module K E] [Star E] :
    LinearMap.IsReal (1 : E →ₗ[K] E) := fun _ => rfl

theorem LinearMap.real_one {E K : Type _} [Semiring K] [InvolutiveStar K] [AddCommMonoid E]
    [StarAddMonoid E] [Module K E] [StarModule K E] : (1 : E →ₗ[K] E).real = 1 :=
  (LinearMap.isReal_iff _).mp LinearMap.isRealOne
