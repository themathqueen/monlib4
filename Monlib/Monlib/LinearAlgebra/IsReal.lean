/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Algebra.Star.StarAlgHom
import Algebra.Star.BigOperators
import LinearAlgebra.InnerAut
import Algebra.Algebra.Basic

#align_import linear_algebra.is_real

/-!
 # Real linear maps (a.k.a. star-preserving linear maps)

 This file defines the function `linear_map.real` which maps a linear map `φ.real (x) = star (φ (star x))`; so that `φ` is real (star-preserving) if and only if `φ = φ.real`.
-/


def LinearMap.IsReal {E F K : Type _} [Semiring K] [AddCommMonoid E] [AddCommMonoid F] [Module K E]
    [Module K F] [Star E] [Star F] (φ : E →ₗ[K] F) : Prop :=
  ∀ x, φ (star x) = star (φ x)

section Sec

variable {E F K : Type _} [AddCommMonoid E] [StarAddMonoid E] [AddCommMonoid F] [StarAddMonoid F]
  [Semiring K] [Module K E] [Module K F] [InvolutiveStar K] [StarModule K E] [StarModule K F]

def LinearMap.real (φ : E →ₗ[K] F) : E →ₗ[K] F
    where
  toFun x := star (φ (star x))
  map_add' x y := by simp only [star_add, map_add]
  map_smul' r x := by simp only [star_smul, SMulHomClass.map_smul, star_star, RingHom.id_apply]

theorem LinearMap.real_eq (φ : E →ₗ[K] F) (x : E) : φ.Real x = star (φ (star x)) :=
  rfl

theorem LinearMap.isReal_iff (φ : E →ₗ[K] F) : φ.IsReal ↔ φ.Real = φ := by
  simp_rw [LinearMap.IsReal, LinearMap.ext_iff, LinearMap.real, LinearMap.coe_mk,
    eq_star_iff_eq_star, eq_comm]

theorem LinearMap.real_add (f g : E →ₗ[K] F) : (f + g).Real = f.Real + g.Real :=
  by
  ext1
  simp only [LinearMap.real, LinearMap.add_apply, LinearMap.coe_mk, star_add]

open scoped BigOperators

theorem LinearMap.real_sum {n : Type _} {s : Finset n} (f : n → E →ₗ[K] F) :
    (∑ i : n in s, f i).Real = ∑ i : n in s, (f i).Real :=
  by
  ext1
  simp only [LinearMap.real, LinearMap.sum_apply, LinearMap.coe_mk, star_sum]

theorem LinearMap.real_real (f : E →ₗ[K] F) : f.Real.Real = f :=
  by
  ext1
  simp only [LinearMap.real, LinearMap.coe_mk, star_star]

theorem LinearMap.real_comp {G : Type _} [AddCommMonoid G] [StarAddMonoid G] [Module K G]
    [StarModule K G] (f : E →ₗ[K] F) (g : G →ₗ[K] E) : (f ∘ₗ g).Real = f.Real ∘ₗ g.Real :=
  by
  ext1
  simp only [LinearMap.real, LinearMap.comp_apply, LinearMap.coe_mk, star_star]

theorem LinearMap.real_starAlgEquiv_conj {E K : Type _} [CommSemiring K] [Semiring E] [Algebra K E]
    [InvolutiveStar K] [StarAddMonoid E] [StarModule K E] (f : E →ₗ[K] E) (φ : E ≃⋆ₐ[K] E) :
    (φ.toAlgEquiv.toLinearEquiv.toLinearMap ∘ₗ
          f ∘ₗ φ.symm.toAlgEquiv.toLinearEquiv.toLinearMap).Real =
      φ.toAlgEquiv.toLinearEquiv.toLinearMap ∘ₗ
        f.Real ∘ₗ φ.symm.toAlgEquiv.toLinearEquiv.toLinearMap :=
  by
  ext1
  simp only [LinearMap.real, LinearMap.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    AlgEquiv.toLinearEquiv_apply, StarAlgEquiv.coe_toAlgEquiv, map_star]

theorem LinearMap.real_starAlgEquiv_conj_iff {E K : Type _} [CommSemiring K] [Semiring E]
    [Algebra K E] [InvolutiveStar K] [StarAddMonoid E] [StarModule K E] (f : E →ₗ[K] E)
    (φ : E ≃⋆ₐ[K] E) :
    (φ.toAlgEquiv.toLinearEquiv.toLinearMap ∘ₗ
          f ∘ₗ φ.symm.toAlgEquiv.toLinearEquiv.toLinearMap).IsReal ↔
      f.IsReal :=
  by
  simp_rw [LinearMap.isReal_iff, LinearMap.real_starAlgEquiv_conj, LinearMap.ext_iff,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, AlgEquiv.toLinearEquiv_apply,
    StarAlgEquiv.coe_toAlgEquiv, ← StarAlgEquiv.symm_apply_eq, StarAlgEquiv.symm_apply_apply]
  refine' ⟨fun h x => _, fun h x => h _⟩
  specialize h (φ x)
  simp_rw [StarAlgEquiv.symm_apply_apply] at h
  exact h

def LinearMap.realRingEquiv {R E : Type _} [Semiring R] [AddCommMonoid E] [StarAddMonoid E]
    [Module R E] [InvolutiveStar R] [StarModule R E] : (E →ₗ[R] E) ≃+* (E →ₗ[R] E)
    where
  toFun f := f.Real
  invFun f := f.Real
  map_add' f g := LinearMap.real_add _ _
  map_mul' f g := LinearMap.real_comp _ _
  left_inv f := LinearMap.real_real _
  right_inv f := LinearMap.real_real _

theorem LinearMap.mulRight_real {E K : Type _} [CommSemiring K] [NonUnitalSemiring E]
    [InvolutiveStar K] [StarRing E] [Module K E] [StarModule K E] [SMulCommClass K E E]
    [IsScalarTower K E E] (x : E) : (LinearMap.mulRight K x).Real = LinearMap.mulLeft K (star x) :=
  by
  ext1 u
  simp_rw [LinearMap.real_eq, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, star_mul,
    star_star]

theorem LinearMap.mulLeft_real {E K : Type _} [CommSemiring K] [NonUnitalSemiring E]
    [InvolutiveStar K] [StarRing E] [Module K E] [StarModule K E] [SMulCommClass K E E]
    [IsScalarTower K E E] (x : E) : (LinearMap.mulLeft K x).Real = LinearMap.mulRight K (star x) :=
  by
  ext1 u
  simp_rw [LinearMap.real_eq, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, star_mul,
    star_star]

end Sec

variable {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [StarAddMonoid E]
  [StarModule 𝕜 E] [FiniteDimensional 𝕜 E]

theorem LinearMap.real.spectrum (φ : E →ₗ[𝕜] E) : spectrum 𝕜 φ.Real = star (spectrum 𝕜 φ) :=
  by
  ext
  simp_rw [Set.mem_star, ← Module.End.hasEigenvalue_iff_mem_spectrum, ←
    Module.End.has_eigenvector_iff_hasEigenvalue, LinearMap.real_eq, star_eq_iff_star_eq, star_smul]
  constructor <;> rintro ⟨v, ⟨h, hv⟩⟩
  · exact ⟨star v, h.symm, star_ne_zero.mpr hv⟩
  · refine' ⟨star v, _, star_ne_zero.mpr hv⟩
    rw [star_star]
    exact h.symm

theorem LinearMap.real.eigenspace {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [StarAddMonoid E] [StarModule 𝕜 E] (φ : E →ₗ[𝕜] E) (α : 𝕜) (x : E) :
    x ∈ Module.End.eigenspace φ.Real α ↔ star x ∈ Module.End.eigenspace φ (star α) := by
  simp_rw [Module.End.mem_eigenspace_iff, LinearMap.real_eq, star_eq_iff_star_eq, star_smul,
    eq_comm]

theorem LinearMap.real_neg {E : Type _} {F : Type _} {K : Type _} [AddCommMonoid E]
    [StarAddMonoid E] [AddCommGroup F] [StarAddMonoid F] [Semiring K] [Module K E] [Module K F]
    [InvolutiveStar K] [StarModule K E] [StarModule K F] (f : E →ₗ[K] F) : (-f).Real = -f.Real :=
  by
  ext
  simp only [LinearMap.neg_apply, LinearMap.real_eq, star_neg]

theorem LinearMap.real_sub {E : Type _} {F : Type _} {K : Type _} [AddCommMonoid E]
    [StarAddMonoid E] [AddCommGroup F] [StarAddMonoid F] [Semiring K] [Module K E] [Module K F]
    [InvolutiveStar K] [StarModule K E] [StarModule K F] (f g : E →ₗ[K] F) :
    (f - g).Real = f.Real - g.Real :=
  by
  simp_rw [sub_eq_add_neg, ← LinearMap.real_neg]
  exact LinearMap.real_add _ _

theorem LinearMap.real_smul {E F K : Type _} [CommSemiring K] [AddCommMonoid E] [AddCommMonoid F]
    [StarRing K] [StarAddMonoid E] [StarAddMonoid F] [Module K E] [Module K F] [StarModule K E]
    [StarModule K F] (f : E →ₗ[K] F) (α : K) : (α • f).Real = starRingEnd K α • f.Real :=
  by
  ext
  simp_rw [LinearMap.real_eq, LinearMap.smul_apply, star_smul, starRingEnd_apply]
  rfl

theorem LinearMap.real_inj_eq {E F K : Type _} [Semiring K] [AddCommMonoid E] [AddCommMonoid F]
    [InvolutiveStar K] [StarAddMonoid E] [StarAddMonoid F] [Module K E] [Module K F]
    [StarModule K E] [StarModule K F] (f g : E →ₗ[K] F) : f = g ↔ f.Real = g.Real :=
  by
  refine' ⟨fun h => by rw [h], fun h => _⟩
  rw [← LinearMap.real_real f, h, LinearMap.real_real]

theorem LinearMap.isRealOne {E K : Type _} [Semiring K] [AddCommMonoid E] [Module K E] [Star E] :
    (1 : E →ₗ[K] E).IsReal := fun _ => rfl

theorem LinearMap.real_one {E K : Type _} [Semiring K] [InvolutiveStar K] [AddCommMonoid E]
    [StarAddMonoid E] [Module K E] [StarModule K E] : (1 : E →ₗ[K] E).Real = 1 :=
  (LinearMap.isReal_iff _).mp LinearMap.isRealOne

