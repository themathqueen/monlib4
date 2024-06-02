/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.MyIps.Symm

#align_import linear_algebra.my_ips.basic

/-!

# Some obvious basic properties on inner product space

This files provides some useful and obvious results for linear maps and continuous linear maps.

-/


theorem inner_self_re {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : E) : (RCLike.re (inner x x : 𝕜) : 𝕜) = inner x x := by simp only [inner_self_ofReal_re]

theorem forall_inner_eq_zero_iff {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x : E) : (∀ y, (inner x y : 𝕜) = 0) ↔ x = 0 :=
  by
  refine' ⟨fun h => _, fun h y => by rw [h, inner_zero_left]⟩
  specialize h x
  rw [inner_self_eq_zero] at h
  exact h

open RCLike ContinuousLinearMap

variable {E : Type _} [NormedAddCommGroup E]

/-- linear maps $p,q$ are equal if and only if
  $\langle p x, x \rangle = \langle q x, x \rangle$ for any $x$. -/
theorem LinearMap.ext_iff_inner_map [InnerProductSpace ℂ E] (p q : E →ₗ[ℂ] E) :
    p = q ↔ ∀ x : E, ⟪p x, x⟫_ℂ = ⟪q x, x⟫_ℂ :=
  by
  constructor
  · intro h
    simp_rw [h, forall_const]
  · intro h
    rw [← sub_eq_zero, ← inner_map_self_eq_zero]
    simp_rw [LinearMap.sub_apply, inner_sub_left, h, sub_self, forall_const]

/-- copy of `linear_map.ext_iff_inner_map` but for continuous linear maps -/
theorem ContinuousLinearMap.ext_iff_inner_map [InnerProductSpace ℂ E] (p q : E →L[ℂ] E) :
    p = q ↔ ∀ x : E, ⟪p x, x⟫_ℂ = ⟪q x, x⟫_ℂ := by
  simp_rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ext_iff_inner_map, coe_inj]

/-- Self-adjoint linear operators $p,q$ are equal if and only if
  $\langle p x, x \rangle_\mathbb{k} = \langle q x, x \rangle_\mathbb{k}$. -/
theorem ContinuousLinearMap.IsSelfAdjoint.ext_iff_inner_map {E 𝕜 : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E}
    (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    p = q ↔ ∀ x : E, @inner 𝕜 _ _ (p x) x = @inner 𝕜 _ _ (q x) x :=
  by
  rw [← sub_eq_zero, ← IsSelfAdjoint.inner_map_self_eq_zero (hp.sub hq)]
  simp_rw [sub_apply, inner_sub_left, sub_eq_zero]

section RCLike

variable {𝕜 : Type _} [RCLike 𝕜]

/-- in a complex inner product space, we have
  that an operator $a$ is self-adjoint if and only if
  $\langle a x, x \rangle_\mathbb{C}$ is real for all $x \in E$ -/
theorem isSelfAdjoint_iff_complex_inner_re_eq [InnerProductSpace ℂ E] [CompleteSpace E]
    {a : E →L[ℂ] E} : IsSelfAdjoint a ↔ ∀ x : E, (re ⟪a x, x⟫_ℂ : ℂ) = ⟪a x, x⟫_ℂ := by
  simp_rw [re_to_complex, ← Complex.conj_eq_iff_re, inner_conj_symm, isSelfAdjoint_iff',
    ContinuousLinearMap.ext_iff_inner_map (adjoint a) a, adjoint_inner_left]

local notation "⟪" x "," y "⟫" => @inner 𝕜 _ _ x y

/-- the adjoint of a self-adjoint operator is self-adjoint -/
theorem IsSelfAdjoint.adjoint [InnerProductSpace 𝕜 E] [CompleteSpace E] {a : E →L[𝕜] E}
    (ha : IsSelfAdjoint a) : IsSelfAdjoint (adjoint a) :=
  congr_arg star ha

/-- for a self-adjoint operator $a$, we have $\langle a x, x \rangle_\mathbb{k}$ is real -/
theorem IsSelfAdjoint.inner_re_eq {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {a : E →L[𝕜] E} (ha : IsSelfAdjoint a) (x : E) : (re ⟪a x,x⟫ : 𝕜) = ⟪a x,x⟫ :=
  by
  rcases@I_mul_I_ax 𝕜 _ with (h | _)
  · rw [← re_add_im ⟪a x,x⟫]
    simp_rw [h, MulZeroClass.mul_zero, add_zero]
    norm_cast
  · simp_rw [← conj_eq_iff_re, inner_conj_symm]
    have ha' := ha
    simp_rw [isSelfAdjoint_iff',
      ContinuousLinearMap.IsSelfAdjoint.ext_iff_inner_map ha.adjoint ha, adjoint_inner_left] at ha'
    exact ha' x

end RCLike

/-- copy of `inner_map_self_eq_zero` for bounded linear maps -/
theorem ContinuousLinearMap.inner_map_self_eq_zero [InnerProductSpace ℂ E] {p : E →L[ℂ] E} :
    (∀ x : E, ⟪p x, x⟫_ℂ = 0) ↔ p = 0 :=
  by
  simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe,
    ← LinearMap.ext_iff, coe_zero]
  exact @_root_.inner_map_self_eq_zero E _ _ _

theorem ContinuousLinearMap.adjoint_smul {K E : Type _} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [CompleteSpace E] (φ : E →L[K] E) (a : K) :
    adjoint (a • φ) = starRingEnd K a • adjoint φ := by
  simp_rw [← ContinuousLinearMap.star_eq_adjoint, star_smul, starRingEnd_apply]

theorem LinearMap.adjoint_smul {K E : Type _} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [FiniteDimensional K E] (φ : E →ₗ[K] E) (a : K) :
    adjoint (a • φ) = starRingEnd K a • adjoint φ :=
  by
  have :=
    @ContinuousLinearMap.adjoint_smul K E _ _ _ (FiniteDimensional.complete K E)
      (toContinuousLinearMap φ) a
  simp_rw [← LinearMap.adjoint_toContinuousLinearMap] at this
  rw [LinearMap.adjoint_eq_toCLM_adjoint, _root_.map_smul, this]
  rfl

theorem LinearMap.adjoint_one {K E : Type _} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [FiniteDimensional K E] : adjoint (1 : E →ₗ[K] E) = 1 :=
  star_one _
