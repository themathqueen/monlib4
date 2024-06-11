/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Projection

#align_import linear_algebra.is_proj'

/-!
 # is_proj'

This file contains the definition of `linear_map.is_proj'` and lemmas relating to it, which is essentially `linear_map.is_proj` but as a linear map from `E` to `↥U`.

-/


section

variable {R E : Type _} [Ring R] [AddCommGroup E] [Module R E] {U : Submodule R E}

/-- `linear_map.is_proj` but as a linear map from `E` to `↥U` -/
def isProj' {p : E →ₗ[R] E} (hp : LinearMap.IsProj U p) : E →ₗ[R] ↥U
    where
  toFun x := ⟨p x, hp.1 x⟩
  map_add' x y := by simp_rw [map_add, AddMemClass.mk_add_mk]
  map_smul' r x := by simp_rw [LinearMap.map_smul, RingHom.id_apply, SetLike.mk_smul_mk]

theorem isProj'_apply {p : E →ₗ[R] E} (hp : LinearMap.IsProj U p) (x : E) : ↑(isProj' hp x) = p x :=
  rfl

theorem isProj'_eq {p : E →ₗ[R] E} (hp : LinearMap.IsProj U p) : ∀ x : ↥U, isProj' hp (x : E) = x :=
  by
  intro x
  ext
  simp_rw [isProj'_apply, LinearMap.IsProj.map_id hp _ (SetLike.coe_mem x)]

end

variable {E 𝕜 : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem orthogonalProjection_eq_linear_proj' {K : Submodule 𝕜 E} [HasOrthogonalProjection K] :
    (orthogonalProjection K : E →ₗ[𝕜] K) =
      Submodule.linearProjOfIsCompl K _ Submodule.isCompl_orthogonal_of_completeSpace :=
  by
  have : IsCompl K Kᗮ := Submodule.isCompl_orthogonal_of_completeSpace
  ext x : 1
  nth_rw 1 [← Submodule.linear_proj_add_linearProjOfIsCompl_eq_self this x]
  rw [ContinuousLinearMap.coe_coe, map_add, orthogonalProjection_mem_subspace_eq_self,
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (Submodule.coe_mem _), add_zero]

theorem orthogonalProjection_eq_linear_proj'' {K : Submodule 𝕜 E} [HasOrthogonalProjection K] (x : E) :
    orthogonalProjection K x =
      Submodule.linearProjOfIsCompl K _ Submodule.isCompl_orthogonal_of_completeSpace x :=
  by rw [← orthogonalProjection_eq_linear_proj]

noncomputable def orthogonalProjection' (U : Submodule 𝕜 E) [HasOrthogonalProjection U] : E →L[𝕜] E :=
  U.subtypeL.comp (orthogonalProjection U)

theorem orthogonalProjection'_apply (U : Submodule 𝕜 E) [HasOrthogonalProjection U] (x : E) :
    orthogonalProjection' U x = orthogonalProjection U x :=
  rfl

local notation "P" => orthogonalProjection

local notation "↥P" => orthogonalProjection'

@[simp]
theorem ContinuousLinearMap.range_toLinearMap {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] {p : E →L[𝕜] F} : LinearMap.range (p.toLinearMap) = LinearMap.range p :=
  rfl

open ContinuousLinearMap

@[simp]
theorem orthogonalProjection.range (U : Submodule 𝕜 E) [HasOrthogonalProjection U] :
    LinearMap.range (↥P U) = U := by
  simp_rw [orthogonalProjection', ← range_toLinearMap, coe_comp,
    orthogonalProjection_eq_linear_proj', Submodule.coe_subtypeL, LinearMap.range_comp,
    Submodule.linearProjOfIsCompl_range, Submodule.map_subtype_top]

@[simp]
theorem orthogonalProjection'_eq (U : Submodule 𝕜 E) [HasOrthogonalProjection U] :
    ↥P U = U.subtypeL.comp (P U) :=
  rfl

theorem orthogonal_projection'_eq_linear_proj {K : Submodule 𝕜 E} [HasOrthogonalProjection K] :
    (K.subtypeL.comp (orthogonalProjection K) : E →ₗ[𝕜] E) =
     (K.subtype).comp
        (Submodule.linearProjOfIsCompl K _ Submodule.isCompl_orthogonal_of_completeSpace) :=
  by
  ext x
  simp_rw [ContinuousLinearMap.coe_coe, LinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.subtype_apply, orthogonalProjection_eq_linear_proj'']

theorem orthogonalProjection'_eq_linear_proj' {K : Submodule 𝕜 E} [HasOrthogonalProjection K] (x : E) :
    (orthogonalProjection' K : E →ₗ[𝕜] E) x =
      (K.subtype).comp
        (Submodule.linearProjOfIsCompl K _ Submodule.isCompl_orthogonal_of_completeSpace) x :=
  by rw [← orthogonal_projection'_eq_linear_proj, orthogonalProjection']
