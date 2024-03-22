/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Data.Complex.Basic

#align_import linear_algebra.invariant_submodule

/-!
# Invariant submodules

In this file, we define and prove some basic results on invariant submodules.
-/


namespace Submodule

variable {E R : Type _} [Ring R] [AddCommGroup E] [Module R E]

/-- `U` is `T` invariant (ver 1): `U ≤ U.comap` -/
def InvariantUnder (U : Submodule R E) (T : E →ₗ[R] E) : Prop :=
  U ≤ U.comap T

/-- `U` is `T` invariant if and only if `U.map T ≤ U` -/
@[simp]
theorem invariantUnder_iff_map (U : Submodule R E) (T : E →ₗ[R] E) :
    U.InvariantUnder T ↔ U.map T ≤ U :=
  Submodule.map_le_iff_le_comap.symm

/-- `U` is `T` invariant if and only if `set.maps_to T U U` -/
theorem invariantUnder_iff_mapsTo (U : Submodule R E) (T : E →ₗ[R] E) :
    Set.MapsTo T U U ↔ U.InvariantUnder T :=
  Iff.rfl

/-- `U` is `T` invariant is equivalent to saying `T(U) ⊆ U` -/
theorem invariantUnder_iff (U : Submodule R E) (T : E →ₗ[R] E) : U.InvariantUnder T ↔ T '' U ⊆ U :=
  by rw [← Set.mapsTo', U.invariantUnder_iff_mapsTo]

variable (U V : Submodule R E) (hUV : IsCompl U V) (T : E →ₗ[R] E)

local notation "pᵤ" => Submodule.linearProjOfIsCompl U V hUV

local notation "pᵥ" => Submodule.linearProjOfIsCompl V U hUV.symm

/-- projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p` -/
theorem linearProjOfIsCompl_eq_self_iff {p q : Submodule R E} (hpq : IsCompl p q) (x : E) :
    (p.linearProjOfIsCompl q hpq x : E) = x ↔ x ∈ p :=
  by
  constructor <;> intro H
  · rw [← H]; exact Submodule.coe_mem _
  · exact congr_arg _ (Submodule.linearProjOfIsCompl_apply_left hpq ⟨x, H⟩)

theorem InvariantUnder.linear_proj_comp_self_eq (h : U.InvariantUnder T) (x : U) :
    (pᵤ (T x) : E) = T x :=
  (linearProjOfIsCompl_eq_self_iff _ _).mpr <| h (coe_mem _)

theorem invariantUnderOfLinearProjCompSelfEq (h : ∀ x : U, (pᵤ (T x) : E) = T x) :
    U.InvariantUnder T := fun u hu => by
  rw [mem_comap, ← linearProjOfIsCompl_eq_self_iff hUV _, ←
    (linearProjOfIsCompl_eq_self_iff hUV u).mpr hu, h]

/-- `U` is invariant under `T` if and only if `pᵤ ∘ₗ T = T`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
theorem invariantUnder_iff_linear_proj_comp_self_eq :
    U.InvariantUnder T ↔ ∀ x : U, (pᵤ (T x) : E) = T x :=
  ⟨InvariantUnder.linear_proj_comp_self_eq U V hUV T,
    invariantUnderOfLinearProjCompSelfEq U V hUV T⟩

theorem linearProjOfIsCompl_eq_self_sub_linear_proj {p q : Submodule R E} (hpq : IsCompl p q)
    (x : E) : (q.linearProjOfIsCompl p hpq.symm x : E) = x - (p.linearProjOfIsCompl q hpq x : E) :=
  by rw [eq_sub_iff_add_eq, add_comm, Submodule.linear_proj_add_linearProjOfIsCompl_eq_self]

/-- `V` is invariant under `T` if and only if `pᵤ ∘ₗ (T ∘ₗ pᵤ) = pᵤ ∘ₗ T`,
 where `pᵤ` denotes the linear projection to `U` along `V` -/
theorem invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq :
    V.InvariantUnder T ↔ ∀ x : E, (pᵤ (T (pᵤ x)) : E) = pᵤ (T x) := by
  simp_rw [invariantUnder_iff_linear_proj_comp_self_eq _ _ hUV.symm,
    (LinearMap.range_eq_top.1 (linearProjOfIsCompl_range hUV.symm)).forall,
    linearProjOfIsCompl_eq_self_sub_linear_proj hUV, map_sub, sub_eq_self, Submodule.coe_sub,
    sub_eq_zero, eq_comm]

/-- both `U` and `V` are invariant under `T` if and only if `T` commutes with `pᵤ`,
 where `pᵤ` denotes the linear projection to `U` along `V` -/
theorem isCompl_invariantUnder_iff_linear_proj_and_self_commute :
    U.InvariantUnder T ∧ V.InvariantUnder T ↔ Commute (U.subtype ∘ₗ pᵤ) T :=
  by
  simp_rw [Commute, SemiconjBy, LinearMap.ext_iff, LinearMap.mul_apply, LinearMap.comp_apply,
    U.subtype_apply]
  constructor
  · rintro ⟨h1, h2⟩ x
    rw [← (U.invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq V _ _).mp h2 x]
    exact (linearProjOfIsCompl_eq_self_iff hUV _).mpr (h1 (coe_mem (pᵤ x)))
  · intro h
    simp_rw [U.invariantUnder_iff_linear_proj_comp_self_eq _ hUV,
      (LinearMap.range_eq_top.1 (linearProjOfIsCompl_range hUV)).forall,
      U.invariant_under'_iff_linear_proj_comp_self_comp_linear_proj_eq _ hUV, h,
      linearProjOfIsCompl_idempotent hUV, ← forall_and, and_self_iff,
      forall_const]

/-- `U` is invariant under `T.symm` if and only if `U ⊆ T(U)` -/
theorem invariantUnder_symm_iff_le_map (T : E ≃ₗ[R] E) : U.InvariantUnder T.symm ↔ U ≤ U.map T :=
  (U.invariantUnder_iff_map T.symm).trans (T.toEquiv.symm.subset_symm_image _ _).symm

theorem commutes_with_linear_proj_iff_linear_proj_eq [Invertible T] :
    Commute (U.subtype.comp pᵤ) T ↔ (⅟ T).comp ((U.subtype.comp pᵤ).comp T) = U.subtype.comp pᵤ :=
  by
  rw [Commute, SemiconjBy]
  simp_rw [LinearMap.mul_eq_comp]
  constructor
  · intro h
    simp_rw [h, ← LinearMap.mul_eq_comp, ← mul_assoc, invOf_mul_self, one_mul]
  · intro h
    rw [← h]; simp_rw [← LinearMap.mul_eq_comp, ← mul_assoc, mul_invOf_self]
    rw [mul_assoc (⅟ T) _ _]
    simp_rw [LinearMap.mul_eq_comp, h]; rfl

theorem invariantUnder_inv_iff_U_subset_image [Invertible T] :
    U.InvariantUnder (⅟ T) ↔ ↑U ⊆ T '' U := by
  constructor
  · intro h x hx
    simp only [Set.mem_image, SetLike.mem_coe]
    use(⅟ T) x
    rw [← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, mul_invOf_self, LinearMap.one_apply,
      eq_self_iff_true, and_true_iff]
    exact h hx
  · intro h x hx
    rw [Submodule.mem_comap]
    simp only [Set.subset_def, Set.mem_image] at h
    cases' h x hx with y hy
    rw [← hy.2, ← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, invOf_mul_self]
    exact hy.1

theorem inv_linear_proj_comp_map_eq_linear_proj_iff_images_eq [Invertible T] :
    (⅟ T).comp ((U.subtype.comp pᵤ).comp T) = U.subtype.comp pᵤ ↔ T '' U = U ∧ T '' V = V :=
  by
  simp_rw [← Submodule.commutes_with_linear_proj_iff_linear_proj_eq, ←
    isCompl_invariantUnder_iff_linear_proj_and_self_commute, Set.Subset.antisymm_iff]
  have Hu : ∀ p q r s, ((p ∧ q) ∧ r ∧ s) = ((p ∧ r) ∧ q ∧ s) := fun _ _ _ _ =>
    by
    simp only [and_assoc, eq_iff_iff, and_congr_right_iff]
    simp only [← and_assoc, and_congr_left_iff]
    simp only [and_comm]; simp only [iff_self_iff, imp_true_iff]
  rw [Hu]
  clear Hu
  simp_rw [← Submodule.invariantUnder_iff _ _, iff_self_and, ←
    Submodule.invariantUnder_inv_iff_U_subset_image,
    isCompl_invariantUnder_iff_linear_proj_and_self_commute U V hUV]
  rw [Submodule.commutes_with_linear_proj_iff_linear_proj_eq, Commute, SemiconjBy]
  simp_rw [← LinearMap.mul_eq_comp]
  intro h
  rw [← h]
  simp_rw [mul_assoc _ _ (⅟ T), mul_invOf_self, h]
  rfl

end Submodule

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem StarAlgebra.centralizer_prod {M : Type _} [AddCommGroup M] [Module ℂ M]
    [StarRing (M →ₗ[ℂ] M)] [StarModule ℂ (M →ₗ[ℂ] M)] (A B : StarSubalgebra ℂ (M →ₗ[ℂ] M)) :
    (A.carrier ×ˢ B.carrier).centralizer = A.carrier.centralizer ×ˢ B.carrier.centralizer :=
  by
  ext
  simp_rw [Set.mem_prod, Set.mem_centralizer_iff, ← forall_and, Set.mem_prod, and_imp, Prod.forall,
    Prod.mul_def, Prod.eq_iff_fst_eq_snd_eq, StarSubalgebra.mem_carrier]
  exact
    ⟨fun h y => ⟨fun hy => (h y 0 hy B.zero_mem').1, fun hy => (h 0 y A.zero_mem' hy).2⟩,
      fun h y z hy hz => ⟨(h y).1 hy, (h z).2 hz⟩⟩
