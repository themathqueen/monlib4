/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.InvariantSubmodule
import Analysis.InnerProductSpace.Adjoint
import Analysis.InnerProductSpace.Spectrum
import LinearAlgebra.MyIps.Symm

#align_import linear_algebra.my_ips.ips

/-!
# Finite-dimensional inner product spaces

In this file, we prove some results in finite-dimensional inner product spaces.

## Notation

This file uses the local notation `P _` for `orthogonal_projection _`
and `↥P _` for the extended orthogonal projection `orthogonal_projection' _`.

We let $V$ be an inner product space over $\mathbb{k}$.
-/


variable {V 𝕜 : Type _} [IsROrC 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

local notation "P" => orthogonalProjection

-- local notation `↥P` := orthogonal_projection'
/-- $U$ is $T$-invariant if and only if $U^\bot$ is $T^*$ invariant -/
theorem Submodule.invariantUnder_iff_ortho_adjoint_invariant [FiniteDimensional 𝕜 V]
    (U : Submodule 𝕜 V) (T : V →ₗ[𝕜] V) :
    Submodule.InvariantUnder U T ↔ Submodule.InvariantUnder Uᗮ T.adjoint :=
  by
  suffices
    ∀ U : Submodule 𝕜 V,
      ∀ T : V →ₗ[𝕜] V, Submodule.InvariantUnder U T → Submodule.InvariantUnder Uᗮ T.adjoint
    by
    refine' ⟨this U T, _⟩
    intro h
    rw [← LinearMap.adjoint_adjoint T, ← Submodule.orthogonal_orthogonal U]
    apply this
    exact h
  clear U T
  simp only [Submodule.invariantUnder_iff, SetLike.mem_coe, Set.image_subset_iff, Set.subset_def,
    Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro U T h x hx y hy
  rw [LinearMap.adjoint_inner_right]
  apply (Submodule.mem_orthogonal U x).mp hx
  apply h y hy

theorem Submodule.invariantUnder_iff_ortho_adjoint_invariant' (U : Submodule 𝕜 V) [CompleteSpace V]
    [CompleteSpace U] (T : V →L[𝕜] V) : U.InvariantUnder T ↔ Uᗮ.InvariantUnder T.adjoint :=
  by
  suffices
    ∀ U : Submodule 𝕜 V,
      ∀ T : V →L[𝕜] V, CompleteSpace U → U.InvariantUnder T → Uᗮ.InvariantUnder T.adjoint
    by
    refine' ⟨this U T _inst_5, fun h => _⟩
    rw [← T.adjoint_adjoint, ← U.orthogonal_orthogonal]
    exact this _ _ (Submodule.orthogonal.completeSpace U) h
  clear _inst_5 U T
  simp_rw [Submodule.invariantUnder_iff, ContinuousLinearMap.coe_coe, SetLike.mem_coe,
    Set.image_subset_iff, Set.subset_def, Set.mem_preimage]
  intro U T _inst_4 h x hx y hy
  rw [ContinuousLinearMap.adjoint_inner_right]
  apply (U.mem_orthogonal x).mp hx
  apply h y hy

/-- $T$ is self adjoint implies
  $U$ is $T$-invariant if and only if $U^\bot$ is $T$-invariant -/
theorem IsSelfAdjoint.submodule_invariant_iff_ortho_submodule_invariant [FiniteDimensional 𝕜 V]
    (U : Submodule 𝕜 V) (T : V →ₗ[𝕜] V) (h : IsSelfAdjoint T) :
    Submodule.InvariantUnder U T ↔ Submodule.InvariantUnder Uᗮ T := by
  rw [Submodule.invariantUnder_iff_ortho_adjoint_invariant, linear_map.is_self_adjoint_iff'.mp h]

/-- $\textnormal{ker}(T) = \textnormal{range}(T^*)^\bot$ -/
theorem ker_is_ortho_adjoint_range {W : Type _} [FiniteDimensional 𝕜 V] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] (T : V →ₗ[𝕜] W) : T.ker = T.adjoint.rangeᗮ :=
  by
  ext
  simp only [LinearMap.mem_ker, Submodule.mem_orthogonal, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, LinearMap.adjoint_inner_left]
  exact
    ⟨fun h => by simp only [h, inner_zero_right, forall_const], fun h =>
      inner_self_eq_zero.mp (h (T x))⟩

/-- given any idempotent operator $T \in L(V)$, then `is_compl T.ker T.range`,
in other words, there exists unique $v \in \textnormal{ker}(T)$ and $w \in \textnormal{range}(T)$ such that $x = v + w$ -/
theorem LinearMap.IsProj.isCompl_range_ker {V R : Type _} [Ring R] [AddCommGroup V] [Module R V]
    (U : Submodule R V) (T : V →ₗ[R] V) (h : LinearMap.IsProj U T) : IsCompl T.ker T.range :=
  by
  have : IsIdempotentElem T
  rw [IsIdempotentElem]
  rw [LinearMap.mul_eq_comp]
  rw [← LinearMap.isProj_iff_idempotent]
  use U; exact h
  constructor
  · rw [disjoint_iff]
    ext
    simp only [Submodule.mem_bot, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range,
      ContinuousLinearMap.toLinearMap_eq_coe, ContinuousLinearMap.coe_coe]
    constructor
    · intro h'
      cases' h'.2 with y hy
      rw [← hy, ← IsIdempotentElem.eq this, LinearMap.mul_apply, hy]
      exact h'.1
    · intro h'
      rw [h', map_zero]
      simp only [eq_self_iff_true, true_and_iff]
      use x
      simp only [h', map_zero, eq_self_iff_true]
  · suffices ∀ x : V, ∃ v : T.ker, ∃ w : T.range, x = v + w
      by
      rw [codisjoint_iff, ← Submodule.add_eq_sup]
      ext
      rcases this x with ⟨v, w, hvw⟩
      simp only [Submodule.mem_top, iff_true_iff, hvw]
      apply Submodule.add_mem_sup (SetLike.coe_mem v) (SetLike.coe_mem w)
    intro x
    use x - T x
    rw [LinearMap.mem_ker, map_sub, ← LinearMap.mul_apply, IsIdempotentElem.eq this, sub_self]
    use T x; rw [LinearMap.mem_range] <;> simp only [exists_apply_eq_apply]
    simp only [Submodule.coe_mk, sub_add_cancel]

/--
idempotent $T$ is self-adjoint if and only if $\textnormal{ker}(T)^\bot=\textnormal{range}(T)$ -/
theorem LinearMap.is_idempotent_isSelfAdjoint_iff_ker_is_ortho_to_range [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (h : IsIdempotentElem T) :
    IsSelfAdjoint T ↔ T.kerᗮ = T.range :=
  by
  rw [LinearMap.isSelfAdjoint_iff']
  constructor
  · intro l; rw [ker_is_ortho_adjoint_range, Submodule.orthogonal_orthogonal]
    revert l; exact congr_arg LinearMap.range
  · intro h1; apply eq_of_sub_eq_zero
    simp only [← inner_map_self_eq_zero]
    intro x
    have := IsIdempotentElem.eq h
    rw [LinearMap.mul_eq_comp] at this
    obtain ⟨U, hT⟩ := (LinearMap.isProj_iff_idempotent T).mpr this
    obtain ⟨v, w, hvw, hunique⟩ :=
      Submodule.existsUnique_add_of_isCompl (LinearMap.IsProj.isCompl_range_ker U T hT) x
    simp only [LinearMap.sub_apply, inner_sub_left, LinearMap.adjoint_inner_left]
    cases' SetLike.coe_mem w with y hy
    rw [← hvw, map_add, linear_map.mem_ker.mp (SetLike.coe_mem v), ← hy, ← LinearMap.mul_apply,
      IsIdempotentElem.eq h, zero_add, hy, inner_add_left, inner_add_right, ← inner_conj_symm ↑w ↑v,
      (Submodule.mem_orthogonal T.ker ↑w).mp (by rw [h1]; exact SetLike.coe_mem w) v
        (SetLike.coe_mem v),
      map_zero, zero_add, sub_self]

section IsStarNormal

open LinearMap

/-- linear map `is_star_normal` if and only if it commutes with its adjoint -/
theorem LinearMap.isStarNormal_iff_adjoint [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ Commute T T.adjoint := by rw [Commute.symm_iff];
  exact ⟨fun hT => hT.star_comm_self, IsStarNormal.mk⟩

theorem ContinuousLinearMap.isStarNormal_iff_adjoint [CompleteSpace V] (T : V →L[𝕜] V) :
    IsStarNormal T ↔ Commute T T.adjoint := by rw [Commute.symm_iff];
  exact ⟨fun hT => hT.star_comm_self, IsStarNormal.mk⟩

theorem isSymmetric_hMul_adjoint_self [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V) :
    IsSymmetric (T * T.adjoint) := fun u v => by
  simp_rw [mul_apply, ← adjoint_inner_left T, ← adjoint_inner_right T]

theorem IsSymmetric.neg (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) : IsSymmetric (-T) :=
  by
  intro u v
  simp_rw [neg_apply, inner_neg_left, inner_neg_right, neg_inj]
  exact hT u v

theorem IsSymmetric.sub {T S : V →ₗ[𝕜] V} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T - S).IsSymmetric := by
  rw [sub_eq_add_neg]
  exact is_symmetric.add hT (IsSymmetric.neg S hS)

/-- $T$ is normal if and only if $\forall v, \|T v\| = \|T^* v\|$ -/
theorem LinearMap.IsStarNormal.norm_eq_adjoint [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ ∀ v : V, ‖T v‖ = ‖T.adjoint v‖ :=
  by
  rw [T.is_star_normal_iff_adjoint, Commute, SemiconjBy, ← sub_eq_zero]
  simp_rw [←
    is_symmetric.inner_map_self_eq_zero
      (IsSymmetric.sub (isSymmetric_hMul_adjoint_self T) (is_symmetric_adjoint_mul_self T)),
    sub_apply, inner_sub_left, mul_apply, adjoint_inner_left, inner_self_eq_norm_sq_to_K, ←
    adjoint_inner_right T, inner_self_eq_norm_sq_to_K, sub_eq_zero, ←
    sq_eq_sq (norm_nonneg _) (norm_nonneg _)]
  norm_cast
  simp_rw [eq_comm]

theorem ContinuousLinearMap.IsStarNormal.norm_eq_adjoint [CompleteSpace V] (T : V →L[𝕜] V) :
    IsStarNormal T ↔ ∀ v : V, ‖T v‖ = ‖T.adjoint v‖ :=
  by
  rw [T.is_star_normal_iff_adjoint, Commute, SemiconjBy, ← sub_eq_zero]
  simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_sub,
    ← LinearMap.ext_iff, ContinuousLinearMap.coe_zero]
  have : is_symmetric ((T.comp T.adjoint : V →ₗ[𝕜] V) - (T.adjoint.comp T : V →ₗ[𝕜] V)) :=
    fun u v => by
    simp_rw [← ContinuousLinearMap.mul_def, sub_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.mul_apply, inner_sub_left, inner_sub_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, sub_left_inj,
      ← ContinuousLinearMap.adjoint_inner_left T, ← ContinuousLinearMap.adjoint_inner_right T]
  simp_rw [← ContinuousLinearMap.mul_def] at this
  rw [← is_symmetric.inner_map_self_eq_zero this]
  simp_rw [sub_apply, inner_sub_left, ContinuousLinearMap.coe_coe, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K, ←
    ContinuousLinearMap.adjoint_inner_right T, inner_self_eq_norm_sq_to_K, sub_eq_zero, ←
    sq_eq_sq (norm_nonneg _) (norm_nonneg _), eq_comm]
  norm_cast

/-- if $T$ is normal, then $\textnormal{ker}(T) = \textnormal{ker}(T^*)$ -/
theorem LinearMap.IsStarNormal.ker_eq_ker_adjoint [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (h : IsStarNormal T) : T.ker = T.adjoint.ker := by
  ext <;>
    rw [mem_ker, mem_ker, ← norm_eq_zero, Iff.comm, ← norm_eq_zero, ←
      (LinearMap.IsStarNormal.norm_eq_adjoint T).mp h]

/-- if $T$ is normal, then $\textnormal{range}(T)=\textnormal{range}(T^*)$ -/
theorem LinearMap.IsStarNormal.range_eq_range_adjoint [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (h : IsStarNormal T) : T.range = T.adjoint.range := by
  rw [← Submodule.orthogonal_orthogonal T.adjoint.range, ← ker_is_ortho_adjoint_range,
    LinearMap.IsStarNormal.ker_eq_ker_adjoint T h, ker_is_ortho_adjoint_range, adjoint_adjoint,
    Submodule.orthogonal_orthogonal]

theorem ContinuousLinearMap.IsStarNormal.ker_eq_ker_adjoint [CompleteSpace V] (T : V →L[𝕜] V)
    (h : IsStarNormal T) : T.ker = T.adjoint.ker :=
  by
  ext; simp_rw [mem_ker, ContinuousLinearMap.toLinearMap_eq_coe, ContinuousLinearMap.coe_coe]
  rw [← norm_eq_zero, Iff.comm, ← norm_eq_zero, ←
    (ContinuousLinearMap.IsStarNormal.norm_eq_adjoint T).mp h]

theorem ContinuousLinearMap.ker_is_eq_ortho_adjoint_range {W : Type _} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W] (T : V →L[𝕜] W) :
    T.ker = T.adjoint.rangeᗮ := by
  ext
  simp_rw [Submodule.mem_orthogonal, LinearMap.mem_range, LinearMap.mem_ker,
    ContinuousLinearMap.toLinearMap_eq_coe, ContinuousLinearMap.coe_coe, forall_exists_index,
    forall_apply_eq_imp_iff, ContinuousLinearMap.adjoint_inner_left]
  exact
    ⟨fun h => by simp_rw [h, inner_zero_right, forall_const], fun h => inner_self_eq_zero.mp (h _)⟩

theorem ContinuousLinearMap.IsStarNormal.isCompl_ker_range [CompleteSpace V] (T : V →L[𝕜] V)
    [FiniteDimensional 𝕜 V] (h : IsStarNormal T) : IsCompl T.ker T.range :=
  by
  rw [ContinuousLinearMap.ker_is_eq_ortho_adjoint_range]
  apply IsCompl.symm
  suffices T.range = T.adjoint.range by rw [← this];
    exact Submodule.isCompl_orthogonal_of_completeSpace
  · apply_fun Submodule.orthogonal
    · nth_rw 1 [← ContinuousLinearMap.adjoint_adjoint T]
      simp_rw [← ContinuousLinearMap.ker_is_eq_ortho_adjoint_range]
      exact (ContinuousLinearMap.IsStarNormal.ker_eq_ker_adjoint T h).symm
    · intro U W hUW
      rw [← Submodule.orthogonal_orthogonal U, hUW]
      exact Submodule.orthogonal_orthogonal W

theorem ContinuousLinearMap.IsIdempotentElem.toLinearMap {E R : Type _} [Ring R] [AddCommMonoid E]
    [Module R E] [TopologicalSpace E] (T : E →L[R] E) :
    IsIdempotentElem T ↔ IsIdempotentElem T.toLinearMap :=
  by
  simp_rw [ContinuousLinearMap.toLinearMap_eq_coe, IsIdempotentElem, ContinuousLinearMap.ext_iff,
    LinearMap.ext_iff, ContinuousLinearMap.coe_coe]
  rfl

theorem ContinuousLinearMap.IsIdempotent.isSelfAdjoint_iff_ker_is_ortho_to_range
    [InnerProductSpace ℂ V] [CompleteSpace V] (T : V →L[ℂ] V) (h : IsIdempotentElem T) :
    IsSelfAdjoint T ↔ T.ker = T.rangeᗮ := by
  constructor
  · intro l;
    rw [← ContinuousLinearMap.adjoint_adjoint T, ←
      ContinuousLinearMap.ker_is_eq_ortho_adjoint_range, ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.IsStarNormal.ker_eq_ker_adjoint T l.is_star_normal
  · intro h1
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    apply eq_of_sub_eq_zero
    simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_sub, ← ext_iff, ContinuousLinearMap.coe_zero, ←
      inner_map_self_eq_zero]
    intro x
    rw [ContinuousLinearMap.IsIdempotentElem.toLinearMap, ContinuousLinearMap.toLinearMap_eq_coe] at
      h
    have := IsIdempotentElem.eq h
    rw [LinearMap.mul_eq_comp] at this
    obtain ⟨U, hT⟩ := (LinearMap.isProj_iff_idempotent ↑T).mpr this
    obtain ⟨v, w, hvw, hunique⟩ :=
      Submodule.existsUnique_add_of_isCompl (LinearMap.IsProj.isCompl_range_ker U (↑T) hT) x
    simp only [LinearMap.sub_apply, inner_sub_left, LinearMap.adjoint_inner_left]
    cases' SetLike.coe_mem w with y hy
    simp_rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.adjoint_inner_left, ←
      ContinuousLinearMap.coe_coe, ← hvw, map_add, linear_map.mem_ker.mp (SetLike.coe_mem v), ← hy,
      ← LinearMap.mul_apply, IsIdempotentElem.eq h, zero_add, hy, inner_add_left, inner_add_right, ←
      inner_conj_symm ↑w ↑v,
      (Submodule.mem_orthogonal T.ker ↑w).mp
        (by rw [h1]; intro y hy; rw [inner_eq_zero_symm]; exact hy w (SetLike.coe_mem w)) v
        (SetLike.coe_mem v),
      map_zero, zero_add, sub_self]

open scoped ComplexConjugate

open Module.End

/--
if $T$ is normal, then $\forall x \in V, x \in \textnormal{eigenspace}(T ,\mu) \iff x \in \textnormal{eigenspace}(T^* ,\bar{\mu})$ -/
theorem LinearMap.IsStarNormal.eigenvec_in_eigenspace_iff_eigenvec_in_adjoint_conj_eigenspace
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (h : IsStarNormal T) (μ : ℂ) :
    ∀ x : V, x ∈ eigenspace T μ ↔ x ∈ eigenspace T.adjoint (conj μ) :=
  by
  suffices
    ∀ T : V →ₗ[ℂ] V,
      IsStarNormal T → ∀ μ : ℂ, ∀ v : V, v ∈ eigenspace T μ → v ∈ eigenspace T.adjoint (conj μ)
    by
    intro v; refine' ⟨this T h μ v, _⟩
    intro hv; rw [← adjoint_adjoint T, ← IsROrC.conj_conj μ]
    apply this _ _ _ _ hv; exact IsStarNormal.star
  clear h μ T
  intro T h μ v hv
  have t1 : (T - μ • 1) v = 0 :=
    by
    rw [sub_apply, smul_apply, one_apply, sub_eq_zero]
    exact mem_eigenspace_iff.mp hv
  suffices (T.adjoint - conj μ • 1) v = 0
    by
    rw [mem_eigenspace_iff, ← sub_eq_zero]
    rw [sub_apply, smul_apply, one_apply] at this; exact this
  rw [← norm_eq_zero]
  have nh : IsStarNormal (T - μ • 1) := by
    apply IsStarNormal.mk
    rw [star_sub, star_smul, IsROrC.star_def, star_one, Commute, SemiconjBy]
    simp only [sub_mul, mul_sub, Commute.eq h.star_comm_self]
    simp only [smul_one_mul, smul_smul, mul_smul_comm, mul_one]
    rw [mul_comm, sub_sub_sub_comm]
  have : (T - μ • 1).adjoint = T.adjoint - conj μ • 1 := by
    simp only [← star_eq_adjoint, star_sub, star_smul, IsROrC.star_def, star_one]
  rw [← this, ← (LinearMap.IsStarNormal.norm_eq_adjoint (T - μ • 1)).mp nh, t1, norm_zero]

end IsStarNormal

/-- $T$ is injective if and only if $T^*$ is surjective  -/
theorem LinearMap.injective_iff_adjoint_surjective {W : Type _} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) :
    Function.Injective T ↔ Function.Surjective T.adjoint := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.range_eq_top, ker_is_ortho_adjoint_range,
    Submodule.orthogonal_eq_bot_iff]

