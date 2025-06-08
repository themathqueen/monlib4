/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Ips.Pos
import Monlib.LinearAlgebra.Ips.Ips
import Monlib.LinearAlgebra.Ips.Symm
import Monlib.RepTheory.AutMat
import Monlib.LinearAlgebra.KroneckerToTensor
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Monlib.LinearAlgebra.Ips.RankOne
import Monlib.LinearAlgebra.Ips.Basic
import Monlib.LinearAlgebra.IsProj'
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!

# Minimal projections

In this file we show some necessary results for positive operators on a Hilbert space.

## main results

**Theorem.** If $p,q$ are (orthogonal) projections on $E$,
  then the following are equivalent:
   - (i) $pq = p = qp$
   - (ii) $p(E) \subseteq q(E)$
   - (iii) $q - p$ is an (orthogonal) projection
   - (iv) $q - p$ is positive

for part (iii), it suffices to show that the element is an idempotent since
  $q - p$ is self-adjoint

it turns out that $qp = p$ (from (i)) if and only if (ii) and
  (i) if and only if (iii) for idempotent operators on a module over a ring
  (see `IsIdempotentElem.comp_idempotent_iff` and
   `linear_map.commutes_iff_isIdempotent_elem`)

obviously when $p,q$ are self-adjoint operators, then $pq = p$ iff $qp=p$
  (see `self_adjoint_commutes_iff`)

so then, obviously, (ii) if and only if (iii) for idempotent self-adjoint operators as well
  (see `continuous_linear_map.image_subset_iff_sub_of_is_idempotent`)

we finally have (i) if and only if (iv) for idempotent self-adjoint operators on a
  finite-dimensional complex-Hilbert space:
  (see `orthogonal_projection_is_positive_iff_commutes`)

## main definition

* an operator is non-negative means that it is positive:
  $0 \leq p$ if and only if $p$ is positive
  (see `is_positive.is_nonneg`)

-/

open Module.End

section

variable {R E : Type _} [Ring R] [AddCommGroup E] [Module R E]

open Submodule LinearMap

/-- given an idempotent linear operator $p$, we have
  $x \in \textnormal{range}(p)$ if and only if $p(x) = x$ (for all $x \in E$) -/
theorem IsIdempotentElem.mem_range_iff {p : E →ₗ[R] E} (hp : IsIdempotentElem p) {x : E} :
    x ∈ range p ↔ p x = x := by
  simp_rw [mem_range]
  constructor
  · rintro ⟨y, hy⟩
    nth_rw 1 [← hy]
    rw [← mul_apply, hp.eq, hy]
  · intro h
    use x

variable {U V : Submodule R E} {q : E →ₗ[R] E} (hq : IsIdempotentElem q)

include hq in
/-- given idempotent linear operators $p,q$,
  we have $qp = p$ iff $p(E) \subseteq q(E)$ -/
theorem IsIdempotentElem.comp_idempotent_iff
  {E₂ : Type*} [AddCommGroup E₂] [Module R E₂] (p : E₂ →ₗ[R] E) :
    q.comp p = p ↔ LinearMap.range p ≤ LinearMap.range q :=
by
  simp_rw [LinearMap.ext_iff, comp_apply, ← IsIdempotentElem.mem_range_iff hq,
    SetLike.le_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
include hq in
theorem IsIdempotentElem.comp_idempotent_iff'
  {E₂ : Type*} [AddCommGroup E₂] [Module R E₂] (p : E₂ →ₗ[R] E) :
    q.comp p = p ↔ Submodule.map p ⊤ ≤ Submodule.map q ⊤ :=
by simp_rw [IsIdempotentElem.comp_idempotent_iff hq, Submodule.map_top]

variable {p : E →ₗ[R] E} (hp : IsIdempotentElem p)

include hp hq in
/-- if $p,q$ are idempotent operators and $pq = p = qp$,
  then $q - p$ is an idempotent operator -/
theorem LinearMap.isIdempotentElem_sub_of (h : p.comp q = p ∧ q.comp p = p) :
    IsIdempotentElem (q - p) := by
  simp_rw [IsIdempotentElem, mul_eq_comp, sub_comp, comp_sub, h.1, h.2, ← mul_eq_comp, hp.eq, hq.eq,
    sub_self, sub_zero]

/-- if $p,q$ are idempotent operators and $q - p$ is also an idempotent
  operator, then $pq = p = qp$ -/
theorem LinearMap.commutes_of_isIdempotentElem {E 𝕜 : Type _} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] {p q : E →ₗ[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : IsIdempotentElem (q - p)) : p.comp q = p ∧ q.comp p = p :=
  by
  simp_rw [IsIdempotentElem, mul_eq_comp, comp_sub, sub_comp, ← mul_eq_comp, hp.eq, hq.eq, ←
    sub_add_eq_sub_sub, sub_right_inj, add_sub] at h
  have h' : (2 : 𝕜) • p = q.comp p + p.comp q :=
    by
    simp_rw [two_smul]
    nth_rw 2 [← h]
    simp_rw [mul_eq_comp, add_sub_cancel, add_comm]
  have H : ((2 : 𝕜) • p).comp q = q.comp (p.comp q) + p.comp q := by
    simp_rw [h', add_comp, comp_assoc, ← mul_eq_comp, hq.eq]
  simp_rw [add_comm, two_smul, add_comp, add_right_inj] at H
  have H' : q.comp ((2 : 𝕜) • p) = q.comp p + q.comp (p.comp q) := by
    simp_rw [h', comp_add, ← comp_assoc, ← mul_eq_comp, hq.eq]
  simp_rw [two_smul, comp_add, add_right_inj] at H'
  have H'' : q.comp p = p.comp q := by
    simp_rw [H']
    exact H.symm
  rw [← H'', and_self_iff, ← smul_right_inj (two_ne_zero' 𝕜), h', ← H'', two_smul]

/-- given idempotent operators $p,q$,
  we have $pq = p = qp$ iff $q - p$ is an idempotent operator -/
theorem LinearMap.commutes_iff_isIdempotentElem {E 𝕜 : Type _} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] {p q : E →ₗ[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p.comp q = p ∧ q.comp p = p ↔ IsIdempotentElem (q - p) :=
  ⟨fun h => LinearMap.isIdempotentElem_sub_of hq hp h, fun h =>
    LinearMap.commutes_of_isIdempotentElem hp hq h⟩

end

open ContinuousLinearMap

variable {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]

local notation "P" => Submodule.orthogonalProjection

/-- given self-adjoint operators $p,q$,
  we have $pq=p$ iff $qp=p$ -/
theorem self_adjoint_proj_commutes [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E}
    (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) : p.comp q = p ↔ q.comp p = p :=
  by
  constructor <;> intro h <;>
  · apply_fun adjoint using star_injective
    simp only [adjoint_comp, isSelfAdjoint_iff'.mp hpa, isSelfAdjoint_iff'.mp hqa, h]

local notation "↥P" => orthogonalProjection'

open Submodule

theorem orthogonalProjection.isIdempotentElem [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsIdempotentElem (↥P U) :=
  by
  rw [IsIdempotentElem]
  ext
  simp_rw [ContinuousLinearMap.mul_apply, orthogonalProjection'_eq, comp_apply, Submodule.subtypeL_apply,
    orthogonalProjection_mem_subspace_eq_self]

class ContinuousLinearMap.IsOrthogonalProjection [InnerProductSpace 𝕜 E]
  (T : E →L[𝕜] E) : Prop where
  isIdempotent : IsIdempotentElem T
  kerEqRangeOrtho : LinearMap.ker T = (LinearMap.range T)ᗮ

lemma ContinuousLinearMap.IsOrthogonalProjection.eq [InnerProductSpace 𝕜 E]
  {T : E →L[𝕜] E} (hT : T.IsOrthogonalProjection) :
    IsIdempotentElem T ∧ (LinearMap.ker T = (LinearMap.range T)ᗮ) :=
⟨hT.1, hT.2⟩

theorem IsIdempotentElem.clm_to_lm [InnerProductSpace 𝕜 E] {T : E →L[𝕜] E} :
    IsIdempotentElem T ↔ IsIdempotentElem (T : E →ₗ[𝕜] E) :=
  by
  simp_rw [IsIdempotentElem, Module.End.mul_eq_comp, ← coe_comp, coe_inj]
  rfl

lemma ContinuousLinearMap.HasOrthogonalProjection_of_isOrthogonalProjection [InnerProductSpace 𝕜 E]
    {T : E →L[𝕜] E} [h : T.IsOrthogonalProjection] : HasOrthogonalProjection (LinearMap.range T) :=
by
  constructor
  intro x
  rw [← h.kerEqRangeOrtho]
  simp only [LinearMap.mem_range, LinearMap.mem_ker, map_sub, exists_exists_eq_and]
  simp_rw [← mul_apply, h.isIdempotent.eq]
  exact ⟨x, sub_self _⟩


lemma ker_to_clm
  {R R₂ M M₂ : Type*} [Semiring R]
  [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
  [TopologicalSpace M] [TopologicalSpace M₂]
  [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂} (f : M →SL[τ₁₂] M₂) :
    LinearMap.ker (ContinuousLinearMap.toLinearMap f) = LinearMap.ker f := rfl

lemma subtype_compL_ker [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
  (f : E →L[𝕜] U) :
    LinearMap.ker (U.subtypeL ∘L f) = (LinearMap.ker f) :=
  by
  rw [← ker_to_clm]
  simp only [coe_comp, Submodule.coe_subtypeL, LinearMap.ker_comp,
    Submodule.ker_subtype, Submodule.comap_bot]
  rfl


lemma orthogonalProjection.isOrthogonalProjection [InnerProductSpace 𝕜 E]
    (U : Submodule 𝕜 E) [h : HasOrthogonalProjection U] :
    (↥P U).IsOrthogonalProjection :=
by
  refine ⟨orthogonalProjection.isIdempotentElem _, ?_⟩
  rw [orthogonalProjection.range, ← ker_orthogonalProjection, orthogonalProjection'_eq,
    subtype_compL_ker]

open LinearMap in
/-- given any idempotent operator $T ∈ L(V)$, then `is_compl T.ker T.range`,
in other words, there exists unique $v ∈ \textnormal{ker}(T)$ and $w ∈ \textnormal{range}(T)$ such that $x = v + w$ -/
theorem IsIdempotentElem.isCompl_range_ker {V R : Type _} [Semiring R] [AddCommGroup V]
    [Module R V] {T : V →ₗ[R] V} (h : IsIdempotentElem T) : IsCompl (ker T) (range T) :=
  by
  constructor
  · rw [disjoint_iff]
    ext x
    simp only [Submodule.mem_bot, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range,
      ContinuousLinearMap.coe_coe]
    constructor
    · intro h'
      cases' h'.2 with y hy
      rw [← hy, ← IsIdempotentElem.eq h, Module.End.mul_apply, hy]
      exact h'.1
    · intro h'
      rw [h', map_zero]
      simp only [true_and]
      use x
      simp only [h', map_zero, eq_self_iff_true]
  · suffices ∀ x : V, ∃ v : ker T, ∃ w : range T, x = v + w
      by
      rw [codisjoint_iff, ← Submodule.add_eq_sup]
      ext x
      rcases this x with ⟨v, w, hvw⟩
      simp only [Submodule.mem_top, iff_true, hvw]
      apply Submodule.add_mem_sup (SetLike.coe_mem v) (SetLike.coe_mem w)
    intro x
    use ⟨x - T x, ?_⟩, ⟨T x, ?_⟩
    . simp only [Submodule.coe_mk, sub_add_cancel]
    . rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, IsIdempotentElem.eq h, sub_self]
    . rw [LinearMap.mem_range]; simp only [exists_apply_eq_apply]

theorem IsCompl.of_orthogonal_projection [InnerProductSpace 𝕜 E] {T : E →L[𝕜] E}
    (h : T.IsOrthogonalProjection) : IsCompl (LinearMap.ker T) (LinearMap.range T) :=
IsIdempotentElem.isCompl_range_ker ((IsIdempotentElem.toLinearMap _).mp h.1)

@[simp]
theorem orthogonalProjection.ker [InnerProductSpace 𝕜 E]
  {K : Submodule 𝕜 E} [HasOrthogonalProjection K] : LinearMap.ker (↥P K) = Kᗮ :=
by
  simp_rw [orthogonalProjection'_eq, ← ker_to_clm]
  simp only [coe_comp, Submodule.coe_subtypeL, LinearMap.ker_comp, Submodule.ker_subtype,
    Submodule.comap_bot, ker_to_clm, ker_orthogonalProjection]

theorem _root_.LinearMap.isIdempotentElem_of_isProj {V R : Type _} [Semiring R] [AddCommGroup V]
    [Module R V] {T : V →ₗ[R] V} {U : Submodule R V}
    (h : LinearMap.IsProj U T) :
  IsIdempotentElem T :=
by ext; exact h.2 _ (h.1 _)

/-- $P_V P_U = P_U$ if and only if $P_V - P_U$ is an orthogonal projection -/
theorem sub_of_isOrthogonalProjection [InnerProductSpace ℂ E] [CompleteSpace E]
    {U V : Submodule ℂ E} [CompleteSpace U] [CompleteSpace V] :
    (↥P V).comp (↥P U) = ↥P U ↔ (↥P V - ↥P U).IsOrthogonalProjection :=
  by
  let p := ↥P U
  let q := ↥P V
  have pp : p = U.subtypeL.comp (P U) := rfl
  have qq : q = V.subtypeL.comp (P V) := rfl
  have hp : IsIdempotentElem p := orthogonalProjection.isIdempotentElem U
  have hq : IsIdempotentElem q := orthogonalProjection.isIdempotentElem V
  have hpa := orthogonalProjection_isSelfAdjoint U
  have hqa := orthogonalProjection_isSelfAdjoint V
  have h2 := self_adjoint_proj_commutes hpa hqa
  simp_rw [orthogonalProjection', ← pp, ← qq] at *
  constructor
  · intro h
    have h_and : (p : E →ₗ[ℂ] E) ∘ₗ (q : E →ₗ[ℂ] E) = p ∧ (q : E →ₗ[ℂ] E) ∘ₗ (p : E →ₗ[ℂ] E) = p :=
      by simp_rw [← coe_comp, coe_inj, h2, and_self_iff, h]
    rw [LinearMap.commutes_iff_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
        (IsIdempotentElem.clm_to_lm.mp hq),
      ← coe_sub, ← IsIdempotentElem.clm_to_lm] at h_and
    refine' ⟨h_and, _⟩
    rw [← IsIdempotentElem.isSelfAdjoint_iff_ker_isOrtho_to_range _ (h_and)]
    exact IsSelfAdjoint.sub hqa hpa
  · rintro ⟨h1, _⟩
    simp_rw [IsIdempotentElem.clm_to_lm, coe_sub, ←
      LinearMap.commutes_iff_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
        (IsIdempotentElem.clm_to_lm.mp hq),
      ← coe_comp, coe_inj] at h1
    exact h1.2

section

/-- instance for `≤` on linear maps -/
instance LinearMap.IsSymmetric.hasLe {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : LE (E →ₗ[𝕜] E) :=
  by
  refine' { le := _ }
  intro u v
  exact (v - u : E →ₗ[𝕜] E).IsPositive'

@[reducible]
def SymmetricLM (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℂ g] :=
{x : g →ₗ[ℂ] g | LinearMap.IsSymmetric x}

@[reducible]
def SelfAdjointCLM (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℂ g]
  [CompleteSpace g] :=
{x : g →L[ℂ] g | IsSelfAdjoint x}

local notation "L(" x "," y ")" => x →L[y] x

local notation "l(" x "," y ")" => x →ₗ[y] x

open scoped ComplexOrder
set_option synthInstance.maxHeartbeats 40000 in
instance {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] : PartialOrder (E →ₗ[𝕜] E) where
  le := fun u v => LinearMap.IsPositive' (v - u : E →ₗ[𝕜] E)
  le_refl := fun a => by
    simp_rw [sub_self]
    constructor
    · intro u v
      simp_rw [LinearMap.zero_apply, inner_zero_left, inner_zero_right]
    · intro x
      simp_rw [LinearMap.zero_apply, inner_zero_right, le_refl]
  le_trans := by
    intro a b c hab hbc
    rw [← add_zero (c : E →ₗ[𝕜] E), ← sub_self ↑b, ← add_sub_assoc, add_sub_right_comm, add_sub_assoc]
    exact LinearMap.IsPositive'.add hbc hab
  le_antisymm := by
    rintro a b hba hab
    rw [← sub_eq_zero]
    rw [← LinearMap.IsSymmetric.inner_map_self_eq_zero hab.1]
    intro x
    have hba2 := hba.2 x
    rw [← neg_le_neg_iff, ← inner_neg_right, ← LinearMap.neg_apply, neg_sub, neg_zero] at hba2
    rw [hab.1]
    apply le_antisymm hba2 (hab.2 _)

/-- `p ≤ q` means `q - p` is positive -/
theorem LinearMap.IsPositive'.hasLe {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {p q : SymmetricLM E} : p ≤ q ↔ (q - p : l(E,ℂ)).IsPositive' := by rfl

noncomputable instance IsSymmetric.hasZero {E : Type _} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : Zero ↥{x : E →ₗ[ℂ] E | x.IsSymmetric} :=
  by
  fconstructor
  fconstructor
  exact 0
  simp_rw [Set.mem_setOf_eq, LinearMap.IsSymmetric, LinearMap.zero_apply, inner_zero_left,
    inner_zero_right, forall_const]

/-- saying `p` is positive is the same as saying `0 ≤ p` -/
theorem LinearMap.IsPositive'.is_nonneg {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {p : l(E,𝕜)} : p.IsPositive' ↔ 0 ≤ p :=
  by
  nth_rw 1 [← sub_zero p]
  rfl

end

/-- a self-adjoint idempotent operator is positive -/
theorem SelfAdjointAndIdempotent.is_positive {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {p : E →L[𝕜] E} (hp : IsIdempotentElem p)
    (hpa : IsSelfAdjoint p) : 0 ≤ p :=
  by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine' ⟨hpa, _⟩
  rw [← hp.eq]
  simp_rw [reApplyInnerSelf_apply, ContinuousLinearMap.mul_apply]
  intro x
  simp_rw [← adjoint_inner_right _ _ x, isSelfAdjoint_iff'.mp hpa]
  exact inner_self_nonneg

/-- an idempotent is positive if and only if it is self-adjoint -/
theorem IsIdempotentElem.is_positive_iff_self_adjoint [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {p : E →L[𝕜] E} (hp : IsIdempotentElem p) : 0 ≤ p ↔ IsSelfAdjoint p :=
  ⟨fun h => ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h).1, fun h =>
    SelfAdjointAndIdempotent.is_positive hp h⟩

theorem IsIdempotentElem.self_adjoint_is_positive_isOrthogonalProjection_tFAE {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {p : E →L[ℂ] E}
    (hp : IsIdempotentElem p) : List.TFAE [IsSelfAdjoint p, p.IsOrthogonalProjection, 0 ≤ p] :=
  by
  tfae_have 3 ↔ 1 := hp.is_positive_iff_self_adjoint
  tfae_have 2 → 1 := by
    intro h
    rw [IsIdempotentElem.isSelfAdjoint_iff_ker_isOrtho_to_range _ hp]
    exact h.2
  tfae_have 1 → 2 := by
    intro h
    rw [IsIdempotentElem.isSelfAdjoint_iff_ker_isOrtho_to_range _ hp] at h
    exact ⟨hp, h⟩
  tfae_finish

/-- orthogonal projections are obviously positive -/
theorem orthogonalProjection.is_positive [InnerProductSpace ℂ E] {U : Submodule ℂ E}
    [CompleteSpace E] [CompleteSpace U] : 0 ≤ U.subtypeL.comp (P U) :=
  SelfAdjointAndIdempotent.is_positive (orthogonalProjection.isIdempotentElem U)
    (orthogonalProjection_isSelfAdjoint U)

theorem SelfAdjointAndIdempotent.sub_is_positive_of [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {p q : E →L[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpa : IsSelfAdjoint p)
    (hqa : IsSelfAdjoint q) (h : p.comp q = p) : 0 ≤ q - p :=
  SelfAdjointAndIdempotent.is_positive
    (coe_inj.mp
      ((LinearMap.commutes_iff_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
            (IsIdempotentElem.clm_to_lm.mp hq)).mp
        ⟨coe_inj.mpr h, coe_inj.mpr ((self_adjoint_proj_commutes hpa hqa).mp h)⟩))
    (IsSelfAdjoint.sub hqa hpa)

/-- given orthogonal projections `Pᵤ,Pᵥ`,
  then `Pᵤ(Pᵥ)=Pᵤ` implies `Pᵥ-Pᵤ` is positive (i.e., `Pᵤ ≤ Pᵥ`) -/
theorem orthogonalProjection.sub_is_positive_of [InnerProductSpace ℂ E] {U V : Submodule ℂ E}
    [CompleteSpace U] [CompleteSpace V] [CompleteSpace E] (h : (↥P U).comp (↥P V) = ↥P U) :
    0 ≤ ↥P V - ↥P U :=
  SelfAdjointAndIdempotent.sub_is_positive_of (orthogonalProjection.isIdempotentElem U)
    (orthogonalProjection.isIdempotentElem V) (orthogonalProjection_isSelfAdjoint U)
    (orthogonalProjection_isSelfAdjoint V) h

/-- given orthogonal projections `Pᵤ,Pᵥ`,
  then if `Pᵥ - Pᵤ` is idempotent, then `Pᵤ Pᵥ = Pᵤ` -/
theorem orthogonal_projection_commutes_of_is_idempotent [InnerProductSpace ℂ E]
    {U V : Submodule ℂ E} [CompleteSpace U] [CompleteSpace V] [CompleteSpace E]
    (h : IsIdempotentElem (↥P V - ↥P U)) : (↥P V).comp (↥P U) = ↥P U :=
  by
  let p := ↥P U
  let q := ↥P V
  have pp : p = U.subtypeL.comp (P U) := rfl
  have qq : q = V.subtypeL.comp (P V) := rfl
  simp_rw [← pp, ← qq] at *
  have hp : IsIdempotentElem p := orthogonalProjection.isIdempotentElem U
  have hq : IsIdempotentElem q := orthogonalProjection.isIdempotentElem V
  exact
    coe_inj.mp
      (LinearMap.commutes_of_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
          (IsIdempotentElem.clm_to_lm.mp hq) (IsIdempotentElem.clm_to_lm.mp h)).2

open scoped FiniteDimensional

/-- copy of `linear_map.is_positive_iff_exists_adjoint_mul_self` -/
theorem ContinuousLinearMap.isPositive_iff_exists_adjoint_hMul_self [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] (T : E →L[𝕜] E) :
    T.IsPositive ↔ ∃ S : E →L[𝕜] E, T = adjoint S * S :=
  by
  rw [IsPositive.toLinearMap', LinearMap.isPositive'_iff_exists_adjoint_hMul_self]
  constructor <;> rintro ⟨S, hS⟩
  use LinearMap.toContinuousLinearMap S
  · ext
    rw [← ContinuousLinearMap.coe_coe T, hS]
    rfl
  · simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ← LinearMap.ext_iff] at *
    exact ⟨S, hS⟩

open RCLike
open scoped InnerProductSpace

/-- in a finite-dimensional complex Hilbert space `E`,
  if `p,q` are self-adjoint operators, then
  `p ≤ q` iff `∀ x ∈ E : ⟪x, p x⟫ ≤ ⟪x, q x⟫` -/
theorem ContinuousLinearMap.is_positive_le_iff_inner [InnerProductSpace 𝕜 E]
    [CompleteSpace E]
    {p q : E →L[𝕜] E} (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) :
    p ≤ q ↔ ∀ x : E, re ⟪x, p x⟫_𝕜 ≤ re ⟪x, q x⟫_𝕜 :=
  by
  rw [ContinuousLinearMap.le_def]
  constructor
  · intro h x
    rw [← sub_nonneg, ← map_sub, ← inner_sub_right, ← sub_apply]
    exact IsPositive.re_inner_nonneg_right h x
  · intro h
    refine' ⟨IsSelfAdjoint.sub hqa hpa, fun x => _⟩
    simp_rw [reApplyInnerSelf_apply, sub_apply, inner_sub_left, map_sub, sub_nonneg]
    nth_rw 1 [inner_re_symm]
    nth_rw 2 [inner_re_symm]
    exact h x

local notation "⟪" x "," y "⟫" => @inner 𝕜 _ _ x y

/-- given self-adjoint idempotent operators `p,q`, we have
  `∀ x ∈ E : ⟪x, p x⟫ ≤ ⟪x, q x⟫ ↔ ∀ x ∈ E, ‖p x‖ ≤ ‖q x‖` -/
theorem ContinuousLinearMap.hasLe_norm [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpa : IsSelfAdjoint p)
    (hqa : IsSelfAdjoint q) : (∀ x : E, re ⟪x,p x⟫ ≤ re ⟪x,q x⟫) ↔ ∀ x : E, ‖p x‖ ≤ ‖q x‖ :=
  by
  rw [← hp.eq, ← hq.eq]
  simp_rw [mul_apply, ← adjoint_inner_left _ (q _) _, ← adjoint_inner_left _ (p _) _,
    isSelfAdjoint_iff'.mp hpa, isSelfAdjoint_iff'.mp hqa, inner_self_eq_norm_sq, sq_le_sq,
    abs_norm, ← mul_apply, hp.eq, hq.eq]

@[simp]
theorem IsPositive.HasLe.sub [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E} :
    p ≤ q ↔ 0 ≤ q - p := by simp only [LE.le, sub_zero]

theorem self_adjoint_and_idempotent_is_positive_iff_commutes
    [InnerProductSpace ℂ E]
    [CompleteSpace E] {p q : E →L[ℂ] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpa : IsSelfAdjoint p)
    (hqa : IsSelfAdjoint q) : p ≤ q ↔ q.comp p = p :=
  by
  rw [← self_adjoint_proj_commutes hpa hqa, IsPositive.HasLe.sub]
  refine' ⟨fun h => _, fun h => SelfAdjointAndIdempotent.sub_is_positive_of hp hq hpa hqa h⟩
  rw [← IsPositive.HasLe.sub,
    ContinuousLinearMap.is_positive_le_iff_inner hpa hqa] at h
  symm
  rw [← sub_eq_zero]
  nth_rw 1 [← mul_one p]
  simp_rw [ContinuousLinearMap.mul_def, ← comp_sub, ← ContinuousLinearMap.inner_map_self_eq_zero, comp_apply, sub_apply,
    ContinuousLinearMap.one_apply]
  intro x
  specialize h ((1 - q) x)
  simp_rw [sub_apply, map_sub, ← ContinuousLinearMap.mul_apply, mul_one, hq.eq,
    sub_self, inner_zero_right, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.mul_apply, ← map_sub, zero_re] at h
  rw [← hp.eq, ContinuousLinearMap.mul_apply, ← adjoint_inner_left, isSelfAdjoint_iff'.mp hpa, re_inner_self_nonpos] at h
  rw [h, inner_zero_left]

/-- in a complex-finite-dimensional Hilbert space `E`, we have
  `Pᵤ ≤ Pᵤ` iff `PᵥPᵤ = Pᵤ` -/
theorem orthogonal_projection_is_le_iff_commutes [InnerProductSpace ℂ E]
    {U V : Submodule ℂ E} [CompleteSpace E] [CompleteSpace U] [CompleteSpace V] :
    ↥P U ≤ ↥P V ↔ (↥P V).comp (↥P U) = ↥P U :=
  self_adjoint_and_idempotent_is_positive_iff_commutes (orthogonalProjection.isIdempotentElem U)
    (orthogonalProjection.isIdempotentElem V) (orthogonalProjection_isSelfAdjoint U)
    (orthogonalProjection_isSelfAdjoint V)

theorem orthogonalProjection.is_le_iff_subset [InnerProductSpace ℂ E] {U V : Submodule ℂ E}
    [CompleteSpace E]
    [CompleteSpace U] [CompleteSpace V] : ↥P U ≤ ↥P V ↔ U ≤ V := by
  simp_rw [orthogonal_projection_is_le_iff_commutes, ← coe_inj, coe_comp,
    IsIdempotentElem.comp_idempotent_iff
      (IsIdempotentElem.clm_to_lm.mp (orthogonalProjection.isIdempotentElem V)),
    range_toLinearMap, orthogonalProjection.range]

theorem Submodule.map_to_linearMap [Module 𝕜 E] {p : E →L[𝕜] E} {U : Submodule 𝕜 E} :
    Submodule.map (p : E →ₗ[𝕜] E) U = Submodule.map p U :=
  rfl

/-- given self-adjoint idempotent operators `p,q` we have,
  `p(E) ⊆ q(E)` iff `q - p` is an idempotent operator -/
theorem ContinuousLinearMap.image_subset_iff_sub_of_is_idempotent [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {p q : E →L[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) :
    LinearMap.range p ≤ LinearMap.range q ↔ IsIdempotentElem (q - p) := by
  simp_rw [IsIdempotentElem.clm_to_lm, coe_sub, ←
    LinearMap.commutes_iff_isIdempotentElem (IsIdempotentElem.clm_to_lm.mp hp)
      (IsIdempotentElem.clm_to_lm.mp hq),
    ← coe_comp, coe_inj, self_adjoint_proj_commutes hpa hqa, and_self_iff, ← coe_inj, coe_comp,
    IsIdempotentElem.comp_idempotent_iff (IsIdempotentElem.clm_to_lm.mp hq)]
  rfl

section MinProj

/-- definition of a map being a minimal projection -/
def ContinuousLinearMap.IsMinimalProjection [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (x : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  IsSelfAdjoint x ∧ Module.finrank 𝕜 U = 1 ∧ LinearMap.IsProj U x

/-- definition of orthogonal projection being minimal
  i.e., when the dimension of its space equals one -/
def orthogonalProjection.IsMinimalProjection [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [CompleteSpace U] : Prop :=
  Module.finrank 𝕜 U = 1

open FiniteDimensional

/-- when a submodule `U` has dimension `1`, then
  for any submodule `V`, we have `V ≤ U` if and only if `V = U` or `V = 0` -/
theorem Submodule.le_finrank_one
  {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
  (U V : Submodule R M) [Module.Finite R ↥U] [Module.Finite R ↥V]
  (hU : Module.finrank R U = 1) : V ≤ U ↔ V = U ∨ V = 0 :=
  by
  simp_rw [Submodule.zero_eq_bot]
  constructor
  · intro h
    have : Module.finrank R V ≤ 1 := by
      rw [← hU]
      apply Submodule.finrank_mono h
    have : Module.finrank R V = 0 ∨ Module.finrank R V = 1 := Order.le_succ_bot_iff.mp this
    rcases this with (this_1 | this_1)
    · simp only [Submodule.finrank_eq_zero] at this_1
      right
      exact this_1
    · left
      apply eq_of_le_of_finrank_eq h
      simp_rw [this_1, hU]
  · intro h
    rcases h with (⟨rfl, rfl⟩ | h)
    · exact le_refl U
    · rw [h]
      exact bot_le

/-- for orthogonal projections `Pᵤ,Pᵥ`,
  if `Pᵤ` is a minimal orthogonal projection, then
  for any `Pᵥ` if `Pᵥ ≤ Pᵤ` and `Pᵥ ≠ 0`, then `Pᵥ = Pᵤ` -/
theorem orthogonalProjection.isMinimalProjection_of
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  (U W : Submodule ℂ E) [Module.Finite ℂ ↥U] [Module.Finite ℂ ↥W]
  (hU : orthogonalProjection.IsMinimalProjection U)
  (hW : ↥P W ≤ ↥P U) (h : ↥P W ≠ 0) :
    ↥P W = ↥P U :=
  by
  simp_rw [orthogonalProjection'_eq, le_antisymm_iff,
    ← orthogonalProjection'_eq]
  refine' ⟨hW, _⟩
  rw [orthogonalProjection.is_le_iff_subset] at hW ⊢
  have := Submodule.finrank_mono hW
  simp_rw [orthogonalProjection.IsMinimalProjection] at hU
  rw [Submodule.le_finrank_one U W hU] at hW
  cases' hW with hW1 hW2
  · simp_rw [hW1, le_refl]
  · simp_rw [hW2, Submodule.zero_eq_bot, orthogonalProjection'_eq, orthogonalProjection_bot,
      comp_zero] at h
    contradiction

/-- any rank one operator given by a norm one vector is a minimal projection -/
theorem rankOne_self_isMinimalProjection [InnerProductSpace ℂ E] [CompleteSpace E] {x : E}
    (h : ‖x‖ = 1) : (rankOne ℂ x x).IsMinimalProjection (Submodule.span ℂ {x}) :=
  by
  refine' ⟨rankOne_self_isSelfAdjoint, _⟩
  simp_rw [finrank_eq_one_iff']
  constructor
  · use⟨x, Submodule.mem_span_singleton_self x⟩
    simp_rw [ne_eq, Submodule.mk_eq_zero, SetLike.mk_smul_mk]
    refine' ⟨norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero), fun w => _⟩
    cases' Submodule.mem_span_singleton.mp (SetLike.coe_mem w) with r hr
    use r
    simp_rw [hr]
  · apply LinearMap.IsProj.mk
    simp_rw [Submodule.mem_span_singleton, rankOne_apply, exists_apply_eq_apply, forall_const]
    simp_rw [Submodule.mem_span_singleton, rankOne_apply, forall_exists_index,
      forall_apply_eq_imp_iff, inner_smul_right, inner_self_eq_norm_sq_to_K, h, ofReal_one,
      one_pow, mul_one, forall_const]

/-- if `x ∈ E` then we can normalize this (i.e., there exists `y ∈ E`
  such that `∥y∥ = 1` where `x = r • y` for some `r ∈ ℝ`) unless `x = 0` -/
theorem normalize_op [InnerProductSpace ℂ E] (x : E) :
    (∃ (y : E) (r : ℝ), ‖y‖ = 1 ∧ x = (r : ℂ) • y) ∨ x = 0 :=
  by
  by_cases A : x = 0
  · right
    exact A
  · have B : ‖x‖ ≠ 0 := by
      simp only [ne_eq, norm_eq_zero]
      exact A
    left
    use ((1 / ‖x‖) • x)
    use‖x‖
    constructor
    · simp_rw [norm_smul, one_div, norm_inv, norm_norm, mul_comm, mul_inv_cancel₀ B]
    · simp_rw [one_div, Complex.coe_smul, smul_inv_smul₀ B]

/-- given any non-zero `x ∈ E`, we have
  `1 / ‖x‖ ^ 2 • |x⟩⟨x|` is a minimal projection -/
theorem rankOne_self_isMinimalProjection' [InnerProductSpace ℂ E] [CompleteSpace E] {x : E} (h : x ≠ 0) :
    IsMinimalProjection ((1 / ‖x‖ ^ 2) • rankOne ℂ x x) (Submodule.span ℂ {x}) :=
  by
  rcases normalize_op x with ⟨y, r, ⟨hy, hx⟩⟩
  · have : r ^ 2 ≠ 0 := by
      intro d
      rw [pow_eq_zero_iff two_ne_zero] at d
      rw [d, Complex.coe_smul, zero_smul] at hx
      contradiction
    simp_rw [hx, Complex.coe_smul, one_div, ← Complex.coe_smul, map_smulₛₗ, LinearMap.smul_apply,
      RingHom.id_apply, Complex.conj_ofReal,
      norm_smul, mul_pow, Complex.norm_real, mul_inv, smul_smul, hy,
      one_pow, inv_one, mul_one, Real.norm_eq_abs, ← abs_pow, pow_two, abs_mul_self, ← pow_two,
      Complex.ofReal_inv, Complex.ofReal_pow, Complex.coe_smul]
    norm_cast
    rw [inv_mul_cancel₀ this, one_smul]
    have : Submodule.span ℂ {((r : ℝ) : ℂ) • y} = Submodule.span ℂ {y} :=
      by
      rw [Submodule.span_singleton_smul_eq _]
      refine' Ne.isUnit _
      rw [ne_eq]
      rw [← pow_eq_zero_iff two_ne_zero]
      norm_cast
    rw [← Complex.coe_smul, this]
    exact rankOne_self_isMinimalProjection hy
  · contradiction

lemma LinearMap.range_of_isProj {R M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  {p : M →ₗ[R] M} {U : Submodule R M}
  (hp : LinearMap.IsProj U p) :
  LinearMap.range p = U :=
by
  ext x
  rw [mem_range]
  refine ⟨λ ⟨y, hy⟩ => ?_, λ h => ⟨x, hp.map_id _ h⟩⟩
  . rw [← hy]
    exact hp.map_mem y

open scoped FiniteDimensional
set_option synthInstance.maxHeartbeats 200000 in
/-- a linear operator is an orthogonal projection onto a submodule, if and only if
  it is self-adjoint and idempotent;
  so it always suffices to say `p = p⋆ = p²` -/
theorem orthogonal_projection_iff [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {p : E →L[𝕜] E} : (∃ (U : Submodule 𝕜 E), --(hU : CompleteSpace U)
      ↥P U = p)
      ↔ IsSelfAdjoint p ∧ IsIdempotentElem p :=
  by
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨orthogonalProjection_isSelfAdjoint _, orthogonalProjection.isIdempotentElem _⟩
  · rintro ⟨h1, h2⟩
    simp_rw [IsIdempotentElem, ContinuousLinearMap.mul_def, ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe,
      coe_comp, ← LinearMap.ext_iff] at h2
    rcases(LinearMap.isProj_iff_isIdempotentElem _).mpr h2 with ⟨W, hp⟩
    let p' := isProj' hp
    have hp' : p' = isProj' hp := rfl
    simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ← isProj'_apply hp,
      orthogonalProjection'_eq_linear_proj', ← hp']
    rw [← LinearMap.linearProjOfIsCompl_of_proj p' (isProj'_eq hp)]
    use W
    . intro x
      simp_rw [LinearMap.coe_comp, Submodule.coe_subtype]
      suffices this : LinearMap.ker p' = Wᗮ
        by simp_rw [this]; rfl
      ext y
      simp_rw [LinearMap.mem_ker, Submodule.mem_orthogonal]
      constructor
      · intro hp'y u hu
        rw [← hp.2 u hu, ContinuousLinearMap.coe_coe, ← adjoint_inner_right,
          IsSelfAdjoint.adjoint_eq h1, ← ContinuousLinearMap.coe_coe, ← isProj'_apply hp, ← hp', hp'y,
          Submodule.coe_zero, inner_zero_right]
      · intro h
        rw [← Submodule.coe_eq_zero, ← @inner_self_eq_zero 𝕜, isProj'_apply hp,
          ContinuousLinearMap.coe_coe, ← adjoint_inner_left, IsSelfAdjoint.adjoint_eq h1, ←
          ContinuousLinearMap.coe_coe, ← LinearMap.comp_apply, h2,
          h _ (LinearMap.IsProj.map_mem hp _)]
    -- . have : p = W.subtype ∘ₗ p' := by rfl
    --   rw [← LinearMap.range_of_isProj hp]
    --   simp only [range_toLinearMap]

set_option synthInstance.maxHeartbeats 200000 in
/-- a linear operator is an orthogonal projection onto a submodule, if and only if
  it is a self-adjoint linear projection onto the submodule;
  also see `orthogonal_projection_iff` -/
theorem orthogonal_projection_iff' [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {p : E →L[𝕜] E} (U : Submodule 𝕜 E) : ↥P U = p ↔ IsSelfAdjoint p ∧ LinearMap.IsProj U p :=
  by
  constructor
  · intro h
    rw [← h]
    refine' ⟨orthogonalProjection_isSelfAdjoint _, _⟩
    apply LinearMap.IsProj.mk
    simp_rw [orthogonalProjection'_apply, Submodule.coe_mem, forall_const]
    simp_rw [orthogonalProjection'_apply, orthogonalProjection_eq_self_iff, imp_self, forall_const]
  · rintro ⟨h, h2⟩
    have : IsIdempotentElem p :=
      by
      simp_rw [IsIdempotentElem.toLinearMap, ← LinearMap.isProj_iff_isIdempotentElem]
      use U
      apply LinearMap.IsProj.mk <;> simp_rw [ContinuousLinearMap.coe_coe]
      exact h2.1
      exact h2.2
    have hp : LinearMap.IsProj U (p : E →ₗ[𝕜] E) :=
      by
      apply LinearMap.IsProj.mk <;> simp_rw [ContinuousLinearMap.coe_coe]
      exact h2.1
      exact h2.2
    simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe,
      orthogonalProjection'_eq_linear_proj']
    let p' := isProj' hp
    have hp' : p' = isProj' hp := rfl
    simp_rw [← isProj'_apply hp, ← hp']
    rw [← LinearMap.linearProjOfIsCompl_of_proj p' (isProj'_eq hp)]
    simp_rw [LinearMap.coe_comp, Submodule.coe_subtype]
    intro x
    suffices this : LinearMap.ker p' = Uᗮ
      by simp_rw [this]; rfl
    ext y
    simp_rw [LinearMap.mem_ker, Submodule.mem_orthogonal]
    constructor
    · intro hp'y u hu
      rw [← hp.2 u hu, ContinuousLinearMap.coe_coe, ← adjoint_inner_right,
        IsSelfAdjoint.adjoint_eq h, ← ContinuousLinearMap.coe_coe, ← isProj'_apply hp, ← hp', hp'y,
        Submodule.coe_zero, inner_zero_right]
    · intro h'
      rw [← Submodule.coe_eq_zero, ← @inner_self_eq_zero 𝕜, isProj'_apply hp,
        ContinuousLinearMap.coe_coe, ← adjoint_inner_left, IsSelfAdjoint.adjoint_eq h, ←
        ContinuousLinearMap.mul_apply, this, h' _ (LinearMap.IsProj.map_mem h2 _)]

set_option synthInstance.maxHeartbeats 200000 in
theorem orthogonalProjection.isMinimalProjection_to_clm [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) :
    (↥P U).IsMinimalProjection U ↔ orthogonalProjection.IsMinimalProjection U :=
  by
  refine' ⟨fun h => h.2.1, fun h => _⟩
  rw [ContinuousLinearMap.IsMinimalProjection, and_left_comm, ← orthogonal_projection_iff' U]
  refine' ⟨h, _⟩
  rfl

theorem Submodule.isOrtho_iff_inner_eq' {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {U W : Submodule 𝕜 E} :
    U ⟂ W ↔ ∀ (u : ↥U) (w : ↥W), inner 𝕜 (u : E) (w : E) = 0 :=
  by
  rw [Submodule.isOrtho_iff_inner_eq]
  constructor
  · intro h u w
    exact h _ (SetLike.coe_mem _) _ (SetLike.coe_mem _)
  · intro h x hx y hy
    exact h ⟨x, hx⟩ ⟨y, hy⟩

-- moved from `ips.lean`
/-- `U` and `W` are mutually orthogonal if and only if `(P U).comp (P W) = 0`,
where `P U` is `orthogonal_projection U` -/
theorem Submodule.is_pairwise_orthogonal_iff_orthogonal_projection_comp_eq_zero
    [InnerProductSpace 𝕜 E] (U W : Submodule 𝕜 E)
    [HasOrthogonalProjection U] [HasOrthogonalProjection W] :
    U ⟂ W ↔ (↥P U).comp (↥P W) = 0 :=
  by
  rw [Submodule.isOrtho_iff_inner_eq']
  constructor
  · intro h
    ext v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, ← @inner_self_eq_zero 𝕜,
      orthogonalProjection'_apply, orthogonalProjection'_apply, ←
      inner_orthogonalProjection_left_eq_right, orthogonalProjection_mem_subspace_eq_self]
    exact h _ _
  · intro h x y
    rw [← orthogonalProjection_eq_self_iff.mpr (SetLike.coe_mem x), ←
      orthogonalProjection_eq_self_iff.mpr (SetLike.coe_mem y),
      inner_orthogonalProjection_left_eq_right, ← orthogonalProjection'_apply, ←
      orthogonalProjection'_apply, ← ContinuousLinearMap.comp_apply, h,
      ContinuousLinearMap.zero_apply, inner_zero_right]

--
theorem orthogonalProjection.orthogonal_complement_eq [InnerProductSpace 𝕜 E]
    (U : Submodule 𝕜 E) [HasOrthogonalProjection U] : ↥P Uᗮ = 1 - ↥P U :=
  by
  have : 1 = id 𝕜 E := rfl
  simp_rw [this, id_eq_sum_orthogonalProjection_self_orthogonalComplement U,
    orthogonalProjection'_eq, add_sub_cancel_left]

example [InnerProductSpace ℂ E] {U W : Submodule ℂ E} [CompleteSpace E] [CompleteSpace U]
  [CompleteSpace W] :
  (↥P U).comp (↥P W) = 0 ↔ ↥P U + ↥P W ≤ 1 := by
  simp_rw [← Submodule.is_pairwise_orthogonal_iff_orthogonal_projection_comp_eq_zero,
    Submodule.isOrtho_iff_le, ← orthogonalProjection.is_le_iff_subset,
    orthogonalProjection.orthogonal_complement_eq, add_comm (↥P U) (↥P W), LE.le,
    sub_add_eq_sub_sub]

end MinProj

section
  lemma ContinuousLinearMap.isOrthogonalProjection_iff
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) :
    T.IsOrthogonalProjection ↔ IsIdempotentElem T ∧ LinearMap.ker T = (LinearMap.range T)ᗮ :=
  ⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

  open scoped FiniteDimensional
  theorem ContinuousLinearMap.isOrthogonalProjection_iff'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {p : E →L[ℂ] E} :
    IsOrthogonalProjection p
    ↔ IsIdempotentElem p ∧ IsSelfAdjoint p :=
  by

    rw [isOrthogonalProjection_iff]
    simp only [and_congr_right_iff]
    intro h
    have := List.TFAE.out (IsIdempotentElem.self_adjoint_is_positive_isOrthogonalProjection_tFAE h) 0 1
    rw [this, isOrthogonalProjection_iff]
    simp only [h, true_and]

  lemma LinearMap.isSelfAdjoint_toContinuousLinearMap
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (f : E →ₗ[𝕜] E) :
      _root_.IsSelfAdjoint (LinearMap.toContinuousLinearMap f) ↔ _root_.IsSelfAdjoint f :=
  by
    simp_rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, isSymmetric_iff_isSelfAdjoint]
    rfl

  lemma LinearMap.isOrthogonalProjection_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) :
    (LinearMap.toContinuousLinearMap T).IsOrthogonalProjection
      ↔ IsIdempotentElem T ∧ IsSelfAdjoint T :=
  by rw [ContinuousLinearMap.isOrthogonalProjection_iff',
    isSelfAdjoint_toContinuousLinearMap,
    ContinuousLinearMap.IsIdempotentElem.toLinearMap]; simp only [coe_toContinuousLinearMap]
end

lemma lmul_isIdempotentElem_iff {R A : Type*} [CommSemiring R]
  [Semiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (a : A) :
  (IsIdempotentElem (lmul a : _ →ₗ[R] _)) ↔ (IsIdempotentElem a) :=
by
  simp_rw [IsIdempotentElem, mul_eq_comp, lmul_eq_mul, ← LinearMap.mulLeft_mul]
  refine ⟨λ h => ?_, λ h => by rw [h]⟩
  rw [LinearMap.ext_iff] at h
  specialize h 1
  simp_rw [LinearMap.mulLeft_apply, mul_one] at h
  exact h

lemma lmul_tmul {R A B : Type*} [CommSemiring R]
  [Semiring A] [Semiring B] [Module R A] [Module R B] [SMulCommClass R A A]
  [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B] (a : A) (b : B) :
  lmul (a ⊗ₜ[R] b) = TensorProduct.map (lmul a) (lmul b) :=
by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, TensorProduct.map_tmul, lmul_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

lemma lmul_eq_lmul_iff {R A : Type*} [CommSemiring R]
  [Semiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (a b : A) :
  lmul a = (lmul b : _ →ₗ[R] _) ↔ a = b :=
by
  refine ⟨λ h => ?_, λ h => by rw [h]⟩
  rw [LinearMap.ext_iff] at h
  specialize h 1
  simp_rw [lmul_apply, mul_one] at h
  exact h

lemma isIdempotentElem_algEquiv_iff {R A B : Type*} [CommSemiring R]
  [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
  (φ : A ≃ₐ[R] B)
  (a : A) :
  IsIdempotentElem (φ a : B) ↔ IsIdempotentElem a :=
by
  simp_rw [IsIdempotentElem, ← map_mul, Function.Injective.eq_iff (AlgEquiv.injective _)]

theorem orthogonalProjection'_isProj {R M : Type*} [RCLike R] [NormedAddCommGroup M]
  [InnerProductSpace R M] (U : Submodule R M) [HasOrthogonalProjection U] :
  LinearMap.IsProj U (orthogonalProjection' U) :=
by
  constructor <;>
  simp only [orthogonalProjection'_eq, coe_comp', Submodule.coe_subtypeL', Submodule.coe_subtype,
    Function.comp_apply, SetLike.coe_mem, implies_true,
    orthogonalProjection_eq_self_iff, imp_self, implies_true]

theorem LinearMap.isProj_iff {S M F : Type*} [Semiring S] [AddCommMonoid M]
    [Module S M] (m : Submodule S M) [FunLike F M M] (f : F) :
  LinearMap.IsProj m f ↔ (∀ x, f x ∈ m) ∧ (∀ x ∈ m, f x = x) :=
⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

theorem LinearMap.isProj_coe {R M : Type*} [RCLike R] [NormedAddCommGroup M]
  [InnerProductSpace R M] (T : M →L[R] M) (U : Submodule R M) :
  LinearMap.IsProj U T.toLinearMap ↔ LinearMap.IsProj U T :=
by simp_rw [LinearMap.isProj_iff, ContinuousLinearMap.coe_coe]

open LinearMap in
lemma orthogonalProjection_trace {R M : Type*} [RCLike R] [NormedAddCommGroup M] [InnerProductSpace R M]
  [FiniteDimensional R M]
  (U : Submodule R M) :
  (trace R M) (orthogonalProjection' U).toLinearMap = Module.finrank R U :=
by
  refine IsProj.trace ?_
  rw [isProj_coe]
  exact orthogonalProjection'_isProj U

lemma ContinuousLinearMap.eq_comp_orthogonalProjection_ker_ortho
  {𝕜 M₁ M₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup M₁] [InnerProductSpace 𝕜 M₁]
  [NormedAddCommGroup M₂] [InnerProductSpace 𝕜 M₂]
  {T : M₁ →L[𝕜] M₂} [HasOrthogonalProjection (LinearMap.ker T)]
  [HasOrthogonalProjection (LinearMap.range T)]
  [CompleteSpace M₁] [CompleteSpace M₂] :
  T = T ∘L (orthogonalProjection' (LinearMap.ker T)ᗮ)
  ∧
  T = (orthogonalProjection' (LinearMap.range T)) ∘L T :=
by
  simp_rw [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply,
    ext_inner_left_iff (𝕜 := 𝕜) (E := M₂)]
  simp only [orthogonalProjection'_eq, coe_comp', Submodule.coe_subtypeL', Submodule.coe_subtype,
    Function.comp_apply, orthogonalProjection_orthogonal_val, map_sub, LinearMap.map_coe_ker,
    sub_zero, implies_true, true_and,
    orthogonalProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ _)]

theorem orthogonalProjection_of_top {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace ↥(⊤ : Submodule 𝕜 E)] :
    orthogonalProjection' (⊤ : Submodule 𝕜 E) = 1 :=
  by
  ext1
  simp_rw [ContinuousLinearMap.one_apply, orthogonalProjection'_apply]
  rw [orthogonalProjection_eq_self_iff]
  simp only [Submodule.mem_top]

theorem LinearMap.IsProj.top (S M : Type*) [Semiring S] [AddCommMonoid M]
  [Module S M] :
    LinearMap.IsProj (⊤ : Submodule S M) (LinearMap.id (R := S)) :=
⟨fun _ ↦ trivial, fun _ ↦ congrFun rfl⟩

theorem LinearMap.IsProj.codRestrict_of_top {S M : Type*} [Semiring S] [AddCommMonoid M]
  [Module S M] :
    (Submodule.subtype ⊤).comp (LinearMap.IsProj.top S M).codRestrict = LinearMap.id :=
rfl
theorem LinearMap.IsProj.subtype_comp_codRestrict {S M : Type*} [Semiring S] [AddCommMonoid M]
  [Module S M] {U : Submodule S M} {f : M →ₗ[S] M} (hf : LinearMap.IsProj U f) :
    (Submodule.subtype U).comp hf.codRestrict = f :=
rfl

theorem LinearMap.IsProj.codRestrict_eq_dim_iff {S M : Type*}
  [Semiring S] [AddCommMonoid M] [Module S M]
  {f : M →ₗ[S] M} {U : Submodule S M} (hf : LinearMap.IsProj U f) :
    U = (⊤ : Submodule S M)
    ↔ (Submodule.subtype _).comp hf.codRestrict = LinearMap.id :=
by
  rw[LinearMap.IsProj.subtype_comp_codRestrict]
  constructor
  . rintro rfl
    ext
    simp only [id_coe, id_eq, hf.2 _ Submodule.mem_top]
  . rintro rfl
    refine Submodule.eq_top_iff'.mpr ?mpr.a
    intro x
    rw [← id_apply (R := S) x]
    exact hf.map_mem x
