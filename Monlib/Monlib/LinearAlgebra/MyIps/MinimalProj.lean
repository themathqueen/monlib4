/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyIps.Pos
import LinearAlgebra.MyIps.Ips
import LinearAlgebra.MyIps.Symm
import RepTheory.AutMat
import LinearAlgebra.KroneckerToTensor
import LinearAlgebra.Matrix.Hermitian
import LinearAlgebra.MyIps.RankOne
import LinearAlgebra.MyIps.Basic
import LinearAlgebra.IsProj'
import Analysis.InnerProductSpace.Orthogonal

#align_import linear_algebra.my_ips.minimal_proj

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
  (see `is_idempotent_elem.comp_idempotent_iff` and
   `linear_map.commutes_iff_is_idempotent_elem`)

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


section

variable {R E : Type _} [Ring R] [AddCommGroup E] [Module R E]

open Submodule LinearMap

/-- given an idempotent linear operator $p$, we have
  $x \in \textnormal{range}(p)$ if and only if $p(x) = x$ (for all $x \in E$) -/
theorem IsIdempotentElem.mem_range_iff {p : E →ₗ[R] E} (hp : IsIdempotentElem p) {x : E} :
    x ∈ p.range ↔ p x = x := by
  simp_rw [mem_range]
  constructor
  · rintro ⟨y, hy⟩
    nth_rw 1 [← hy]
    rw [← mul_apply, hp.eq, hy]
  · intro h
    use x
    exact h

variable {U V : Submodule R E} {p q : E →ₗ[R] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)

/-- given idempotent linear operators $p,q$,
  we have $qp = p$ iff $p(E) \subseteq q(E)$ -/
theorem IsIdempotentElem.comp_idempotent_iff : q.comp p = p ↔ map p ⊤ ≤ map q ⊤ := by
  simp_rw [ext_iff, comp_apply, ← IsIdempotentElem.mem_range_iff hq, Submodule.map_top,
    SetLike.le_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]

/-- if $p,q$ are idempotent operators and $pq = p = qp$,
  then $q - p$ is an idempotent operator -/
theorem LinearMap.isIdempotentElem_sub_of (h : p.comp q = p ∧ q.comp p = p) :
    IsIdempotentElem (q - p) := by
  simp_rw [IsIdempotentElem, mul_eq_comp, sub_comp, comp_sub, h.1, h.2, ← mul_eq_comp, hp.eq, hq.eq,
    sub_self, sub_zero]

/-- if $p,q$ are idempotent operators and $q - p$ is also an idempotent
  operator, then $pq = p = qp$ -/
theorem LinearMap.commutes_of_isIdempotentElem {E 𝕜 : Type _} [IsROrC 𝕜] [AddCommGroup E]
    [Module 𝕜 E] {p q : E →ₗ[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : IsIdempotentElem (q - p)) : p.comp q = p ∧ q.comp p = p :=
  by
  simp_rw [IsIdempotentElem, mul_eq_comp, comp_sub, sub_comp, ← mul_eq_comp, hp.eq, hq.eq, ←
    sub_add_eq_sub_sub, sub_right_inj, add_sub] at h
  have h' : (2 : 𝕜) • p = q.comp p + p.comp q :=
    by
    simp_rw [two_smul]
    nth_rw 2 [← h]
    simp_rw [mul_eq_comp, add_sub_cancel'_right, add_comm]
  have H : ((2 : 𝕜) • p).comp q = q.comp (p.comp q) + p.comp q := by
    simp_rw [h', add_comp, comp_assoc, ← mul_eq_comp, hq.eq]
  simp_rw [add_comm, two_smul, add_comp, add_right_inj] at H
  have H' : q.comp ((2 : 𝕜) • p) = q.comp p + q.comp (p.comp q) := by
    simp_rw [h', comp_add, ← comp_assoc, ← mul_eq_comp, hq.eq]
  simp_rw [two_smul, comp_add, add_right_inj] at H'
  have H'' : q.comp p = p.comp q := by
    simp_rw [H']
    exact H.symm
  rw [← H'', and_self_iff, ← smul_right_inj two_ne_zero, h', ← H'', two_smul]
  exact LinearMap.noZeroSMulDivisors
  exact Invertible.ne_zero 2

/-- given idempotent operators $p,q$,
  we have $pq = p = qp$ iff $q - p$ is an idempotent operator -/
theorem LinearMap.commutes_iff_isIdempotentElem {E 𝕜 : Type _} [IsROrC 𝕜] [AddCommGroup E]
    [Module 𝕜 E] {p q : E →ₗ[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p.comp q = p ∧ q.comp p = p ↔ IsIdempotentElem (q - p) :=
  ⟨fun h => LinearMap.isIdempotentElem_sub_of hp hq h, fun h =>
    LinearMap.commutes_of_isIdempotentElem hp hq h⟩

end

open ContinuousLinearMap

variable {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]

local notation "P" => orthogonalProjection

/-- given self-adjoint operators $p,q$,
  we have $pq=p$ iff $qp=p$ -/
theorem self_adjoint_proj_commutes [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E}
    (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) : p.comp q = p ↔ q.comp p = p :=
  by
  have : Function.Injective fun a₁ : E →L[𝕜] E => star a₁ :=
    by
    intro x y h
    simp_rw [← star_eq_adjoint] at h
    exact star_injective h
  constructor <;> intro h <;>
    · apply_fun adjoint
      simp only [adjoint_comp, is_self_adjoint_iff'.mp hpa, is_self_adjoint_iff'.mp hqa, h]
      exact _inst_4

local notation "↥P" => orthogonalProjection'

theorem orthogonalProjection.idempotent [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [CompleteSpace U] : IsIdempotentElem (↥P U) :=
  by
  rw [IsIdempotentElem]
  ext
  simp_rw [mul_apply, orthogonalProjection'_eq, comp_apply, Submodule.subtypeL_apply,
    orthogonalProjection_mem_subspace_eq_self]

def ContinuousLinearMap.IsOrthogonalProjection [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) : Prop :=
  IsIdempotentElem T ∧ T.ker = T.rangeᗮ

/-- given any idempotent operator $T ∈ L(V)$, then `is_compl T.ker T.range`,
in other words, there exists unique $v ∈ \textnormal{ker}(T)$ and $w ∈ \textnormal{range}(T)$ such that $x = v + w$ -/
theorem LinearMap.IsIdempotent.isCompl_range_ker {V R : Type _} [Ring R] [AddCommGroup V]
    [Module R V] (T : V →ₗ[R] V) (h : IsIdempotentElem T) : IsCompl T.ker T.range :=
  by
  constructor
  · rw [disjoint_iff]
    ext
    simp only [Submodule.mem_bot, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range,
      ContinuousLinearMap.toLinearMap_eq_coe, ContinuousLinearMap.coe_coe]
    constructor
    · intro h'
      cases' h'.2 with y hy
      rw [← hy, ← IsIdempotentElem.eq h, LinearMap.mul_apply, hy]
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
    use x - T x;
    rw [LinearMap.mem_ker, map_sub, ← LinearMap.mul_apply, IsIdempotentElem.eq h, sub_self]
    use T x; rw [LinearMap.mem_range] <;> simp only [exists_apply_eq_apply]
    simp only [Submodule.coe_mk, sub_add_cancel]

theorem IsCompl.of_orthogonal_projection [InnerProductSpace 𝕜 E] {T : E →L[𝕜] E}
    (h : T.IsOrthogonalProjection) : IsCompl T.ker T.range :=
  LinearMap.IsIdempotent.isCompl_range_ker _ ((IsIdempotentElem.toLinearMap _).mp h.1)

theorem orthogonalProjection.isOrthogonalProjection [InnerProductSpace ℂ E] {U : Submodule ℂ E}
    [CompleteSpace E] [CompleteSpace U] : (↥P U).IsOrthogonalProjection :=
  ⟨(orthogonalProjection.idempotent U : IsIdempotentElem (U.subtypeL.comp (P U) : E →L[ℂ] E)),
    (IsIdempotent.isSelfAdjoint_iff_ker_is_ortho_to_range (U.subtypeL.comp (P U) : E →L[ℂ] E)
          (orthogonalProjection.idempotent U :
            IsIdempotentElem (U.subtypeL.comp (P U) : E →L[ℂ] E))).mp
      (orthogonalProjection_isSelfAdjoint U)⟩

theorem IsIdempotentElem.clm_to_lm [InnerProductSpace 𝕜 E] {T : E →L[𝕜] E} :
    IsIdempotentElem T ↔ IsIdempotentElem (T : E →ₗ[𝕜] E) :=
  by
  simp_rw [IsIdempotentElem, LinearMap.mul_eq_comp, ← coe_comp, coe_inj]
  rfl

/-- $P_V P_U = P_U$ if and only if $P_V - P_U$ is an orthogonal projection -/
theorem sub_of_isOrthogonalProjection [InnerProductSpace ℂ E] [CompleteSpace E]
    {U V : Submodule ℂ E} [CompleteSpace U] [CompleteSpace V] :
    (↥P V).comp (↥P U) = ↥P U ↔ (↥P V - ↥P U).IsOrthogonalProjection :=
  by
  let p := ↥P U
  let q := ↥P V
  have pp : p = U.subtypeL.comp (P U) := rfl
  have qq : q = V.subtypeL.comp (P V) := rfl
  have hp : IsIdempotentElem p := orthogonalProjection.idempotent U
  have hq : IsIdempotentElem q := orthogonalProjection.idempotent V
  have hpa := orthogonalProjection_isSelfAdjoint U
  have hqa := orthogonalProjection_isSelfAdjoint V
  have h2 := self_adjoint_proj_commutes hpa hqa
  simp_rw [orthogonalProjection', ← pp, ← qq] at *
  constructor
  · intro h
    have h_and : (p : E →ₗ[ℂ] E) ∘ₗ (q : E →ₗ[ℂ] E) = p ∧ (q : E →ₗ[ℂ] E) ∘ₗ (p : E →ₗ[ℂ] E) = p :=
      by simp_rw [← coe_comp, coe_inj, h2, and_self_iff, h]
    rw [LinearMap.commutes_iff_isIdempotentElem (is_idempotent_elem.clm_to_lm.mp hp)
        (is_idempotent_elem.clm_to_lm.mp hq),
      ← coe_sub, ← IsIdempotentElem.clm_to_lm] at h_and
    refine' ⟨h_and, _⟩
    rw [← is_idempotent.is_self_adjoint_iff_ker_is_ortho_to_range _ h_and]
    exact IsSelfAdjoint.sub hqa hpa
  · rintro ⟨h1, h3⟩
    simp_rw [IsIdempotentElem.clm_to_lm, coe_sub, ←
      LinearMap.commutes_iff_isIdempotentElem (is_idempotent_elem.clm_to_lm.mp hp)
        (is_idempotent_elem.clm_to_lm.mp hq),
      ← coe_comp, coe_inj] at h1
    exact h1.2

section

/-- instance for `≤` on linear maps -/
instance LinearMap.IsSymmetric.hasLe {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : LE (E →ₗ[𝕜] E) :=
  by
  refine' { le := _ }
  intro u v
  exact (v - u : E →ₗ[𝕜] E).IsPositive

local notation "sa" g => {x : g →ₗ[ℂ] g | x.IsSymmetric}

local notation "SA" g => {x : g →L[ℂ] g | IsSelfAdjoint x}

local notation "L(" x "," y ")" => x →L[y] x

local notation "l(" x "," y ")" => x →ₗ[y] x

instance {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : PartialOrder (sa E) :=
  by
  fconstructor
  · intro u v
    exact (v - u : E →ₗ[ℂ] E).IsPositive
  · intro a
    simp_rw [sub_self]
    constructor
    · intro u v
      simp_rw [LinearMap.zero_apply, inner_zero_left, inner_zero_right]
    · intro x
      simp_rw [LinearMap.zero_apply, inner_zero_right, IsROrC.zero_re']
  · simp_rw [LE.le]
    intro a b c hab hbc
    rw [← add_zero ↑c, ← sub_self ↑b, ← add_sub_assoc, add_sub_right_comm, add_sub_assoc]
    exact LinearMap.IsPositive.add hbc hab
  · simp_rw [LE.le]
    rintro a b hba hab
    simp_rw [subtype.coe_inj.symm, LinearMap.ext_iff_inner_map]
    intro x
    have hba2 := hba.2 x
    rw [← neg_le_neg_iff, ← map_neg, ← inner_neg_right, ← LinearMap.neg_apply, neg_sub, neg_zero] at
      hba2
    rw [← sub_eq_zero, ← inner_sub_left, ← LinearMap.sub_apply, hab.1, ←
      ((LinearMap.complex_isPositive _).mp hab _).1, le_antisymm hba2 (hab.2 x),
      Complex.ofReal_zero]

/-- `p ≤ q` means `q - p` is positive -/
theorem LinearMap.IsPositive.hasLe {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {p q : sa E} : p ≤ q ↔ (q - p : l(E,ℂ)).IsPositive := by rfl

noncomputable instance IsSymmetric.hasZero {E : Type _} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : Zero ↥{x : E →ₗ[ℂ] E | x.IsSymmetric} :=
  by
  fconstructor
  fconstructor
  exact 0
  simp_rw [Set.mem_setOf_eq, LinearMap.IsSymmetric, LinearMap.zero_apply, inner_zero_left,
    inner_zero_right, forall_const]

/-- saying `p` is positive is the same as saying `0 ≤ p` -/
theorem LinearMap.IsPositive.is_nonneg {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {p : l(E,𝕜)} : p.IsPositive ↔ 0 ≤ p :=
  by
  nth_rw 1 [← sub_zero p]
  rfl

end

section

/-- instance for `≤` on bounded linear maps -/
instance {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] : LE (E →L[𝕜] E) :=
  by
  refine' { le := _ }
  intro u v
  exact is_positive (v - u)

/-- when `a,b` are self-adjoint operators, then
  if `a ≤ b` and `b ≤ a`, then `a = b` -/
theorem IsSelfAdjoint.HasLe.le_antisymm {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {a b : E →L[𝕜] E} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  by
  simp_rw [LE.le] at *
  rw [ContinuousLinearMap.IsSelfAdjoint.ext_iff_inner_map ha hb]
  intro x
  have hba2 := hba.2 x
  rw [← neg_le_neg_iff, re_apply_inner_self_apply, ← map_neg, ← inner_neg_left, ← neg_apply,
    neg_sub, neg_zero] at hba2
  symm
  rw [← sub_eq_zero, ← inner_sub_left, ← sub_apply, ← IsSelfAdjoint.inner_re_eq hab.1 x,
    IsROrC.ofReal_eq_zero, le_antisymm (hab.2 x) hba2]
  rfl

/-- we always have `a ≤ a` -/
@[refl, simp]
theorem ContinuousLinearMap.hasLe.le_refl {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {a : E →L[𝕜] E} : a ≤ a := by
  simp_rw [LE.le, sub_self, is_positive_zero]

/-- when `a,b` are self-adjoint operators, then
  if `a ≤ b` and `b ≤ c`, then `a ≤ c` -/
@[simp]
theorem IsSelfAdjoint.HasLe.le_trans {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {a b c : E →L[𝕜] E} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hc : IsSelfAdjoint c) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  by
  simp_rw [LE.le] at *
  rw [← add_zero c, ← sub_self b, ← add_sub_assoc, add_sub_right_comm, add_sub_assoc]
  exact is_positive.add hbc hab

/-- `p ≤ q` means `q - p` is positive -/
@[refl, simp]
theorem ContinuousLinearMap.IsPositive.hasLe {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E} : p ≤ q ↔ (q - p).IsPositive := by
  rfl

/-- saying `p` is positive is the same as saying `0 ≤ p` -/
@[refl, simp]
theorem ContinuousLinearMap.IsPositive.is_nonneg {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {p : E →L[𝕜] E} : p.IsPositive ↔ 0 ≤ p :=
  by
  nth_rw 1 [← sub_zero p]
  rfl

end

/-- a self-adjoint idempotent operator is positive -/
theorem SelfAdjointAndIdempotent.is_positive {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {p : E →L[𝕜] E} (hp : IsIdempotentElem p)
    (hpa : IsSelfAdjoint p) : 0 ≤ p :=
  by
  rw [← ContinuousLinearMap.IsPositive.is_nonneg]
  refine' ⟨hpa, _⟩
  rw [← hp.eq]
  simp_rw [re_apply_inner_self_apply, mul_apply]
  intro x
  simp_rw [← adjoint_inner_right _ _ x, is_self_adjoint_iff'.mp hpa]
  exact inner_self_nonneg

/-- an idempotent is positive if and only if it is self-adjoint -/
theorem IsIdempotentElem.is_positive_iff_self_adjoint [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {p : E →L[𝕜] E} (hp : IsIdempotentElem p) : 0 ≤ p ↔ IsSelfAdjoint p :=
  ⟨fun h => (ContinuousLinearMap.IsPositive.is_nonneg.mpr h).1, fun h =>
    SelfAdjointAndIdempotent.is_positive hp h⟩

theorem IsIdempotentElem.self_adjoint_is_positive_isOrthogonalProjection_tFAE {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {p : E →L[ℂ] E}
    (hp : IsIdempotentElem p) : TFAE [IsSelfAdjoint p, p.IsOrthogonalProjection, 0 ≤ p] :=
  by
  tfae_have 3 ↔ 1
  · exact hp.is_positive_iff_self_adjoint
  tfae_have 2 → 1
  · intro h
    rw [ContinuousLinearMap.IsOrthogonalProjection, ←
      is_idempotent.is_self_adjoint_iff_ker_is_ortho_to_range _ hp] at h
    exact h.2
  tfae_have 1 → 2
  · intro h
    rw [is_idempotent.is_self_adjoint_iff_ker_is_ortho_to_range _ hp] at h
    exact ⟨hp, h⟩
  tfae_finish

/-- orthogonal projections are obviously positive -/
theorem orthogonalProjection.is_positive [InnerProductSpace ℂ E] {U : Submodule ℂ E}
    [CompleteSpace E] [CompleteSpace U] : 0 ≤ U.subtypeL.comp (P U) :=
  SelfAdjointAndIdempotent.is_positive (orthogonalProjection.idempotent U)
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
  SelfAdjointAndIdempotent.sub_is_positive_of (orthogonalProjection.idempotent U)
    (orthogonalProjection.idempotent V) (orthogonalProjection_isSelfAdjoint U)
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
  have hp : IsIdempotentElem p := orthogonalProjection.idempotent U
  have hq : IsIdempotentElem q := orthogonalProjection.idempotent V
  have hpa := orthogonalProjection_isSelfAdjoint U
  have hqa := orthogonalProjection_isSelfAdjoint V
  have h2 := self_adjoint_proj_commutes hpa hqa
  exact
    coe_inj.mp
      (LinearMap.commutes_of_isIdempotentElem (is_idempotent_elem.clm_to_lm.mp hp)
          (is_idempotent_elem.clm_to_lm.mp hq) (is_idempotent_elem.clm_to_lm.mp h)).2

/-- copy of `linear_map.is_positive_iff_exists_adjoint_mul_self` -/
theorem ContinuousLinearMap.isPositive_iff_exists_adjoint_hMul_self [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {n : ℕ} [FiniteDimensional 𝕜 E] (hn : FiniteDimensional.finrank 𝕜 E = n)
    (T : E →L[𝕜] E) : T.IsPositive ↔ ∃ S : E →L[𝕜] E, T = S.adjoint * S :=
  by
  rw [← is_positive.to_linear_map, LinearMap.isPositive_iff_exists_adjoint_hMul_self _ hn,
    to_linear_map_eq_coe]
  constructor <;> rintro ⟨S, hS⟩ <;> use S
  · exact map_continuous S
  · simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ←
      ContinuousLinearMap.toLinearMap_eq_coe, ← LinearMap.ext_iff] at *
    exact hS
  · rw [hS, mul_def, coe_comp]
    rfl

open IsROrC

/-- in a finite-dimensional complex Hilbert space `E`,
  if `p,q` are self-adjoint operators, then
  `p ≤ q` iff `∀ x ∈ E : ⟪x, p x⟫ ≤ ⟪x, q x⟫` -/
theorem ContinuousLinearMap.is_positive_le_iff_inner {n : ℕ} [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (hn : FiniteDimensional.finrank ℂ E = n) {p q : E →L[ℂ] E}
    (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) :
    p ≤ q ↔ ∀ x : E, re ⟪x, p x⟫_ℂ ≤ re ⟪x, q x⟫_ℂ :=
  by
  rw [ContinuousLinearMap.IsPositive.hasLe]
  constructor
  · intro h x
    obtain ⟨S, hS⟩ := (ContinuousLinearMap.isPositive_iff_exists_adjoint_hMul_self hn _).mp h
    rw [← sub_nonneg, ← map_sub, ← inner_sub_right, ← sub_apply, hS, mul_apply, adjoint_inner_right]
    exact inner_self_nonneg
  · intro h
    refine' ⟨IsSelfAdjoint.sub hqa hpa, fun x => _⟩
    simp_rw [re_apply_inner_self_apply, sub_apply, inner_sub_left, map_sub, sub_nonneg]
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
    is_self_adjoint_iff'.mp hpa, is_self_adjoint_iff'.mp hqa, inner_self_eq_norm_sq, sq_le_sq,
    abs_norm, ← mul_apply, hp.eq, hq.eq, iff_self_iff]

@[simp]
theorem IsPositive.HasLe.sub [InnerProductSpace 𝕜 E] [CompleteSpace E] {p q : E →L[𝕜] E} :
    p ≤ q ↔ 0 ≤ q - p := by rfl

theorem self_adjoint_and_idempotent_is_positive_iff_commutes {n : ℕ} [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (hn : FiniteDimensional.finrank ℂ E = n) {p q : E →L[ℂ] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpa : IsSelfAdjoint p)
    (hqa : IsSelfAdjoint q) : p ≤ q ↔ q.comp p = p :=
  by
  rw [← self_adjoint_proj_commutes hpa hqa, IsPositive.HasLe.sub]
  refine' ⟨fun h => _, fun h => SelfAdjointAndIdempotent.sub_is_positive_of hp hq hpa hqa h⟩
  rw [← ContinuousLinearMap.IsPositive.is_nonneg, ← ContinuousLinearMap.IsPositive.hasLe,
    ContinuousLinearMap.is_positive_le_iff_inner hn hpa hqa] at h
  symm
  rw [← sub_eq_zero]
  nth_rw 1 [← mul_one p]
  simp_rw [mul_def, ← comp_sub, ← ContinuousLinearMap.inner_map_self_eq_zero, comp_apply, sub_apply,
    one_apply]
  intro x
  specialize h ((1 - q) x)
  simp_rw [sub_apply, map_sub, ← mul_apply, mul_one, hq.eq, sub_self, inner_zero_right, one_apply,
    mul_apply, ← map_sub, zero_re'] at h
  rw [← hp.eq, mul_apply, ← adjoint_inner_left, is_self_adjoint_iff'.mp hpa, inner_self_nonpos] at h
  rw [h, inner_zero_left]

/-- in a complex-finite-dimensional Hilbert space `E`, we have
  `Pᵤ ≤ Pᵤ` iff `PᵥPᵤ = Pᵤ` -/
theorem orthogonal_projection_is_le_iff_commutes {n : ℕ} [InnerProductSpace ℂ E]
    {U V : Submodule ℂ E} [CompleteSpace U] [CompleteSpace V] [FiniteDimensional ℂ E]
    (hn : FiniteDimensional.finrank ℂ E = n) : ↥P U ≤ ↥P V ↔ (↥P V).comp (↥P U) = ↥P U :=
  self_adjoint_and_idempotent_is_positive_iff_commutes hn (orthogonalProjection.idempotent U)
    (orthogonalProjection.idempotent V) (orthogonalProjection_isSelfAdjoint U)
    (orthogonalProjection_isSelfAdjoint V)

theorem orthogonalProjection.is_le_iff_subset {n : ℕ} [InnerProductSpace ℂ E] {U V : Submodule ℂ E}
    [CompleteSpace U] [CompleteSpace V] [FiniteDimensional ℂ E]
    (hn : FiniteDimensional.finrank ℂ E = n) : ↥P U ≤ ↥P V ↔ U ≤ V := by
  simp_rw [orthogonal_projection_is_le_iff_commutes hn, ← coe_inj, coe_comp,
    IsIdempotentElem.comp_idempotent_iff
      (is_idempotent_elem.clm_to_lm.mp (orthogonalProjection.idempotent V)),
    Submodule.map_top, ← to_linear_map_eq_coe, range_to_linear_map, orthogonalProjection.range,
    iff_self_iff]

theorem Submodule.map_to_linearMap [Module 𝕜 E] {p : E →L[𝕜] E} {U : Submodule 𝕜 E} :
    Submodule.map (p : E →ₗ[𝕜] E) U = Submodule.map p U :=
  rfl

/-- given self-adjoint idempotent operators `p,q` we have,
  `p(E) ⊆ q(E)` iff `q - p` is an idempotent operator -/
theorem ContinuousLinearMap.image_subset_iff_sub_of_is_idempotent [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {p q : E →L[𝕜] E} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hpa : IsSelfAdjoint p) (hqa : IsSelfAdjoint q) :
    Submodule.map p ⊤ ≤ Submodule.map q ⊤ ↔ IsIdempotentElem (q - p) := by
  simp_rw [IsIdempotentElem.clm_to_lm, coe_sub, ←
    LinearMap.commutes_iff_isIdempotentElem (is_idempotent_elem.clm_to_lm.mp hp)
      (is_idempotent_elem.clm_to_lm.mp hq),
    ← coe_comp, coe_inj, self_adjoint_proj_commutes hpa hqa, and_self_iff, ← coe_inj, coe_comp,
    IsIdempotentElem.comp_idempotent_iff (is_idempotent_elem.clm_to_lm.mp hq),
    Submodule.map_to_linearMap, iff_self_iff]

section MinProj

/-- definition of a map being a minimal projection -/
def ContinuousLinearMap.IsMinimalProjection [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (x : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  IsSelfAdjoint x ∧ FiniteDimensional.finrank 𝕜 U = 1 ∧ LinearMap.IsProj U x

/-- definition of orthogonal projection being minimal
  i.e., when the dimension of its space equals one -/
def orthogonalProjection.IsMinimalProjection [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [CompleteSpace U] : Prop :=
  FiniteDimensional.finrank 𝕜 U = 1

/-- given self-adjoint operators `p,q` we have
  `p = q` iff `p ≤ q` and `q ≤ p` -/
@[simp]
theorem IsSelfAdjoint.HasLe.le_antisymm_iff [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {p q : E →L[𝕜] E} (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) : p = q ↔ p ≤ q ∧ q ≤ p :=
  by
  refine' ⟨fun h => _, fun h => IsSelfAdjoint.HasLe.le_antisymm hp hq h.1 h.2⟩
  rw [h, and_self_iff]

open FiniteDimensional

/-- when a submodule `U` has dimension `1`, then
  for any submodule `V`, we have `V ≤ U` if and only if `V = U` or `V = 0` -/
theorem Submodule.le_finrank_one [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (U V : Submodule 𝕜 E) (hU : finrank 𝕜 U = 1) : V ≤ U ↔ V = U ∨ V = 0 :=
  by
  simp_rw [Submodule.zero_eq_bot]
  constructor
  · intro h
    have : finrank 𝕜 V ≤ 1 := by
      rw [← hU]
      apply Submodule.finrank_le_finrank_of_le h
    have : finrank 𝕜 V = 0 ∨ finrank 𝕜 V = 1 := order.le_succ_bot_iff.mp this
    cases this
    · simp only [Submodule.finrank_eq_zero] at this_1
      right
      exact this_1
    · left
      apply eq_of_le_of_finrank_eq h
      simp_rw [this_1, hU]
  · intro h
    rcases h with ⟨rfl, rfl⟩
    · exact le_refl U
    · rw [h]
      exact bot_le

/-- for orthogonal projections `Pᵤ,Pᵥ`,
  if `Pᵤ` is a minimal orthogonal projection, then
  for any `Pᵥ` if `Pᵥ ≤ Pᵤ` and `Pᵥ ≠ 0`, then `Pᵥ = Pᵤ` -/
theorem orthogonalProjection.isMinimalProjection_of {n : ℕ} [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (hn : finrank ℂ E = n) (U W : Submodule ℂ E)
    (hU : orthogonalProjection.IsMinimalProjection U) (hW : ↥P W ≤ ↥P U) (h : ↥P W ≠ 0) :
    ↥P W = ↥P U :=
  by
  simp_rw [orthogonalProjection'_eq,
    IsSelfAdjoint.HasLe.le_antisymm_iff (orthogonalProjection_isSelfAdjoint W)
      (orthogonalProjection_isSelfAdjoint U),
    ← orthogonalProjection'_eq]
  refine' ⟨hW, _⟩
  rw [orthogonalProjection.is_le_iff_subset hn] at hW ⊢
  have := Submodule.finrank_le_finrank_of_le hW
  simp_rw [orthogonalProjection.IsMinimalProjection] at hU
  rw [Submodule.le_finrank_one U W hU] at hW
  cases' hW with hW1 hW2
  · simp_rw [hW1, le_refl]
  · simp_rw [hW2, Submodule.zero_eq_bot, orthogonalProjection'_eq, orthogonalProjection_bot,
      comp_zero] at h
    contradiction

/-- any rank one operator given by a norm one vector is a minimal projection -/
theorem rankOne.isMinimalProjection [InnerProductSpace ℂ E] [CompleteSpace E] (x : E)
    (h : ‖x‖ = 1) : (rankOne x x).IsMinimalProjection (Submodule.span ℂ {x}) :=
  by
  refine' ⟨rankOne.isSelfAdjoint x, _⟩
  simp_rw [finrank_eq_one_iff']
  constructor
  · use⟨x, Submodule.mem_span_singleton_self x⟩
    simp_rw [Ne.def, Submodule.mk_eq_zero, SetLike.mk_smul_mk]
    refine' ⟨norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero), fun w => _⟩
    cases' submodule.mem_span_singleton.mp (SetLike.coe_mem w) with r hr
    use r
    simp_rw [hr, SetLike.eta]
  · apply LinearMap.IsProj.mk
    simp_rw [Submodule.mem_span_singleton, rankOne_apply, exists_apply_eq_apply, forall_const]
    simp_rw [Submodule.mem_span_singleton, rankOne_apply, forall_exists_index,
      forall_apply_eq_imp_iff, inner_smul_right, inner_self_eq_norm_sq_to_K, h, Complex.ofReal_one,
      one_pow, mul_one, eq_self_iff_true, forall_const]

/-- if `x ∈ E` then we can normalize this (i.e., there exists `y ∈ E`
  such that `∥y∥ = 1` where `x = r • y` for some `r ∈ ℝ`) unless `x = 0` -/
theorem normalize_op [InnerProductSpace ℂ E] (x : E) :
    (∃ (y : E) (r : ℝ), ‖y‖ = 1 ∧ x = (r : ℂ) • y) ∨ x = 0 :=
  by
  by_cases A : x = 0
  · right
    exact A
  · have B : ‖x‖ ≠ 0 := by
      simp only [Ne.def, norm_eq_zero]
      exact A
    use(1 / ‖x‖) • x
    use‖x‖
    constructor
    · simp_rw [norm_smul, one_div, norm_inv, norm_norm, mul_comm, mul_inv_cancel B]
    · simp_rw [one_div, Complex.coe_smul, smul_inv_smul₀ B]

/-- given any non-zero `x ∈ E`, we have
  `1 / ‖x‖ ^ 2 • |x⟩⟨x|` is a minimal projection -/
theorem rankOne.isMinimalProjection' [InnerProductSpace ℂ E] [CompleteSpace E] (x : E) (h : x ≠ 0) :
    ((1 / ‖x‖ ^ 2) • rankOne x x).IsMinimalProjection (Submodule.span ℂ {x}) :=
  by
  rcases normalize_op x with ⟨y, r, ⟨hy, hx⟩⟩
  · have : r ^ 2 ≠ 0 := by
      intro d
      rw [pow_eq_zero_iff two_pos] at d
      rw [d, Complex.coe_smul, zero_smul] at hx
      contradiction
      exact IsRightCancelMulZero.to_noZeroDivisors ℝ
    simp_rw [hx, Complex.coe_smul, one_div, ← Complex.coe_smul, rankOne.apply_smul,
      rankOne.smul_real_apply, norm_smul, mul_pow, Complex.norm_real, mul_inv, smul_smul, hy,
      one_pow, inv_one, mul_one, Real.norm_eq_abs, ← abs_pow, pow_two, abs_mul_self, ← pow_two,
      Complex.ofReal_inv, Complex.ofReal_pow, Complex.coe_smul]
    norm_cast
    rw [inv_mul_cancel this, one_smul]
    have : Submodule.span ℂ {↑r • y} = Submodule.span ℂ {y} :=
      by
      rw [Submodule.span_singleton_smul_eq _]
      refine' Ne.isUnit _
      exact coeToLift
      rw [Ne.def]
      rw [← pow_eq_zero_iff two_pos]
      norm_cast
      exact this
      exact Lex.noZeroDivisors
    rw [← Complex.coe_smul, this]
    exact rankOne.isMinimalProjection y hy
  · contradiction

/-- a linear operator is an orthogonal projection onto a submodule, if and only if
  it is self-adjoint and idempotent;
  so it always suffices to say `p = p⋆ = p²` -/
theorem orthogonal_projection_iff [InnerProductSpace 𝕜 E] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    {p : E →L[𝕜] E} : (∃ U : Submodule 𝕜 E, ↥P U = p) ↔ IsSelfAdjoint p ∧ IsIdempotentElem p :=
  by
  constructor
  · rintro ⟨U, hp⟩
    rw [← hp]
    exact ⟨orthogonalProjection_isSelfAdjoint _, orthogonalProjection.idempotent _⟩
  · rintro ⟨h1, h2⟩
    simp_rw [IsIdempotentElem, mul_def, ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe,
      coe_comp, ← LinearMap.ext_iff] at h2
    rcases(LinearMap.isProj_iff_idempotent _).mpr h2 with ⟨W, hp⟩
    let p' := isProj' hp
    have hp' : p' = isProj' hp := rfl
    simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ← isProj'_apply hp,
      orthogonalProjection'_eq_linear_proj', ← hp']
    rw [← LinearMap.linearProjOfIsCompl_of_proj p' (isProj'_eq hp)]
    use W
    intro x
    simp_rw [LinearMap.coe_comp, Submodule.coeSubtype, SetLike.coe_eq_coe]
    suffices p'.ker = Wᗮ by simp_rw [this]
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

/-- a linear operator is an orthogonal projection onto a submodule, if and only if
  it is a self-adjoint linear projection onto the submodule;
  also see `orthogonal_projection_iff` -/
theorem orthogonal_projection_iff' [InnerProductSpace 𝕜 E] [CompleteSpace E] [FiniteDimensional 𝕜 E]
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
    have : p.comp p = p :=
      by
      simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.coe_comp, ← LinearMap.ext_iff, ← LinearMap.isProj_iff_idempotent]
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
    simp_rw [LinearMap.coe_comp, Submodule.coeSubtype, SetLike.coe_eq_coe]
    intro x
    suffices p'.ker = Uᗮ by simp_rw [this]
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
        ContinuousLinearMap.comp_apply, this, h' _ (LinearMap.IsProj.map_mem h2 _)]

theorem orthogonalProjection.isMinimalProjection_to_clm [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E)
    [CompleteSpace E] [FiniteDimensional 𝕜 E] :
    (↥P U).IsMinimalProjection U ↔ orthogonalProjection.IsMinimalProjection U :=
  by
  refine' ⟨fun h => h.2.1, fun h => _⟩
  rw [ContinuousLinearMap.IsMinimalProjection, and_left_comm, ← orthogonal_projection_iff' U]
  refine' ⟨h, _⟩
  rfl

theorem Submodule.isOrtho_iff_inner_eq' {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {U W : Submodule 𝕜 E} :
    U ⟂ W ↔ ∀ (u : ↥U) (w : ↥W), (inner (u : E) (w : E) : 𝕜) = 0 :=
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
    [InnerProductSpace 𝕜 E] (U W : Submodule 𝕜 E) [CompleteSpace U] [CompleteSpace W] :
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
    rw [← orthogonal_projection_eq_self_iff.mpr (SetLike.coe_mem x), ←
      orthogonal_projection_eq_self_iff.mpr (SetLike.coe_mem y),
      inner_orthogonalProjection_left_eq_right, ← orthogonalProjection'_apply, ←
      orthogonalProjection'_apply, ← ContinuousLinearMap.comp_apply, h,
      ContinuousLinearMap.zero_apply, inner_zero_right]

--
theorem orthogonalProjection.orthogonal_complement_eq [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [CompleteSpace ↥U] : ↥P Uᗮ = 1 - ↥P U :=
  by
  have : 1 = id 𝕜 E := rfl
  simp_rw [this, id_eq_sum_orthogonalProjection_self_orthogonalComplement U,
    orthogonalProjection'_eq, add_sub_cancel']

example {n : ℕ} [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {U W : Submodule ℂ E}
    (h : finrank ℂ E = n) : (↥P U).comp (↥P W) = 0 ↔ ↥P U + ↥P W ≤ 1 := by
  simp_rw [← Submodule.is_pairwise_orthogonal_iff_orthogonal_projection_comp_eq_zero,
    Submodule.isOrtho_iff_le, ← orthogonalProjection.is_le_iff_subset h,
    orthogonalProjection.orthogonal_complement_eq, add_comm (↥P U) (↥P W), LE.le,
    sub_add_eq_sub_sub, iff_self_iff]

end MinProj

