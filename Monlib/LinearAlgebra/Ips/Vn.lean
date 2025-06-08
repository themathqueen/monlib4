/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.InvariantSubmodule
import Monlib.LinearAlgebra.Ips.Basic
import Monlib.LinearAlgebra.Ips.Ips
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Monlib.LinearAlgebra.Ips.MinimalProj
import Monlib.LinearAlgebra.Ips.RankOne

/-!

# A bit on von Neumann algebras

This file contains two simple results about von Neumann algebras.

-/


namespace VonNeumannAlgebra

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma star_commutant_iff {M : VonNeumannAlgebra H} {e : H →L[ℂ] H} :
  star e ∈ M.commutant ↔ e ∈ M.commutant :=
by
  simp only [mem_commutant_iff]
  constructor
  . rintro h g hg
    have : star g ∈ M := by aesop
    specialize h (star g) this
    simp_rw [← star_mul, star_inj] at h
    exact h.symm
  . rintro h g hg
    have : star g ∈ M := by aesop
    specialize h (star g) this
    rw [← star_star g]
    simp_rw [← star_mul, h]

/-- a continuous linear map `e` is in the von Neumann algebra `M`
if and only if `e.ker` and `e.range` are `M'`
(i.e., the commutant of `M` or `M.centralizer`) invariant subspaces -/
theorem elem_idempotent_iff_ker_and_range_invariantUnder_commutant (M : VonNeumannAlgebra H)
    (e : H →L[ℂ] H) (h : IsIdempotentElem e) :
    e ∈ M ↔ ∀ y : H →L[ℂ] H, y ∈ M.commutant → (LinearMap.ker e).InvariantUnder y ∧ (LinearMap.range e).InvariantUnder y :=
  by
  simp_rw [Submodule.invariantUnder_iff, Set.subset_def,
    ContinuousLinearMap.coe_coe, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker,
    LinearMap.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro he y hy
    have : e.comp y = y.comp e :=
      by
      rw [← VonNeumannAlgebra.commutant_commutant M, VonNeumannAlgebra.mem_commutant_iff] at he
      exact (he y hy).symm
    simp_rw [← ContinuousLinearMap.comp_apply, this]
    exact
      ⟨fun x hx => by rw [ContinuousLinearMap.comp_apply, hx, map_zero], fun u ⟨v, hv⟩ => by
        simp_rw [← hv, ← ContinuousLinearMap.comp_apply, ← this, ContinuousLinearMap.comp_apply,
          exists_apply_eq_apply]⟩
  · intro H'
    rw [← VonNeumannAlgebra.commutant_commutant M]
    intro m hm; ext x
    obtain ⟨v, w, hvw, _⟩ :=
      Submodule.existsUnique_add_of_isCompl (IsIdempotentElem.isCompl_range_ker (IsIdempotentElem.clm_to_lm.mp h)) x
    obtain ⟨y, hy⟩ := SetLike.coe_mem w
    -- let hvv := SetLike.coe_mem v
    -- let hvv : H := (@Subtype.val H (fun x ↦ x ∈ ↑(LinearMap.ker ↑e)) v : H)
    -- have hv' : e v = 0 := by
    --   simp only [LinearMap.map_coe_ker]

-- rw [LinearMap.mem_ker] at hv'
    simp_rw [ContinuousLinearMap.coe_coe] at hy
    -- simp only [coe_commutant, Set.instInvolutiveStarSet, Set.mem_union, Set.mem_star] at hm
    simp_rw [Set.mem_union, Set.mem_star, SetLike.mem_coe,
      star_commutant_iff, or_self] at hm
    simp_rw [← hvw, ContinuousLinearMap.mul_apply, map_add, LinearMap.map_coe_ker, map_zero, zero_add]
    obtain ⟨p, hp⟩ := (H' _ hm).2 (e y) (LinearMap.mem_range.mpr ⟨y, rfl⟩)
    -- have := hm e
    . rw [(H' m hm).1 v (LinearMap.map_coe_ker _ v), zero_add, ← hy, ← ContinuousLinearMap.mul_apply e e,
      IsIdempotentElem.eq h, ← hp, ← ContinuousLinearMap.mul_apply e e, IsIdempotentElem.eq h]
    -- . have hm'' := star_commutant_iff.mpr hm
      -- rw [(H' m hm'').1 v hg, zero_add, ← hy, ← ContinuousLinearMap.mul_apply e e,
      -- IsIdempotentElem.eq h,
      -- ← hp, ← ContinuousLinearMap.mul_apply e e, IsIdempotentElem.eq h]

/-- By definition, the bounded linear operators on a Hilbert space `H` form a von Neumann algebra.

  !!(But the note on the definition says that we can't do this because it's a bundled structure?)!! idk? -/
def ofHilbertSpace : VonNeumannAlgebra H
    where
  carrier := Set.univ
  mul_mem' _ _ := Set.mem_univ _
  add_mem' _ _ := Set.mem_univ _
  star_mem' _ := Set.mem_univ _
  algebraMap_mem' _ := Set.mem_univ _
  centralizer_centralizer' := ContinuousLinearMap.centralizer_centralizer

end VonNeumannAlgebra
