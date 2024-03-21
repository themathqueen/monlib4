/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.InvariantSubmodule
import LinearAlgebra.MyIps.Basic
import LinearAlgebra.MyIps.Ips
import Analysis.VonNeumannAlgebra.Basic
import LinearAlgebra.MyIps.MinimalProj
import LinearAlgebra.MyIps.RankOne

#align_import linear_algebra.my_ips.vn

/-!

# A bit on von Neumann algebras

This file contains two simple results about von Neumann algebras.

-/


namespace VonNeumannAlgebra

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- a continuous linear map `e` is in the von Neumann algebra `M`
if and only if `e.ker` and `e.range` are `M'`
(i.e., the commutant of `M` or `M.centralizer`) invariant subspaces -/
theorem has_idempotent_iff_ker_and_range_are_invariantUnder_commutant (M : VonNeumannAlgebra H)
    (e : H →L[ℂ] H) (h : IsIdempotentElem e) :
    e ∈ M ↔ ∀ y : H →L[ℂ] H, y ∈ M.commutant → e.ker.InvariantUnder y ∧ e.range.InvariantUnder y :=
  by
  simp_rw [Submodule.invariantUnder_iff, Set.subset_def, ContinuousLinearMap.toLinearMap_eq_coe,
    ContinuousLinearMap.coe_coe, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker,
    LinearMap.mem_range, ContinuousLinearMap.coe_coe, forall_exists_index, and_imp,
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
  · intro H
    rw [← VonNeumannAlgebra.commutant_commutant M]
    intro m hm; ext x
    have h' : IsIdempotentElem e.to_linear_map :=
      by
      rw [IsIdempotentElem] at h ⊢; ext y
      rw [LinearMap.mul_apply, ContinuousLinearMap.toLinearMap_eq_coe, ContinuousLinearMap.coe_coe,
        ← ContinuousLinearMap.mul_apply, h]
    obtain ⟨v, w, hvw, hunique⟩ :=
      Submodule.existsUnique_add_of_isCompl (LinearMap.IsIdempotent.isCompl_range_ker (↑e) h') x
    obtain ⟨y, hy⟩ := SetLike.coe_mem w
    have hg := linear_map.mem_ker.mp (SetLike.coe_mem v)
    simp_rw [ContinuousLinearMap.toLinearMap_eq_coe, ContinuousLinearMap.coe_coe] at hy hg
    rw [SetLike.mem_coe] at hm
    simp_rw [← hvw, ContinuousLinearMap.mul_apply, map_add, hg, map_zero, zero_add]
    obtain ⟨p, hp⟩ := (H m hm).2 w (SetLike.coe_mem w)
    rw [(H m hm).1 v hg, zero_add, ← hp, ← ContinuousLinearMap.mul_apply e e, IsIdempotentElem.eq h,
      hp, ← hy, ← ContinuousLinearMap.mul_apply e e, IsIdempotentElem.eq h]

/-- By definition, the bounded linear operators on a Hilbert space `H` form a von Neumann algebra.

  !!(But the note on the definition says that we can't do this because it's a bundled structure?)!! idk? -/
def ofHilbertSpace : VonNeumannAlgebra H
    where
  carrier := Set.univ
  hMul_mem' x y hx hy := Set.mem_univ _
  add_mem' x y hx hy := Set.mem_univ _
  star_mem' x hx := Set.mem_univ _
  algebraMap_mem' x := Set.mem_univ _
  centralizer_centralizer' := ContinuousLinearMap.centralizer_centralizer

end VonNeumannAlgebra

