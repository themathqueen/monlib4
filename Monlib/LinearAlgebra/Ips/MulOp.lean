/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Opposite
-- import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!

# Some results on the opposite vector space

This file contains the construction of the basis of an opposite space; and the construction of the opposite inner product space.

-/


variable {R H : Type _} [Ring R] [AddCommGroup H] [Module R H] {ι : Type _} [Fintype ι]

noncomputable def Basis.mulOpposite (b : Basis ι R H) : Basis ι R Hᵐᵒᵖ :=
  by
  refine' Basis.mk _ _
  · exact fun i => MulOpposite.op (b i)
  · have := b.linearIndependent
    simp_rw [linearIndependent_iff', ← MulOpposite.op_smul, ← Finset.op_sum,
      MulOpposite.op_eq_zero_iff] at this ⊢
    exact this
  · simp_rw [top_le_iff]
    ext x
    simp_rw [Submodule.mem_top, iff_true, mem_span_range_iff_exists_fun, ← MulOpposite.op_smul,
      ← Finset.op_sum]
    use b.repr (MulOpposite.unop x)
    rw [Basis.sum_repr, MulOpposite.op_unop]

theorem Basis.mulOpposite_apply (b : Basis ι R H) (i : ι) :
    b.mulOpposite i = MulOpposite.op (b i) := by rw [Basis.mulOpposite, Basis.coe_mk]

theorem Basis.mulOpposite_repr_eq (b : Basis ι R H) :
    b.mulOpposite.repr = (MulOpposite.opLinearEquiv R).symm.trans b.repr :=
  by
  simp_rw [Basis.repr_eq_iff', LinearEquiv.trans_apply, MulOpposite.coe_opLinearEquiv_symm,
    Basis.mulOpposite_apply, MulOpposite.unop_op]
  exact Basis.repr_self _

theorem Basis.mulOpposite_repr_apply (b : Basis ι R H) (x : Hᵐᵒᵖ) :
    b.mulOpposite.repr x = b.repr (MulOpposite.unop x) :=
  by
  rw [Basis.mulOpposite_repr_eq]
  rfl

@[instance]
theorem mulOpposite_finiteDimensional {R H : Type _} [DivisionRing R] [AddCommGroup H] [Module R H]
    [FiniteDimensional R H] : FiniteDimensional R Hᵐᵒᵖ :=
  by
  let b := Basis.ofVectorSpace R H
  let bm := b.mulOpposite
  apply FiniteDimensional.of_finite_basis bm
  exact (Basis.ofVectorSpaceIndex R H).toFinite

@[instance]
def MulOpposite.hasInner {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    Inner 𝕜 Hᵐᵒᵖ where inner x y := inner (MulOpposite.unop x) (MulOpposite.unop y)

theorem MulOpposite.inner_eq {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (x y : Hᵐᵒᵖ) :
    (inner x y : 𝕜) = inner (MulOpposite.unop x) (MulOpposite.unop y) :=
  rfl

theorem MulOpposite.inner_eq' {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (x y : H) :
    inner (MulOpposite.op x) (MulOpposite.op y) = (inner x y : 𝕜) :=
  rfl

@[instance, reducible]
def MulOpposite.innerProductSpace {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] : InnerProductSpace 𝕜 Hᵐᵒᵖ
    where
  norm_sq_eq_inner x := by simp only [inner_eq, inner_self_eq_norm_sq, MulOpposite.norm_unop]
  conj_symm x y := by simp only [inner_eq, inner_conj_symm]
  add_left x y z := by simp only [inner, inner_add_left, MulOpposite.unop_add]
  smul_left r x y := by simp only [inner, inner_smul_left, MulOpposite.unop_smul]

theorem Basis.mulOpposite_is_orthonormal_iff {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ι : Type _} [Fintype ι] (b : Basis ι 𝕜 H) :
    Orthonormal 𝕜 b ↔ Orthonormal 𝕜 b.mulOpposite := by
  simp only [Orthonormal, Basis.mulOpposite_apply, MulOpposite.inner_eq', MulOpposite.norm_op]

noncomputable def OrthonormalBasis.mulOpposite {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ι : Type _} [Fintype ι] (b : OrthonormalBasis ι 𝕜 H) :
    OrthonormalBasis ι 𝕜 Hᵐᵒᵖ :=
  by
  refine' Basis.toOrthonormalBasis _ _
  · exact b.toBasis.mulOpposite
  · rw [← Basis.mulOpposite_is_orthonormal_iff]
    exact b.orthonormal

instance MulOpposite.starModule {R H : Type _} [Star R] [SMul R H] [Star H] [StarModule R H] :
    StarModule R Hᵐᵒᵖ
    where star_smul r a := by simp_rw [star, MulOpposite.unop_smul, star_smul, MulOpposite.op_smul]
