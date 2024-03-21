/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.InnerAut
import LinearAlgebra.MyMatrix.Spectra
import Preq.Equiv

#align_import linear_algebra.blackbox

/-!

# Some stuff on almost-Hermitian matrices

This file contains a blackbox theorem that says that two almost-Hermitian matrices have the same spectrum if and only if they are almost similar. This is a generalization of the fact that two Hermitian matrices have the same spectrum if and only if they are unitarily similar.

-/


open scoped BigOperators

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:570:6: unsupported: specialize @hyp -/
theorem ite_eq_ite_iff {α : Type _} (a b c : α) :
    (∀ {p : Prop} [Decidable p], @ite α p _inst_1 a c = @ite α p _inst_1 b c) ↔ a = b :=
  by
  constructor <;> intro h
  · specialize h True _
    simp_rw [if_true] at h
    exact h
  · simp_rw [h, eq_self_iff_true, forall₂_true_iff]

theorem ite_eq_ite_iff_of_pi {n α : Type _} [DecidableEq n] (a b c : n → α) :
    (∀ i j : n, ite (i = j) (a i) (c i) = ite (i = j) (b i) (c i)) ↔ a = b :=
  by
  rw [← ite_eq_ite_iff _ _ c]
  simp_rw [Function.funext_iff, ite_apply]
  constructor <;> rintro h _ _
  · intro i
    specialize h i i
    simp_rw [eq_self_iff_true, if_true] at h
    rw [h]
  · exact h _

namespace Matrix

open scoped Matrix

variable {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n] [DecidableEq n]

theorem IsAlmostHermitian.spectra_ext [DecidableEq 𝕜] {A B : n → 𝕜}
    (hA : (diagonal A).IsAlmostHermitian) (hB : (diagonal B).IsAlmostHermitian) :
    hA.spectra = hB.spectra ↔ ∃ σ : Equiv.Perm n, ∀ i, A i = B (σ i) := by sorry

theorem IsDiagonal.spectrum_eq_iff_rotation [DecidableEq 𝕜] (A₁ A₂ : n → 𝕜)
    (hA₁ : (diagonal A₁).IsAlmostHermitian) (hA₂ : (diagonal A₂).IsAlmostHermitian) :
    hA₁.spectra = hA₂.spectra ↔
      ∃ U : Equiv.Perm n,
        diagonal A₂ =
          innerAut ⟨(Equiv.toPEquiv U).toMatrix, Equiv.Perm.ToPequiv.toMatrix_mem_unitaryGroup U⟩⁻¹
            (diagonal A₁) :=
  by
  simp_rw [inner_aut_apply', unitary_group.inv_apply, ← Matrix.ext_iff, mul_apply, star_apply, ←
    unitary_group.star_coe_eq_coe_star, unitary_group.inv_apply, star_star, unitary_group.coe_mk,
    PEquiv.equiv_toPEquiv_toMatrix, diagonal_apply, mul_ite, MulZeroClass.mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, one_apply, mul_boole, star_ite, star_one,
    star_zero, boole_mul]
  simp_rw [← ite_and, and_comm', ite_and, ← Equiv.eq_symm_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, (Equiv.injective _).eq_iff]
  rw [is_almost_hermitian.spectra_ext hA₁ hA₂]
  simp_rw [ite_eq_ite_iff_of_pi, Function.funext_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    use σ
    intro i
    rw [hσ, Equiv.apply_symm_apply]
  · rintro ⟨U, hU⟩
    use U
    intro i
    rw [hU, Equiv.symm_apply_apply]

theorem IsAlmostHermitian.spectra_of_innerAut [DecidableEq 𝕜] {A : Matrix n n 𝕜}
    (hA : A.IsAlmostHermitian) (U : unitaryGroup n 𝕜) : (hA.of_innerAut U).spectra = hA.spectra :=
  by sorry

theorem IsAlmostHermitian.innerAut_spectra [DecidableEq 𝕜] {A : Matrix n n 𝕜} (U : unitaryGroup n 𝕜)
    (hA : (innerAut U A).IsAlmostHermitian) :
    hA.spectra = ((isAlmostHermitian_iff_of_innerAut _).mpr hA).spectra :=
  by
  rw [← is_almost_hermitian.spectra_of_inner_aut _ U⁻¹]
  simp_rw [inner_aut_inv_apply_inner_aut_self]

theorem IsAlmostHermitian.spectrum_eq_iff [DecidableEq 𝕜] {A₁ A₂ : Matrix n n 𝕜}
    (hA₁ : A₁.IsAlmostHermitian) (hA₂ : A₂.IsAlmostHermitian) :
    hA₁.spectra = hA₂.spectra ↔ ∃ U : unitaryGroup n 𝕜, A₂ = innerAut U⁻¹ A₁ :=
  by
  constructor
  · rcases hA₁.schur_decomp with ⟨D₁, U₁, h₁⟩
    rcases hA₂.schur_decomp with ⟨D₂, U₂, h₂⟩
    have hA₁' : is_almost_hermitian (inner_aut U₁ (diagonal D₁)) := by rw [h₁] <;> exact hA₁
    have hA₂' : is_almost_hermitian (inner_aut U₂ (diagonal D₂)) := by rw [h₂] <;> exact hA₂
    have h₁' : hA₁.spectra = hA₁'.spectra := by simp_rw [h₁]
    have h₂' : hA₂.spectra = hA₂'.spectra := by simp_rw [h₂]
    rw [h₁', h₂']
    simp_rw [is_almost_hermitian.inner_aut_spectra, is_diagonal.spectrum_eq_iff_rotation]
    rcases hA₁ with ⟨α₁, N₁, hA₁⟩
    rcases hA₂ with ⟨α₂, N₂, hA₂⟩
    simp_rw [← h₁, ← h₂]
    rw [inner_aut_eq_iff] at h₁ h₂
    rintro ⟨U, hU⟩
    simp_rw [hU, inner_aut_apply_inner_aut_inv, inner_aut_eq_iff, inner_aut_apply_inner_aut,
      _root_.mul_inv_rev, inv_inv]
    use U₁ *
          (⟨(Equiv.toPEquiv U).toMatrix, Equiv.Perm.ToPequiv.toMatrix_mem_unitaryGroup _⟩ :
            unitary_group n 𝕜) *
        U₂⁻¹
    simp_rw [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_self, mul_one, inv_mul_cancel_left,
      mul_inv_self, inner_aut_one, LinearMap.one_apply]
  · rintro ⟨U, rfl⟩
    simp_rw [is_almost_hermitian.inner_aut_spectra]

/-- two matrices are _almost similar_ if there exists some
  $0\neq\beta\in\mathbb{C}$ such that $x$ and $\beta y$ are similar -/
def IsAlmostSimilarTo [Fintype n] [DecidableEq n] [IsROrC 𝕜] (x y : Matrix n n 𝕜) : Prop :=
  ∃ (β : 𝕜ˣ) (U : unitaryGroup n 𝕜), (β : 𝕜) • y = innerAut U⁻¹ x

/-- an immediate corollary to `matrix.is_almost_hermitian.spectrum_eq_iff` using
  `matrix.is_almost_similar_to` and `matrix.has_almost_equal_spectra_to` -/
theorem IsAlmostHermitian.hasAlmostEqualSpectraTo_iff_isAlmostSimilarTo [LinearOrder n]
    {x y : Matrix n n ℂ} (hx : x.IsAlmostHermitian) (hy : y.IsAlmostHermitian) :
    hx.HasAlmostEqualSpectraTo hy ↔ x.IsAlmostSimilarTo y := by
  simp_rw [is_almost_hermitian.has_almost_equal_spectra_to, is_almost_hermitian.spectrum_eq_iff,
    Matrix.IsAlmostSimilarTo]

end Matrix

