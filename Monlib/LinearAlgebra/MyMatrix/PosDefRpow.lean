/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyMatrix.PosEqLinearMapIsPositive
import LinearAlgebra.InnerAut

#align_import linear_algebra.my_matrix.pos_def_rpow

/-!
 # The real-power of a positive definite matrix

 This file defines the real-power of a positive definite matrix. In particular, given a positive definite matrix `x` and real number `r`, we get `pos_def.rpow` as the matrix `eigenvector_matrix * (coe ∘ diagonal (eigenvalues ^ r)) * eigenvector_matrix⁻¹`.

 It also proves some basic obvious properties of `pos_def.rpow` such as `pos_def.rpow_mul_rpow` and `pos_def.rpow_zero`.
-/


namespace Matrix

variable {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix BigOperators

noncomputable def PosDef.rpow [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
    Matrix n n 𝕜 :=
  innerAut ⟨hQ.1.eigenvectorMatrix, hQ.1.eigenvectorMatrix_mem_unitaryGroup⟩
    (coe ∘ diagonal (hQ.1.Eigenvalues ^ r))

theorem PosDef.rpow_hMul_rpow [DecidableEq 𝕜] (r₁ r₂ : ℝ) {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow r₁ ⬝ hQ.rpow r₂ = hQ.rpow (r₁ + r₂) :=
  by
  simp_rw [Matrix.PosDef.rpow, ← inner_aut.map_mul]
  have :
    (coe ∘ diagonal (hQ.1.Eigenvalues ^ r₁) : Matrix n n 𝕜) ⬝
        (coe ∘ diagonal (hQ.1.Eigenvalues ^ r₂) : Matrix n n 𝕜) =
      (coe ∘ (diagonal (hQ.1.Eigenvalues ^ r₁) ⬝ diagonal (hQ.1.Eigenvalues ^ r₂)) :
        Matrix n n 𝕜) :=
    by
    ext1; ext1; simp_rw [mul_apply, Function.comp_apply, diagonal_mul_diagonal, diagonal]
    have :
      ∀ (i j : n) (v : n → ℝ),
        (↑(of (fun i j : n => ite (i = j) (v i) 0) i : n → ℝ) : n → 𝕜) j =
          ↑(of (fun i j : n => ite (i = j) (v i) 0) i j) :=
      fun _ _ _ => rfl
    simp_rw [this, of_apply, ite_cast, IsROrC.ofReal_zero, mul_ite, MulZeroClass.mul_zero, ite_mul,
      MulZeroClass.zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← IsROrC.ofReal_mul]
    by_cases x = x_1
    · simp_rw [h]
    · simp_rw [h, if_false]
  simp_rw [this, diagonal_mul_diagonal, Pi.pow_apply, ← Real.rpow_add (hQ.pos_eigenvalues _), ←
    Pi.pow_apply]

theorem PosDef.rpow_one_eq_self [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow 1 = Q := by
  simp_rw [pos_def.rpow]
  nth_rw_rhs 1 [hQ.1.spectral_theorem']
  congr
  simp_rw [coe_diagonal_eq_diagonal_coe]
  congr
  ext1
  rw [Pi.pow_apply, Real.rpow_one]

theorem PosDef.rpow_neg_one_eq_inv_self [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow (-1) = Q⁻¹ := by
  simp_rw [Matrix.PosDef.rpow]
  nth_rw_rhs 1 [hQ.1.spectral_theorem']
  simp_rw [← coe_diagonal_eq_diagonal_coe, inner_aut.map_inv]
  have :
    (diagonal (coe ∘ hQ.1.Eigenvalues) : Matrix n n 𝕜)⁻¹ = diagonal (coe ∘ hQ.1.Eigenvalues)⁻¹ :=
    by
    apply inv_eq_left_inv
    simp_rw [diagonal_mul_diagonal, Pi.inv_apply, Function.comp_apply, ← IsROrC.ofReal_inv, ←
      IsROrC.ofReal_mul, inv_mul_cancel (NormNum.ne_zero_of_pos _ (hQ.pos_eigenvalues _)),
      IsROrC.ofReal_one, diagonal_one]
  simp_rw [this]
  congr
  ext1
  simp_rw [Pi.inv_apply, Function.comp_apply, Pi.pow_apply, Real.rpow_neg_one, IsROrC.ofReal_inv]

theorem PosDef.rpow_zero [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) : hQ.rpow 0 = 1 :=
  by
  simp_rw [Matrix.PosDef.rpow, Pi.pow_def, Real.rpow_zero, diagonal_one]
  have : (coe ∘ (1 : Matrix n n ℝ) : Matrix n n 𝕜) = (1 : Matrix n n 𝕜) :=
    by
    ext1
    simp_rw [Function.comp_apply]
    have : (↑((1 : Matrix n n ℝ) i) : n → 𝕜) j = ↑((1 : Matrix n n ℝ) i j) := rfl
    simp_rw [this, one_apply, ite_cast, IsROrC.ofReal_zero, IsROrC.ofReal_one]
  rw [this, inner_aut_apply_one]

theorem PosDef.rpow.isPosDef [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
    (hQ.rpow r).PosDef :=
  by
  rw [Matrix.PosDef.rpow, pos_def.inner_aut, ← coe_diagonal_eq_diagonal_coe, pos_def.diagonal]
  simp only [Function.comp_apply, IsROrC.ofReal_re, eq_self_iff_true, and_true_iff, Pi.pow_apply]
  intro i
  have := pos_def.pos_eigenvalues hQ i
  apply Real.rpow_pos_of_pos this

theorem PosDef.rpow.isHermitian [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
    (hQ.rpow r).IsHermitian :=
  (PosDef.rpow.isPosDef hQ r).1

theorem PosDef.inv {𝕜 n : Type _} [Fintype n] [IsROrC 𝕜] {Q : Matrix n n 𝕜} [DecidableEq 𝕜]
    [DecidableEq n] (hQ : Q.PosDef) : Q⁻¹.PosDef :=
  by
  rw [← Matrix.PosDef.rpow_neg_one_eq_inv_self hQ, Matrix.PosDef.rpow, pos_def.inner_aut, ←
    coe_diagonal_eq_diagonal_coe, Pi.pow_def]
  constructor
  ·
    simp_rw [is_hermitian, diagonal_conj_transpose, Pi.star_def, IsROrC.star_def,
      Function.comp_apply, IsROrC.conj_ofReal]
  · simp_rw [dot_product, mul_vec, dot_product, diagonal, of_apply, ite_mul, MulZeroClass.zero_mul,
      Function.comp_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.star_apply, mul_comm, ←
      mul_assoc, IsROrC.star_def, IsROrC.conj_mul, ← IsROrC.ofReal_mul, map_sum, IsROrC.ofReal_re]
    intro x hx
    apply Finset.sum_pos'
    · intros
      exact
        mul_nonneg (IsROrC.normSq_nonneg _)
          (Real.rpow_nonneg (le_of_lt (pos_def.pos_eigenvalues hQ i)) _)
    · simp_rw [Ne.def, Function.funext_iff, Pi.zero_apply, Classical.not_forall] at hx
      cases' hx with i hi
      exact
        ⟨i, Finset.mem_univ _,
          mul_pos (is_R_or_C.norm_sq_pos.mpr hi) (Real.rpow_pos_of_pos (hQ.pos_eigenvalues _) _)⟩

theorem PosDef.rpow_ne_zero [Nonempty n] {Q : Matrix n n ℂ} (hQ : Q.PosDef) {r : ℝ} :
    hQ.rpow r ≠ 0 := by
  simp_rw [Matrix.PosDef.rpow, Ne.def, inner_aut_eq_iff, inner_aut_apply_zero, ←
    coe_diagonal_eq_diagonal_coe, ← Matrix.ext_iff, diagonal, DMatrix.zero_apply, of_apply,
    ite_eq_right_iff, Function.comp_apply, IsROrC.ofReal_eq_zero, Pi.pow_apply,
    Real.rpow_eq_zero_iff_of_nonneg (le_of_lt (hQ.pos_eigenvalues _)),
    NormNum.ne_zero_of_pos _ (hQ.pos_eigenvalues _), false_and_iff, imp_false, Classical.not_forall,
    Classical.not_not, exists_eq', exists_const]

end Matrix

