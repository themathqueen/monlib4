/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.MyMatrix.PosEqLinearMapIsPositive
import Monlib.LinearAlgebra.InnerAut
import Monlib.LinearAlgebra.MyMatrix.StarOrderedRing

#align_import linear_algebra.my_matrix.posDef_rpow

/-!
 # The real-power of a positive definite matrix

 This file defines the real-power of a positive definite matrix. In particular, given a positive definite matrix `x` and real number `r`, we get `posDef.rpow` as the matrix `eigenvector_matrix * (coe ∘ diagonal (eigenvalues ^ r)) * eigenvector_matrix⁻¹`.

 It also proves some basic obvious properties of `posDef.rpow` such as `posDef.rpow_mul_rpow` and `posDef.rpow_zero`.
-/


namespace Matrix

variable {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix BigOperators ComplexOrder MatrixOrder

-- noncomputable def IsHermitian.rpow {Q : Matrix n n 𝕜} (hQ : IsHermitian Q) (r : ℝ) :
--   Matrix n n 𝕜 :=
--   Matrix.innerAut hQ.eigenvectorUnitary
--     (Matrix.diagonal (RCLike.ofReal ∘ (hQ.eigenvalues ^ r : n → ℝ) : n → 𝕜))

noncomputable def PosDef.rpow {Q : Matrix n n 𝕜} (hQ : PosDef Q) (r : ℝ) :
  Matrix n n 𝕜 :=
  Matrix.innerAut hQ.1.eigenvectorUnitary
    (Matrix.diagonal (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ r : n → ℝ) : n → 𝕜))

noncomputable def PosSemidef.rpow {Q : Matrix n n 𝕜} (hQ : PosSemidef Q) (r : NNReal) :
  Matrix n n 𝕜 :=
Matrix.innerAut hQ.1.eigenvectorUnitary
  (Matrix.diagonal (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ (r : ℝ) : n → ℝ) : n → 𝕜))

theorem PosDef.rpow_mul_rpow (r₁ r₂ : ℝ) {Q : Matrix n n 𝕜} (hQ : PosDef Q) :
    hQ.rpow r₁ * hQ.rpow r₂ = hQ.rpow (r₁ + r₂) :=
  by
  simp_rw [Matrix.PosDef.rpow, ← innerAut.map_mul, Pi.pow_def, diagonal_mul_diagonal,
    Function.comp_apply, ← RCLike.ofReal_mul, ← Real.rpow_add (hQ.pos_eigenvalues _)]
  rfl

theorem PosSemidef.rpow_mul_rpow (r₁ r₂ : NNRealˣ) (h : r₁ + (r₂ : NNReal) ≠ 0)
  {Q : Matrix n n 𝕜} (hQ : PosSemidef Q) :
    hQ.rpow r₁ * hQ.rpow r₂ = hQ.rpow (r₁ + r₂) :=
  by
  simp_rw [Matrix.PosSemidef.rpow, ← innerAut.map_mul, Pi.pow_def, diagonal_mul_diagonal,
    Function.comp_apply, ← RCLike.ofReal_mul]
  congr
  simp_rw [diagonal_eq_diagonal_iff, Function.comp_apply]
  intro i
  by_cases h : hQ.1.eigenvalues i = 0
  . simp_rw [h]
    rw [Real.zero_rpow, zero_mul, Real.zero_rpow]
    rw [ne_eq, NNReal.coe_eq_zero]
    simp only [add_eq_zero_iff, Units.ne_zero, and_self, not_false_eq_true]
    simp only [ne_eq, NNReal.coe_eq_zero, Units.ne_zero, not_false_eq_true]
  . rw [← Real.rpow_add]; rfl
    apply lt_of_le_of_ne (hQ.eigenvalues_nonneg _)
    rw [ne_eq, eq_comm]
    exact h

theorem PosDef.rpow_one_eq_self {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow 1 = Q := by
  simp_rw [PosDef.rpow, Pi.pow_def, Real.rpow_one]
  rw [← IsHermitian.spectral_theorem'' hQ.1]

theorem PosSemidef.rpow_one_eq_self {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    hQ.rpow 1 = Q := by
  simp_rw [PosSemidef.rpow, Pi.pow_def, NNReal.coe_one, Real.rpow_one]
  rw [← IsHermitian.spectral_theorem'' hQ.1]

@[instance]
noncomputable def PosDef.eigenvaluesInvertible {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
  Invertible (IsHermitian.eigenvalues hQ.1) :=
by
  use (IsHermitian.eigenvalues hQ.1)⁻¹
  <;>
  ext i
  <;>
  simp_rw [Pi.mul_apply, Pi.inv_apply]
  simp_rw [inv_mul_cancel (NeZero.of_pos (hQ.pos_eigenvalues i)).out]; rfl
  simp_rw [mul_inv_cancel (NeZero.of_pos (hQ.pos_eigenvalues i)).out]; rfl

@[instance]
noncomputable def PosDef.eigenvaluesInvertible' {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
  Invertible (RCLike.ofReal ∘ (IsHermitian.eigenvalues hQ.1) : n → 𝕜) :=
by
  use (RCLike.ofReal ∘ (IsHermitian.eigenvalues hQ.1)⁻¹ : n → 𝕜)
  <;>
  ext i
  <;>
  simp_rw [Pi.mul_apply, Function.comp_apply, Pi.inv_apply, ← RCLike.ofReal_mul, Pi.one_apply]
  simp_rw [inv_mul_cancel (NeZero.of_pos (hQ.pos_eigenvalues i)).out, algebraMap.coe_one]
  simp_rw [mul_inv_cancel (NeZero.of_pos (hQ.pos_eigenvalues i)).out, algebraMap.coe_one]

theorem PosDef.rpow_neg_one_eq_inv_self [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow (-1) = Q⁻¹ := by
  simp_rw [Matrix.PosDef.rpow]
  symm
  nth_rw 1 [IsHermitian.spectral_theorem'' hQ.1]
  simp_rw [innerAut.map_inv, Pi.pow_def, Real.rpow_neg_one, Matrix.inv_diagonal]
  simp only [innerAut_coe, EmbeddingLike.apply_eq_iff_eq, diagonal_eq_diagonal_iff,
    Function.comp_apply, ← RCLike.ofReal_inv]
  intro i
  letI := hQ.eigenvaluesInvertible'
  simp_rw [Ring.inverse_invertible]
  rfl

theorem PosDef.rpow_zero [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) : hQ.rpow 0 = 1 :=
  by
  simp_rw [Matrix.PosDef.rpow, Pi.pow_def, Real.rpow_zero, coe_diagonal_eq_diagonal_coe,
    diagonal_one, innerAut_coe, MulEquivClass.map_eq_one_iff]
  ext; simp only [Function.comp_apply, CoeTC.coe, one_apply, coe_ite]; aesop

theorem PosDef.rpow.isPosDef [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
    (hQ.rpow r).PosDef :=
  by
  rw [Matrix.PosDef.rpow, innerAut_posDef_iff, Matrix.PosDef.diagonal]
  simp only [Function.comp_apply, RCLike.zero_lt_real, Pi.pow_apply]
  exact fun i => Real.rpow_pos_of_pos (PosDef.pos_eigenvalues hQ i) r

theorem PosSemidef.sqrt_eq_rpow {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
  hQ.sqrt = hQ.rpow (1 / 2) :=
by
  rw [PosSemidef.rpow, PosSemidef.sqrt, Matrix.innerAut_apply]
  congr
  simp_rw [diagonal_eq_diagonal_iff, Function.comp_apply, Pi.pow_apply,
    Real.sqrt_eq_rpow]
  intro
  rfl

theorem PosDef.sqrt_eq_rpow {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
  hQ.posSemidef.sqrt = hQ.rpow (1 / 2) :=
by convert PosSemidef.sqrt_eq_rpow hQ.posSemidef

theorem PosDef.rpow.isHermitian [DecidableEq 𝕜] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
    (hQ.rpow r).IsHermitian :=
  (PosDef.rpow.isPosDef hQ r).1

theorem PosDef.inv {𝕜 n : Type _} [Fintype n] [RCLike 𝕜] {Q : Matrix n n 𝕜} [DecidableEq 𝕜]
    [DecidableEq n] (hQ : Q.PosDef) : Q⁻¹.PosDef :=
  by
  rw [← Matrix.PosDef.rpow_neg_one_eq_inv_self hQ]
  exact Matrix.PosDef.rpow.isPosDef _ _

theorem PosDef.rpow_ne_zero [Nonempty n] {Q : Matrix n n ℂ} (hQ : Q.PosDef) {r : ℝ} :
    hQ.rpow r ≠ 0 := by
  simp_rw [Matrix.PosDef.rpow, ne_eq, innerAut_eq_iff, innerAut_apply_zero,
    ← Matrix.ext_iff, Matrix.diagonal, Matrix.zero_apply, of_apply,
    ite_eq_right_iff, Function.comp_apply, RCLike.ofReal_eq_zero, Pi.pow_apply,
    Real.rpow_eq_zero_iff_of_nonneg (le_of_lt (hQ.pos_eigenvalues _)),
    (NeZero.of_pos (hQ.pos_eigenvalues _)).out, false_and_iff, imp_false, Classical.not_forall,
    Classical.not_not, exists_eq', exists_const]

end Matrix
