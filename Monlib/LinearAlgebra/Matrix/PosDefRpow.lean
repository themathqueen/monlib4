/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Matrix.PosEqLinearMapIsPositive
import Monlib.LinearAlgebra.InnerAut
import Monlib.LinearAlgebra.Matrix.StarOrderedRing

/-!
 # The real-power of a positive definite matrix

 This file defines the real-power of a positive definite matrix. In particular, given a positive definite matrix `x` and real number `r`, we get `posDef.rpow` as the matrix `eigenvector_matrix * (coe ∘ diagonal (eigenvalues ^ r)) * eigenvector_matrix⁻¹`.

 It also proves some basic obvious properties of `posDef.rpow` such as `posDef.rpow_mul_rpow` and `posDef.rpow_zero`.
-/


namespace Matrix

variable {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable def IsHermitian.rpow {Q : Matrix n n 𝕜} (hQ : IsHermitian Q) (r : ℝ) :
  Matrix n n 𝕜 :=
Matrix.innerAut hQ.eigenvectorUnitary
  (Matrix.diagonal (RCLike.ofReal ∘ (hQ.eigenvalues ^ (r : ℝ) : n → ℝ) : n → 𝕜))

noncomputable abbrev PosSemidef.rpow {Q : Matrix n n 𝕜} (hQ : PosSemidef Q) (r : ℝ) :
  Matrix n n 𝕜 :=
hQ.1.rpow r

noncomputable abbrev PosDef.rpow {Q : Matrix n n 𝕜} (hQ : PosDef Q) (r : ℝ) :
  Matrix n n 𝕜 :=
hQ.1.rpow r

lemma PosDef.rpow_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type _} [Fintype n] [DecidableEq n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
  hQ.rpow r =
  Matrix.innerAut hQ.1.eigenvectorUnitary
    (Matrix.diagonal (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ r : n → ℝ) : n → 𝕜)) :=
rfl

theorem PosSemidef.rpow_mul_rpow (r₁ r₂ : NNRealˣ)
  {Q : Matrix n n 𝕜} (hQ : PosSemidef Q) :
    hQ.rpow r₁ * hQ.rpow r₂ = hQ.rpow (r₁ + r₂) :=
  by
  simp_rw [PosSemidef.rpow, IsHermitian.rpow,
    ← innerAut.map_mul, Pi.pow_def, diagonal_mul_diagonal,
    Function.comp_apply, ← RCLike.ofReal_mul]
  congr
  simp_rw [diagonal_eq_diagonal_iff, Function.comp_apply]
  intro i
  by_cases h : hQ.1.eigenvalues i = 0
  . simp_rw [h]
    rw [Real.zero_rpow, zero_mul, Real.zero_rpow]
    rw [ne_eq]
    rw [← NNReal.coe_add, NNReal.coe_eq_zero]
    simp only [add_eq_zero, Units.ne_zero, and_self, not_false_eq_true]
    simp only [ne_eq, NNReal.coe_eq_zero, Units.ne_zero, not_false_eq_true]
  . rw [← Real.rpow_add]
    apply lt_of_le_of_ne (hQ.eigenvalues_nonneg _)
    rw [ne_eq, eq_comm]
    exact h

theorem PosDef.rpow_mul_rpow (r₁ r₂ : ℝ) {Q : Matrix n n 𝕜} (hQ : PosDef Q) :
    hQ.rpow r₁ * hQ.rpow r₂ = hQ.rpow (r₁ + r₂) :=
  by
  simp_rw [Matrix.PosDef.rpow, IsHermitian.rpow, ← innerAut.map_mul, Pi.pow_def,
    diagonal_mul_diagonal, Function.comp_apply, ← RCLike.ofReal_mul,
    ← Real.rpow_add (hQ.pos_eigenvalues _)]
  rfl

theorem IsHermitian.rpow_one_eq_self {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    hQ.rpow 1 = Q := by
  simp_rw [IsHermitian.rpow, Pi.pow_def, Real.rpow_one]
  rw [← IsHermitian.spectral_theorem'' hQ]

theorem PosSemidef.rpow_one_eq_self {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    hQ.rpow 1 = Q :=
hQ.1.rpow_one_eq_self
theorem PosDef.rpow_one_eq_self {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow 1 = Q :=
hQ.1.rpow_one_eq_self

@[instance]
noncomputable def PosDef.eigenvaluesInvertible {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
  Invertible (IsHermitian.eigenvalues hQ.1) :=
by
  use (IsHermitian.eigenvalues hQ.1)⁻¹
  <;>
  ext i
  <;>
  simp_rw [Pi.mul_apply, Pi.inv_apply]
  simp_rw [inv_mul_cancel₀ (NeZero.of_pos (hQ.pos_eigenvalues i)).out]; rfl
  simp_rw [mul_inv_cancel₀ (NeZero.of_pos (hQ.pos_eigenvalues i)).out]; rfl

@[instance]
noncomputable def PosDef.eigenvaluesInvertible' {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
  Invertible (RCLike.ofReal ∘ (IsHermitian.eigenvalues hQ.1) : n → 𝕜) :=
by
  letI := hQ.eigenvaluesInvertible
  use (RCLike.ofReal ∘ (IsHermitian.eigenvalues hQ.1)⁻¹ : n → 𝕜)
  <;>
  simp only [Pi.mul_def, Function.comp_apply, ← RCLike.ofReal_mul, Pi.inv_def,
    inv_mul_cancel_of_invertible, mul_inv_cancel_of_invertible,
    RCLike.ofReal_one, Pi.one_def]

theorem PosDef.rpow_neg_one_eq_inv_self {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    hQ.rpow (-1) = Q⁻¹ := by
  simp_rw [Matrix.PosDef.rpow]
  symm
  nth_rw 1 [IsHermitian.spectral_theorem'' hQ.1]
  simp_rw [innerAut.map_inv, IsHermitian.rpow, Pi.pow_def, Real.rpow_neg_one, Matrix.inv_diagonal]
  simp only [innerAut_coe, EmbeddingLike.apply_eq_iff_eq, diagonal_eq_diagonal_iff,
    Function.comp_apply, ← RCLike.ofReal_inv]
  intro i
  letI := hQ.eigenvaluesInvertible'
  simp_rw [Ring.inverse_invertible]
  rfl

theorem IsHermitian.rpow_zero {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : hQ.rpow 0 = 1 :=
  by
  simp_rw [IsHermitian.rpow, Pi.pow_def, Real.rpow_zero, coe_diagonal_eq_diagonal_coe,
    diagonal_one, innerAut_coe, EmbeddingLike.map_eq_one_iff]
  ext; simp only [Function.comp_apply, CoeTC.coe, one_apply, coe_ite]; aesop

theorem PosSemidef.rpow_zero {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) : hQ.rpow 0 = 1 :=
hQ.1.rpow_zero
theorem PosDef.rpow_zero {Q : Matrix n n 𝕜} (hQ : Q.PosDef) : hQ.rpow 0 = 1 :=
hQ.1.rpow_zero

theorem IsHermitian.rpow.isHermitian {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) (r : ℝ) :
    (hQ.rpow r).IsHermitian :=
  by
  rw [IsHermitian.rpow, ← innerAut_isHermitian_iff, isHermitian_diagonal_iff]
  simp only [Function.comp_apply, Pi.pow_apply, _root_.IsSelfAdjoint, RCLike.star_def,
    RCLike.conj_ofReal, implies_true]

theorem PosSemidef.rpow.isPosSemidef {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) (r : ℝ) :
    (hQ.rpow r).PosSemidef :=
  by
  rw [Matrix.PosSemidef.rpow, IsHermitian.rpow,
    innerAut_posSemidef_iff, Matrix.PosSemidef.diagonal_iff]
  simp only [Function.comp_apply, RCLike.zero_le_real, Pi.pow_apply]
  exact fun i => Real.rpow_nonneg (PosSemidef.eigenvalues_nonneg hQ i) r

theorem PosDef.rpow.isPosDef {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
    (hQ.rpow r).PosDef :=
  by
  rw [Matrix.PosDef.rpow_eq, innerAut_posDef_iff, Matrix.PosDef.diagonal_iff]
  simp only [Function.comp_apply, RCLike.zero_lt_real, Pi.pow_apply]
  exact fun i => Real.rpow_pos_of_pos (PosDef.pos_eigenvalues hQ i) r

theorem PosSemidef.sqrt_eq_rpow {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
  hQ.sqrt = hQ.rpow (1 / 2) :=
by
  rw [PosSemidef.rpow, PosSemidef.sqrt, IsHermitian.rpow, Matrix.innerAut_apply]
  congr
  simp_rw [diagonal_eq_diagonal_iff, Function.comp_apply, Pi.pow_apply,
    Real.sqrt_eq_rpow, implies_true]

theorem PosDef.sqrt_eq_rpow {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
  hQ.posSemidef.sqrt = hQ.rpow (1 / 2) :=
by convert PosSemidef.sqrt_eq_rpow hQ.posSemidef

-- theorem PosDef.inv {𝕜 n : Type _} [Fintype n] [RCLike 𝕜] {Q : Matrix n n 𝕜}
--     [DecidableEq n] (hQ : Q.PosDef) : Q⁻¹.PosDef :=
--   by
--   rw [← Matrix.PosDef.rpow_neg_one_eq_inv_self hQ]
--   exact Matrix.PosDef.rpow.isPosDef _ _

theorem PosDef.rpow_ne_zero [Nonempty n] {Q : Matrix n n ℂ} (hQ : Q.PosDef) {r : ℝ} :
    hQ.rpow r ≠ 0 := by
  simp_rw [Matrix.PosDef.rpow_eq, ne_eq, innerAut_eq_iff, innerAut_apply_zero,
    ← Matrix.ext_iff, Matrix.diagonal, Matrix.zero_apply, of_apply,
    ite_eq_right_iff, Function.comp_apply, RCLike.ofReal_eq_zero, Pi.pow_apply,
    Real.rpow_eq_zero_iff_of_nonneg (le_of_lt (hQ.pos_eigenvalues _)),
    (NeZero.of_pos (hQ.pos_eigenvalues _)).out, false_and, imp_false, Classical.not_forall,
    Classical.not_not, exists_eq', exists_const]

lemma IsHermitian.rpow_cast {𝕜 : Type*} [RCLike 𝕜] {n : Type _} [Fintype n] [DecidableEq n]
  {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) (r : ℝ)
  {S : Matrix n n 𝕜}
  (hQS : Q = S) :
  hQ.rpow r = (by rw [← hQS]; exact hQ : IsHermitian S).rpow r :=
by aesop
lemma PosDef.rpow_cast {𝕜 : Type*} [RCLike 𝕜] {n : Type _} [Fintype n] [DecidableEq n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ)
  {S : Matrix n n 𝕜}
  (hQS : Q = S) :
  hQ.rpow r = (by rw [← hQS]; exact hQ : PosDef S).rpow r :=
Matrix.IsHermitian.rpow_cast _ _ hQS
lemma PosSemidef.rpow_cast {𝕜 : Type*} [RCLike 𝕜] {n : Type _} [Fintype n] [DecidableEq n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) (r : ℝ)
  {S : Matrix n n 𝕜}
  (hQS : Q = S) :
  hQ.rpow r = (by rw [← hQS]; exact hQ : PosSemidef S).rpow r :=
Matrix.IsHermitian.rpow_cast _ _ hQS

theorem IsHermitian.eigenvectorMatrix_conjTranspose_mul
  {𝕜 : Type*} [RCLike 𝕜] {x : Matrix n n 𝕜} (hx : x.IsHermitian) :
    hx.eigenvectorMatrixᴴ * hx.eigenvectorMatrix = 1 :=
by
  rw [eigenvectorUnitary_coe_eq_eigenvectorMatrix, ← star_eq_conjTranspose]
  exact UnitaryGroup.star_mul_self _

theorem posDefOne_rpow {𝕜 : Type*} [RCLike 𝕜]
  (n : Type _) [Fintype n] [DecidableEq n] (r : ℝ) :
    (posDefOne : PosDef (1 : Matrix n n 𝕜)).rpow r = 1 :=
  by
  rw [PosDef.rpow_eq, innerAut_eq_iff, innerAut_apply_one]
  symm
  nth_rw 1 [← diagonal_one]
  rw [diagonal_eq_diagonal_iff]
  intro i
  simp_rw [Function.comp_apply, Pi.pow_apply]
  rw [← RCLike.ofReal_one, RCLike.ofReal_inj, IsHermitian.eigenvalues_eq', one_mulVec]
  simp_rw [dotProduct, Pi.star_apply, transpose_apply, ← conjTranspose_apply,
    ← mul_apply, IsHermitian.eigenvectorMatrix_conjTranspose_mul, one_apply_eq,
    RCLike.one_re]
  exact (Real.one_rpow _).symm

end Matrix
