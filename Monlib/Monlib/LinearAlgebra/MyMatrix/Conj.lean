/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Data.Matrix.Basic
import LinearAlgebra.Matrix.Hermitian
import Preq.Ites

#align_import linear_algebra.my_matrix.conj

/-!
 # Conjugate of a matrix

This file defines the conjugate of a matrix, `matrix.conj` with the notation of this being `ᴴᵀ` (i.e., `xᴴᵀ i j = star (x i j)`), and shows basic properties about it.
-/


namespace Matrix

open scoped Matrix

variable {α n₁ n₂ : Type _}

/--
conjugate of matrix defined as $\bar{x} := {(x^*)}^\top$, i.e., $\bar{x}_{ij}=\overline{x_{ij}}$ -/
def conj [Star α] (x : Matrix n₁ n₂ α) : Matrix n₁ n₂ α :=
  xᴴᵀ

scoped postfix:1024 "ᴴᵀ" => Matrix.conj

theorem conj_apply [Star α] (x : Matrix n₁ n₂ α) (i : n₁) (j : n₂) : xᴴᵀ i j = star (x i j) :=
  rfl

theorem conj_conj [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᵀᴴᵀ = x :=
  calc
    xᴴᵀᴴᵀ = xᵀᵀᴴᴴ := rfl
    _ = xᵀᵀ := (conjTranspose_conjTranspose _)
    _ = x := transpose_transpose _

theorem conj_add [AddMonoid α] [StarAddMonoid α] (x y : Matrix n₁ n₂ α) : (x + y)ᴴᵀ = xᴴᵀ + yᴴᵀ :=
  by simp_rw [conj, ← transpose_add, ← conj_transpose_add]

theorem conj_smul {R : Type _} [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (x : Matrix n₁ n₂ α) : (c • x)ᴴᵀ = star c • xᴴᵀ := by
  simp_rw [conj, ← transpose_smul, ← conj_transpose_smul]

theorem conj_conjTranspose [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᵀᴴ = xᵀ :=
  calc
    xᴴᵀᴴ = xᵀᴴᴴ := rfl
    _ = xᵀ := conjTranspose_conjTranspose _

theorem conjTranspose_conj [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᴴᵀ = xᵀ :=
  calc
    xᴴᴴᵀ = xᴴᵀᴴ := rfl
    _ = xᵀ := conj_conjTranspose _

theorem transpose_conj_eq_conjTranspose [Star α] (x : Matrix n₁ n₂ α) : xᴴᵀᵀ = xᴴ :=
  rfl

theorem IsHermitian.conj {α n : Type _} [Star α] {x : Matrix n n α} (hx : x.IsHermitian) :
    xᴴᵀ = xᵀ := by simp_rw [conj, hx.eq]

theorem conj_hMul {α m n p : Type _} [Fintype n] [CommSemiring α] [StarRing α] (x : Matrix m n α)
    (y : Matrix n p α) : (x ⬝ y)ᴴᵀ = xᴴᵀ ⬝ yᴴᵀ :=
  by
  ext1
  simp_rw [conj_apply, mul_apply, star_sum, StarMul.star_hMul, conj_apply, mul_comm]

theorem conj_one {α n : Type _} [DecidableEq n] [CommSemiring α] [StarRing α] :
    (1 : Matrix n n α)ᴴᵀ = 1 := by
  ext1
  simp_rw [conj_apply, one_apply, star_ite, star_one, star_zero]

end Matrix

