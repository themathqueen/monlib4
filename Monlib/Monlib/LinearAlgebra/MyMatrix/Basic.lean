/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.Matrix.ToLin
import LinearAlgebra.Matrix.Spectrum
import LinearAlgebra.MyMatrix.Conj
import LinearAlgebra.Trace
import Preq.Finset
import LinearAlgebra.MyIps.RankOne
import Data.Matrix.Kronecker

#align_import linear_algebra.my_matrix.basic

/-!

# Some obvious lemmas on matrices

This file includes some necessary and obvious results for matrices,
such as `matrix.mul_vec_eq`.

We also show that the trace of a symmetric matrix is equal to the sum of its eigenvalues.

-/


namespace Matrix

variable {𝕜 n : Type _} [Field 𝕜] [Fintype n]

theorem eq_zero {R n₁ n₂ : Type _} [Zero R] (x : Matrix n₁ n₂ R) :
    (∀ (i : n₁) (j : n₂), x i j = 0) ↔ x = 0 := by simp_rw [← Matrix.ext_iff, Pi.zero_apply]

/--
two matrices $a,b \in M_n$ are equal iff for all vectors $c \in \mathbb{k}^n$ we have $a c = b c$,
  essentially, treat them as linear maps on $\mathbb{k}^n$ so you can have extentionality with vectors -/
theorem mulVec_eq {R m n : Type _} [CommSemiring R] [Fintype n] [DecidableEq n]
    (a b : Matrix m n R) : a = b ↔ ∀ c : n → R, a.mulVec c = b.mulVec c :=
  by
  refine' ⟨fun h c => by rw [h], fun h => _⟩
  ext
  rw [← mul_vec_std_basis a i j, ← mul_vec_std_basis b i j, h _]

/-- a vector is nonzero iff one of its elements are nonzero -/
theorem vec_ne_zero {R n : Type _} [Semiring R] (a : n → R) : (∃ i, a i ≠ 0) ↔ a ≠ 0 :=
  by
  simp_rw [Ne.def, ← Classical.not_forall]
  constructor
  · intro h h2
    simp_rw [h2, Pi.zero_apply, eq_self_iff_true, imp_true_iff, not_true] at h
    exact h
  · intro h h2
    apply h
    ext
    rw [Pi.zero_apply]
    exact h2 x

/-- two vectors are equal iff their elements are equal -/
theorem ext_vec {𝕜 n : Type _} (α β : n → 𝕜) : α = β ↔ ∀ i : n, α i = β i :=
  by
  refine' ⟨fun h i => by rw [h], fun h => _⟩
  ext i; exact h i

/-- the outer product of two nonzero vectors is nonzero -/
theorem vecMulVec_ne_zero {R n : Type _} [Semiring R] [NoZeroDivisors R] {α β : n → R} (hα : α ≠ 0)
    (hβ : β ≠ 0) : vecMulVec α β ≠ 0 :=
  by
  rw [Ne.def, ← ext_iff]
  rw [← vec_ne_zero] at hα hβ
  cases' hβ with i hiy
  cases' hα with j hju
  simp_rw [vec_mul_vec_eq, mul_apply, Fintype.univ_punit, col_apply, row_apply, Finset.sum_const,
    Finset.card_singleton, nsmul_eq_mul, algebraMap.coe_one, one_mul, Pi.zero_apply, mul_eq_zero,
    Classical.not_forall]
  use j; use i
  push_neg
  exact ⟨hju, hiy⟩

/-- the transpose of `vec_mul_vec x y` is simply `vec_mul_vec y x`  -/
theorem vecMulVec_transpose {R n : Type _} [CommSemiring R] (x y : n → R) :
    (vecMulVec x y).transpose = vecMulVec y x := by
  simp_rw [← Matrix.ext_iff, transpose_apply, vec_mul_vec, mul_comm, of_apply, eq_self_iff_true,
    forall₂_true_iff]

open scoped BigOperators

/-- the identity written as a sum of the standard basis -/
theorem one_eq_sum_std_matrix {n R : Type _} [CommSemiring R] [Fintype n] [DecidableEq n] :
    (1 : Matrix n n R) = ∑ r : n, Matrix.stdBasisMatrix r r (1 : R) := by
  simp_rw [← Matrix.ext_iff, Finset.sum_apply, Matrix.one_apply, Matrix.stdBasisMatrix, ite_and,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, eq_self_iff_true, forall₂_true_iff]

open scoped Matrix ComplexConjugate

open IsROrC Matrix

end Matrix

section trace

variable {ℍ ℍ₂ 𝕜 : Type _} [NormedAddCommGroup ℍ] [NormedAddCommGroup ℍ₂] [IsROrC 𝕜]
  [InnerProductSpace 𝕜 ℍ] [InnerProductSpace 𝕜 ℍ₂] [FiniteDimensional 𝕜 ℍ] [FiniteDimensional 𝕜 ℍ₂]
  {n : Type _} [Fintype n]

local notation "l(" x ")" => x →ₗ[𝕜] x

local notation "L(" x ")" => x →L[𝕜] x

local notation "𝕂" x => Matrix x x 𝕜

open scoped TensorProduct Kronecker BigOperators

/-- $\textnormal{Tr}(A\otimes_k B)=\textnormal{Tr}(A)\textnormal{Tr}(B)$ -/
theorem Matrix.kronecker.trace (A B : 𝕂 n) : (A ⊗ₖ B).trace = A.trace * B.trace :=
  by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.kroneckerMap, Finset.sum_mul_sum]
  rfl

example (A : l(ℍ)) (B : l(ℍ₂)) :
    LinearMap.trace 𝕜 (ℍ ⊗[𝕜] ℍ₂) (TensorProduct.map A B) =
      LinearMap.trace 𝕜 ℍ A * LinearMap.trace 𝕜 ℍ₂ B :=
  LinearMap.trace_tensorProduct' _ _

open LinearMap

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i y) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i y) -/
/-- the trace of a Hermitian matrix is the sum of its eigenvalues -/
theorem Matrix.IsHermitian.trace_eq [DecidableEq n] [DecidableEq 𝕜] {A : 𝕂 n} (hA : A.IsHermitian) :
    A.trace = ∑ i : n, hA.Eigenvalues i :=
  by
  simp_rw [hA.eigenvalues_eq, Matrix.trace, Matrix.diag, Matrix.dotProduct, Pi.star_apply,
    Matrix.mulVec, Matrix.transpose_apply, Matrix.dotProduct, Matrix.transpose_apply,
    Matrix.IsHermitian.eigenvectorMatrix_apply, ← hA.eigenvector_matrix_inv_apply, Finset.mul_sum, ←
    hA.eigenvector_matrix_apply, mul_comm _ (_ * _), mul_assoc, _root_.map_sum]
  norm_cast
  rw [Finset.sum_comm]
  have :=
    calc
      ∑ (y : n) (x : n) (i : n),
            IsROrC.re (A y i * (hA.eigenvector_matrix i x * hA.eigenvector_matrix_inv x y)) =
          ∑ (i : n) (y : n),
            IsROrC.re
              (A y i * ∑ x : n, hA.eigenvector_matrix i x * hA.eigenvector_matrix_inv x y) :=
        by simp_rw [Finset.mul_sum, _root_.map_sum]; rw [Finset.sum_sum_sum]
      _ = ∑ (i : n) (y : n), IsROrC.re (A y i * (1 : 𝕂 n) i y) := by
        simp_rw [← Matrix.mul_apply, Matrix.IsHermitian.eigenvectorMatrix_mul_inv]
      _ = ∑ y : n, IsROrC.re (∑ i : n, A y i * (1 : 𝕂 n) i y) := by simp_rw [← _root_.map_sum];
        rw [Finset.sum_comm]
      _ = ∑ y : n, IsROrC.re ((A.mul 1) y y) := by simp_rw [← Matrix.mul_apply]
      _ = ∑ y : n, IsROrC.re (A y y) := by rw [Matrix.mul_one]
  · rw [this, IsROrC.ofReal_sum]
    congr
    ext1 i
    rw [hA.coe_re_apply_self i]

theorem LinearMap.IsSymmetric.eigenvalue_mem_spectrum [DecidableEq 𝕜]
    (hn : FiniteDimensional.finrank 𝕜 ℍ = Fintype.card n) {A : l(ℍ)} (hA : A.IsSymmetric)
    (i : Fin (Fintype.card n)) : (hA.Eigenvalues hn i : 𝕜) ∈ spectrum 𝕜 A :=
  by
  simp_rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact hA.has_eigenvalue_eigenvalues hn i

theorem Matrix.IsHermitian.eigenvalues_hasEigenvalue {𝕜 n : Type _} [IsROrC 𝕜] [Fintype n]
    [DecidableEq n] [DecidableEq 𝕜] {M : Matrix n n 𝕜} (hM : M.IsHermitian) (i : n) :
    Module.End.HasEigenvalue M.toEuclideanLin (hM.Eigenvalues i) :=
  by
  simp_rw [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀]
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _

theorem Matrix.IsHermitian.hasEigenvector_eigenvectorBasis {𝕜 n : Type _} [IsROrC 𝕜] [Fintype n]
    [DecidableEq n] [DecidableEq 𝕜] {M : Matrix n n 𝕜} (hM : M.IsHermitian) (i : n) :
    Module.End.HasEigenvector M.toEuclideanLin (hM.Eigenvalues i) (hM.eigenvectorBasis i) :=
  by
  simp_rw [Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvalues,
    Matrix.IsHermitian.eigenvalues₀, OrthonormalBasis.reindex_apply]
  exact LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis _ _ _

/-- a Hermitian matrix applied to its eigenvector basis element equals
  the basis element scalar-ed by its respective eigenvalue -/
theorem Matrix.IsHermitian.apply_eigenvectorBasis {𝕜 n : Type _} [IsROrC 𝕜] [Fintype n]
    [DecidableEq n] [DecidableEq 𝕜] {M : Matrix n n 𝕜} (hM : M.IsHermitian) (i : n) :
    M.mulVec (hM.eigenvectorBasis i) = hM.Eigenvalues i • hM.eigenvectorBasis i :=
  by
  calc
    M.mul_vec (hM.eigenvector_basis i) = M.to_euclidean_lin (hM.eigenvector_basis i) := rfl
    _ = hM.eigenvalues i • hM.eigenvector_basis i := _
  rw [module.End.mem_eigenspace_iff.mp (hM.has_eigenvector_eigenvector_basis i).1]
  unfold_coes
  simp only [RingHom.toFun_eq_coe, algebraMap_smul]

open scoped Matrix

theorem EuclideanSpace.inner_eq {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n] {x y : n → 𝕜} :
    (@EuclideanSpace.instInnerProductSpace n 𝕜 _ _).inner x y = star x ⬝ᵥ y :=
  rfl

theorem EuclideanSpace.rankOne_of_orthonormalBasis_eq_one {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n]
    (h : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) :
    ∑ i : n, (rankOne (h i) (h i) : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) = 1 :=
  by
  rw [ContinuousLinearMap.ext_iff]
  intro x
  apply @ext_inner_left 𝕜 _ _ _ EuclideanSpace.instInnerProductSpace
  intro v
  simp_rw [ContinuousLinearMap.sum_apply, rankOne_apply]
  rw [inner_sum]
  simp_rw [inner_smul_right, mul_comm, OrthonormalBasis.sum_inner_mul_inner,
    ContinuousLinearMap.one_apply]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k l) -/
/-- for any matrix $x\in M_{n_1 \times n_2}$, we have
  $$x=\sum_{i,j,k,l}x_{ik}^{jl}(e_{ij} \otimes_k e_{kl}) $$ -/
theorem kmul_representation {R n₁ n₂ : Type _} [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] [Semiring R] (x : Matrix (n₁ × n₂) (n₁ × n₂) R) :
    x =
      ∑ (i : n₁) (j : n₁) (k : n₂) (l : n₂),
        x (i, k) (j, l) • Matrix.stdBasisMatrix i j (1 : R) ⊗ₖ Matrix.stdBasisMatrix k l (1 : R) :=
  by
  simp_rw [← Matrix.ext_iff, Finset.sum_apply, Pi.smul_apply, Matrix.kroneckerMap,
    Matrix.stdBasisMatrix, ite_mul, MulZeroClass.zero_mul, one_mul, Matrix.of_apply, smul_ite,
    smul_zero, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Prod.mk.eta, smul_eq_mul, mul_one, eq_self_iff_true, forall₂_true_iff]

open Matrix

/-- $(x \otimes_k y)^* = x^* \otimes_k y^*$ -/
theorem Matrix.kronecker_conjTranspose {R m n : Type _} [CommSemiring R] [StarRing R]
    (x : Matrix n n R) (y : Matrix m m R) : (x ⊗ₖ y)ᴴ = xᴴ ⊗ₖ yᴴ := by
  simp_rw [← Matrix.ext_iff, conj_transpose_apply, kronecker_map, of_apply, star_mul',
    conj_transpose_apply, eq_self_iff_true, forall₂_true_iff]

theorem Matrix.kronecker.star {n : Type _} (x y : Matrix n n 𝕜) :
    star (x ⊗ₖ y) = star x ⊗ₖ star y :=
  Matrix.kronecker_conjTranspose _ _

-- MOVE:
theorem Matrix.kronecker.transpose {n : Type _} (x y : Matrix n n 𝕜) : (x ⊗ₖ y)ᵀ = xᵀ ⊗ₖ yᵀ :=
  by
  simp_rw [← Matrix.ext_iff]
  intros
  simp only [Matrix.transpose_apply, Matrix.kroneckerMap, of_apply]

theorem Matrix.kronecker.conj {n : Type _} (x y : Matrix n n 𝕜) : (x ⊗ₖ y)ᴴᵀ = xᴴᵀ ⊗ₖ yᴴᵀ := by
  rw [conj, Matrix.kronecker_conjTranspose, Matrix.kronecker.transpose] <;> rfl

theorem Matrix.IsHermitian.eigenvectorMatrix_mem_unitaryGroup {𝕜 : Type _} [IsROrC 𝕜]
    [DecidableEq 𝕜] [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.IsHermitian) :
    hx.eigenvectorMatrix ∈ Matrix.unitaryGroup n 𝕜 := by
  simp_rw [mem_unitary_group_iff, star_eq_conj_transpose, mul_eq_mul,
    is_hermitian.conj_transpose_eigenvector_matrix, is_hermitian.eigenvector_matrix_mul_inv]

theorem Matrix.unitaryGroup.coe_mk [DecidableEq n] (x : Matrix n n 𝕜)
    (hx : x ∈ Matrix.unitaryGroup n 𝕜) : ⇑(⟨x, hx⟩ : Matrix.unitaryGroup n 𝕜) = x :=
  rfl

end trace

open scoped Matrix

variable {R n m : Type _} [Semiring R] [StarAddMonoid R] [DecidableEq n] [DecidableEq m]

theorem Matrix.stdBasisMatrix_conjTranspose (i : n) (j : m) (a : R) :
    (Matrix.stdBasisMatrix i j a)ᴴ = Matrix.stdBasisMatrix j i (star a) :=
  by
  simp_rw [Matrix.stdBasisMatrix, ite_and]
  ext1 x; ext1 y
  by_cases j = x ∧ i = y
  ·
    simp_rw [h.1, h.2, eq_self_iff_true, if_true, Matrix.conjTranspose_apply, eq_self_iff_true,
      if_true]
  simp_rw [Matrix.conjTranspose_apply]
  by_cases h' : a = 0
  · simp_rw [h', if_t_t, star_zero, if_t_t]
  · simp_rw [← ite_and, and_comm' _ (j = x), (Ne.ite_eq_right_iff (star_ne_zero.mpr h')).mpr h,
      star_eq_iff_star_eq, star_zero]
    symm
    rw [ite_eq_right_iff]
    intro H
    exfalso
    exact h H

theorem Matrix.stdBasisMatrix.star_apply (i k : n) (j l : m) (a : R) :
    star (Matrix.stdBasisMatrix i j a k l) = Matrix.stdBasisMatrix j i (star a) l k := by
  rw [← Matrix.stdBasisMatrix_conjTranspose, ← Matrix.conjTranspose_apply]

theorem Matrix.stdBasisMatrix.star_apply' (i : n) (j : m) (x : n × m) (a : R) :
    star (Matrix.stdBasisMatrix i j a x.fst x.snd) =
      Matrix.stdBasisMatrix j i (star a) x.snd x.fst :=
  by rw [Matrix.stdBasisMatrix.star_apply]

/-- $e_{ij}^*=e_{ji}$ -/
theorem Matrix.stdBasisMatrix.star_one {R : Type _} [Semiring R] [StarRing R] (i : n) (j : m) :
    (Matrix.stdBasisMatrix i j (1 : R))ᴴ = Matrix.stdBasisMatrix j i (1 : R) :=
  by
  nth_rw 2 [← star_one R]
  exact Matrix.stdBasisMatrix_conjTranspose _ _ _

open scoped BigOperators

theorem Matrix.trace_iff {R n : Type _} [AddCommMonoid R] [Fintype n] (x : Matrix n n R) :
    x.trace = ∑ k : n, x k k :=
  rfl

theorem Matrix.stdBasisMatrix.hMul_apply_basis {R p q : Type _} [Semiring R] [DecidableEq p]
    [DecidableEq q] (i x : n) (j y : m) (k z : p) (l w : q) :
    Matrix.stdBasisMatrix k l (Matrix.stdBasisMatrix i j (1 : R) x y) z w =
      Matrix.stdBasisMatrix i j (1 : R) x y * Matrix.stdBasisMatrix k l (1 : R) z w :=
  by
  simp_rw [Matrix.stdBasisMatrix, ite_and, ite_mul, MulZeroClass.zero_mul, one_mul, ← ite_and,
    and_rotate, and_assoc', and_comm']

theorem Matrix.stdBasisMatrix.mul_apply_basis' {R p q : Type _} [Semiring R] [DecidableEq p]
    [DecidableEq q] (i x : n) (j y : m) (k z : p) (l w : q) :
    Matrix.stdBasisMatrix k l (Matrix.stdBasisMatrix i j (1 : R) x y) z w =
      ite (i = x ∧ j = y ∧ k = z ∧ l = w) 1 0 :=
  by
  simp_rw [Matrix.stdBasisMatrix.hMul_apply_basis, Matrix.stdBasisMatrix, ite_and, ite_mul,
    MulZeroClass.zero_mul, one_mul]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x x_1) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_2 x_3) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x x_1) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_2 x_3) -/
theorem Matrix.stdBasisMatrix.hMul_apply {R : Type _} [Fintype n] [Semiring R] (i j k l m p : n) :
    ∑ (x : n × n) (x_1 : n × n) (x_2 : n) (x_3 : n),
        Matrix.stdBasisMatrix l k (Matrix.stdBasisMatrix p m (1 : R) x_1.snd x_1.fst) x.snd x.fst *
          Matrix.stdBasisMatrix i x_2 (Matrix.stdBasisMatrix x_3 j (1 : R) x_1.fst x_1.snd) x.fst
            x.snd =
      ∑ (x : n × n) (x_1 : n × n) (x_2 : n) (x_3 : n),
        ite
          (p = x_1.snd ∧
            m = x_1.fst ∧
              l = x.snd ∧ k = x.fst ∧ x_3 = x_1.fst ∧ j = x_1.snd ∧ i = x.fst ∧ x_2 = x.snd)
          1 0 :=
  by
  simp_rw [Matrix.stdBasisMatrix.mul_apply_basis', ite_mul, one_mul, MulZeroClass.zero_mul, ←
    ite_and, and_assoc']

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k l m p) -/
@[simp]
theorem Matrix.stdBasisMatrix.sum_star_hMul_self [Fintype n] (i j : n) (a b : R) :
    ∑ (k : n) (l : n) (m : n) (p : n),
        Matrix.stdBasisMatrix i j a k l * star (Matrix.stdBasisMatrix i j b) m p =
      a * star b :=
  by
  simp_rw [Matrix.star_apply, Matrix.stdBasisMatrix.star_apply, Matrix.stdBasisMatrix, ite_mul,
    MulZeroClass.zero_mul, mul_ite, MulZeroClass.mul_zero, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (kl mp) -/
theorem Matrix.stdBasisMatrix.sum_star_hMul_self' {R : Type _} [Fintype n] [Semiring R] [StarRing R]
    (i j : n) :
    ∑ (kl : n × n) (mp : n × n),
        Matrix.stdBasisMatrix i j (1 : R) kl.1 kl.2 *
          star Matrix.stdBasisMatrix i j (1 : R) mp.1 mp.2 =
      1 :=
  by
  nth_rw_rhs 1 [← one_mul (1 : R)]
  nth_rw_rhs 2 [← star_one R]
  nth_rw_rhs 1 [← Matrix.stdBasisMatrix.sum_star_hMul_self i j _ _]
  simp_rw [← Finset.mul_sum, ← Finset.sum_product']
  rfl

theorem Matrix.stdBasisMatrix.hMul_stdBasisMatrix {R p : Type _} [Semiring R] [DecidableEq p]
    [Fintype m] (i x : n) (j k : m) (l y : p) (a b : R) :
    (Matrix.stdBasisMatrix i j a ⬝ Matrix.stdBasisMatrix k l b) x y =
      ite (i = x ∧ j = k ∧ l = y) (a * b) 0 :=
  by
  simp_rw [Matrix.mul_apply, Matrix.stdBasisMatrix, ite_and, ite_mul, MulZeroClass.zero_mul,
    mul_ite, MulZeroClass.mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_const_zero, eq_comm]

theorem Matrix.stdBasisMatrix.hMul_std_basis_matrix' {R p : Type _} [Fintype n] [DecidableEq p]
    [Semiring R] (i : m) (j k : n) (l : p) :
    Matrix.stdBasisMatrix i j (1 : R) ⬝ Matrix.stdBasisMatrix k l (1 : R) =
      ite (j = k) (1 : R) 0 • Matrix.stdBasisMatrix i l (1 : R) :=
  by
  ext1 x y
  simp_rw [Pi.smul_apply, Matrix.mul_apply, Matrix.stdBasisMatrix, ite_and, ite_mul,
    MulZeroClass.zero_mul, one_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_const_zero, smul_ite, smul_zero, smul_eq_mul, mul_one, ← ite_and, eq_comm,
    and_comm']

theorem LinearMap.toMatrix'_mulVec {n R : Type _} [Fintype n] [CommSemiring R] [DecidableEq n]
    (x : (n → R) →ₗ[R] n → R) (y : n → R) : x.toMatrix'.mulVec y = x y := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

def LinearEquiv.toInvertibleMatrix {n R : Type _} [CommSemiring R] [Fintype n] [DecidableEq n]
    (x : (n → R) ≃ₗ[R] n → R) : Invertible (x : (n → R) →ₗ[R] n → R).toMatrix' := by
  refine' Invertible.mk (x.symm : (n → R) →ₗ[R] n → R).toMatrix' _ _ <;>
    simp only [Matrix.hMul_eq_hMul, ← LinearMap.toMatrix'_mul, LinearMap.mul_eq_comp,
      LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]

theorem Matrix.transposeAlgEquiv_symm_op_apply {n R α : Type _} [CommSemiring R] [CommSemiring α]
    [Fintype n] [DecidableEq n] [Algebra R α] (x : Matrix n n α) :
    (Matrix.transposeAlgEquiv n R α).symm (MulOpposite.op x) = xᵀ := by
  simp_rw [Matrix.transposeAlgEquiv_symm_apply, AddEquiv.invFun_eq_symm, AddEquiv.symm_trans_apply,
    Matrix.transposeAddEquiv_symm, MulOpposite.opAddEquiv_symm_apply, MulOpposite.unop_op,
    Matrix.transposeAddEquiv_apply]

open Matrix

theorem Matrix.dotProduct_eq_trace {R n : Type _} [CommSemiring R] [StarRing R] [Fintype n]
    (x : n → R) (y : Matrix n n R) :
    star x ⬝ᵥ y.mulVec x = ((Matrix.col x ⬝ Matrix.row (star x))ᴴ ⬝ y).trace :=
  by
  simp_rw [trace_iff, dot_product, conj_transpose_mul, conj_transpose_row, conj_transpose_col,
    star_star, mul_apply, mul_vec, dot_product, col_apply, row_apply, Pi.star_apply,
    Fintype.univ_punit, Finset.sum_const, Finset.card_singleton, nsmul_eq_mul, algebraMap.coe_one,
    one_mul, Finset.mul_sum, mul_comm (x _), mul_comm _ (x _), ← mul_assoc, mul_comm]
  rw [Finset.sum_comm]

theorem forall_left_hMul {n R : Type _} [Fintype n] [DecidableEq n] [Semiring R]
    (x y : Matrix n n R) : x = y ↔ ∀ a : Matrix n n R, a * x = a * y :=
  by
  refine' ⟨fun h a => by rw [h], fun h => _⟩
  specialize h 1
  simp_rw [one_mul] at h
  exact h

