/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.MyMatrix.Basic
import Monlib.LinearAlgebra.TensorFinite

#align_import linear_algebra.kronecker_to_tensor

/-!
# Kronecker product to the tensor product

This file contains the definition of `tensor_to_kronecker` and `kronecker_to_tensor`, the linear equivalences between `⊗ₜ` and `⊗ₖ`.

-/


open scoped TensorProduct BigOperators Kronecker

section

variable {R m n : Type _} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def TensorProduct.toKronecker : Matrix m m R ⊗[R] Matrix n n R →ₗ[R] Matrix (m × n) (m × n) R
    where
  toFun x ij kl := (matrixEquivTensor _ _ _).symm x ij.2 kl.2 ij.1 kl.1
  map_add' x y := by simp_rw [AlgEquiv.map_add, DMatrix.add_apply]; rfl
  map_smul' r x :=
    by
    simp only [AlgEquiv.map_smul, Pi.smul_apply, Algebra.id.smul_eq_mul, RingHom.id_apply]
    rfl

theorem TensorProduct.toKronecker_apply (x : Matrix m m R) (y : Matrix n n R) :
    (x ⊗ₜ[R] y).toKronecker = x ⊗ₖ y :=
  by
  simp_rw [TensorProduct.toKronecker, LinearMap.coe_mk, matrixEquivTensor_apply_symm,
    Algebra.algebraMap_eq_smul_one, Matrix.map_apply, Matrix.hMul_eq_hMul, Matrix.mul_apply,
    Pi.smul_apply, Matrix.one_apply, smul_eq_mul, mul_boole, mul_ite, MulZeroClass.mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

def Matrix.kroneckerToTensorProduct : Matrix (m × n) (m × n) R →ₗ[R] Matrix m m R ⊗[R] Matrix n n R
    where
  toFun x := (matrixEquivTensor _ (Matrix m m R) n) fun i j k l => x (k, i) (l, j)
  map_add' x y := by simp_rw [DMatrix.add_apply, ← AlgEquiv.map_add]; rfl
  map_smul' r x := by
    simp_rw [Pi.smul_apply, ← AlgEquiv.map_smul, RingHom.id_apply]
    rfl

theorem TensorProduct.toKronecker_to_tensorProduct (x : Matrix m m R ⊗[R] Matrix n n R) :
    x.toKronecker.kroneckerToTensorProduct = x := by
  simp_rw [TensorProduct.toKronecker, Matrix.kroneckerToTensorProduct, LinearMap.coe_mk,
    AlgEquiv.apply_symm_apply]

theorem Matrix.kroneckerToTensorProduct_apply (x : Matrix m m R) (y : Matrix n n R) :
    (x ⊗ₖ y).kroneckerToTensorProduct = x ⊗ₜ[R] y := by
  rw [← TensorProduct.toKronecker_apply, TensorProduct.toKronecker_to_tensorProduct]

theorem Matrix.kroneckerToTensorProduct_toKronecker (x : Matrix (m × n) (m × n) R) :
    x.kroneckerToTensorProduct.toKronecker = x := by
  simp_rw [Matrix.kroneckerToTensorProduct, TensorProduct.toKronecker, LinearMap.coe_mk,
    AlgEquiv.symm_apply_apply, Prod.mk.eta]

open scoped Matrix

theorem TensorProduct.matrix_star {R m n : Type _} [Field R] [StarRing R] [Fintype m] [Fintype n]
    (x : Matrix m m R) (y : Matrix n n R) : star (x ⊗ₜ[R] y) = xᴴ ⊗ₜ yᴴ :=
  TensorProduct.star_tmul _ _

theorem TensorProduct.toKronecker_star {R m n : Type _} [IsROrC R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (x : Matrix m m R) (y : Matrix n n R) :
    star (x ⊗ₜ y).toKronecker = (star (x ⊗ₜ y)).toKronecker := by
  simp_rw [TensorProduct.matrix_star, TensorProduct.toKronecker_apply, Matrix.star_eq_conjTranspose,
    Matrix.kronecker_conjTranspose]

theorem Matrix.kroneckerToTensorProduct_star {R m n : Type _} [IsROrC R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (x : Matrix m m R) (y : Matrix n n R) :
    star (x ⊗ₖ y).kroneckerToTensorProduct = (star (x ⊗ₖ y)).kroneckerToTensorProduct := by
  simp only [Matrix.kroneckerToTensorProduct_apply, TensorProduct.matrix_star,
    Matrix.star_eq_conjTranspose, Matrix.kronecker_conjTranspose]

open Matrix

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem Matrix.kronecker_eq_sum_std_basis (x : Matrix (m × n) (m × n) R) :
    x = ∑ (i) (j) (k) (l), x (i, k) (j, l) • stdBasisMatrix i j 1 ⊗ₖ stdBasisMatrix k l 1 :=
  kmul_representation _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem TensorProduct.matrix_eq_sum_std_basis (x : Matrix m m R ⊗[R] Matrix n n R) :
    x =
      ∑ (i) (j) (k) (l),
        x.toKronecker (i, k) (j, l) • stdBasisMatrix i j 1 ⊗ₜ stdBasisMatrix k l 1 :=
  by
  rw [eq_comm]
  calc
    ∑ (i) (j) (k) (l),
          x.to_kronecker (i, k) (j, l) •
            std_basis_matrix i j (1 : R) ⊗ₜ std_basis_matrix k l (1 : R) =
        ∑ (i) (j) (k) (l),
          x.to_kronecker (i, k) (j, l) •
            (std_basis_matrix i j (1 : R) ⊗ₜ
                  std_basis_matrix k l (1 : R)).toKronecker.kroneckerToTensorProduct :=
      by simp_rw [TensorProduct.toKronecker_to_tensorProduct]
    _ =
        ∑ (i) (j) (k) (l),
          x.to_kronecker (i, k) (j, l) •
            (std_basis_matrix i j (1 : R) ⊗ₖ
                std_basis_matrix k l (1 : R)).kroneckerToTensorProduct :=
      by simp_rw [TensorProduct.toKronecker_apply]
    _ =
        (∑ (i) (j) (k) (l),
            x.to_kronecker (i, k) (j, l) •
              std_basis_matrix i j (1 : R) ⊗ₖ
                std_basis_matrix k l (1 : R)).kroneckerToTensorProduct :=
      by simp_rw [map_sum, SMulHomClass.map_smul]
    _ = x.to_kronecker.kronecker_to_tensor_product := by rw [← Matrix.kronecker_eq_sum_std_basis]
    _ = x := TensorProduct.toKronecker_to_tensorProduct _

theorem TensorProduct.toKronecker_hMul (x y : Matrix m m R ⊗[R] Matrix n n R) :
    (x * y).toKronecker = x.toKronecker ⬝ y.toKronecker :=
  by
  nth_rw_lhs 1 [x.matrix_eq_sum_std_basis]
  nth_rw_lhs 1 [y.matrix_eq_sum_std_basis]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, map_sum, SMulHomClass.map_smul,
    Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.toKronecker_apply, mul_eq_mul,
    Matrix.mul_kronecker_mul, ← mul_eq_mul, ← smul_mul_smul, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← x.to_kronecker.kronecker_eq_sum_std_basis, ← y.to_kronecker.kronecker_eq_sum_std_basis]

theorem Matrix.kroneckerToTensorProduct_hMul (x y : Matrix m m R) (z w : Matrix n n R) :
    (x ⊗ₖ z ⬝ y ⊗ₖ w).kroneckerToTensorProduct =
      (x ⊗ₖ z).kroneckerToTensorProduct * (y ⊗ₖ w).kroneckerToTensorProduct :=
  by
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.kroneckerToTensorProduct_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Matrix.hMul_eq_hMul]

@[simps]
def tensorToKronecker : Matrix m m R ⊗[R] Matrix n n R ≃ₐ[R] Matrix (m × n) (m × n) R
    where
  toFun := TensorProduct.toKronecker
  invFun := Matrix.kroneckerToTensorProduct
  left_inv := TensorProduct.toKronecker_to_tensorProduct
  right_inv := kroneckerToTensorProduct_toKronecker
  map_add' := LinearMap.map_add' _
  map_mul' := TensorProduct.toKronecker_hMul
  commutes' r := by
    simp_rw [Algebra.algebraMap_eq_smul_one, SMulHomClass.map_smul]
    rw [Algebra.TensorProduct.one_def, TensorProduct.toKronecker_apply, one_kronecker_one]

def kroneckerToTensor : Matrix (m × n) (m × n) R ≃ₐ[R] Matrix m m R ⊗[R] Matrix n n R :=
  tensorToKronecker.symm

theorem kroneckerToTensor_toLinearMap_eq :
    (kroneckerToTensor : Matrix (n × m) (n × m) R ≃ₐ[R] _).toLinearMap =
      (kroneckerToTensorProduct : Matrix (n × m) (n × m) R →ₗ[R] Matrix n n R ⊗[R] Matrix m m R) :=
  rfl

theorem tensorToKronecker_toLinearMap_eq :
    ((@tensorToKronecker R m n _ _ _ _ _ : Matrix m m R ⊗[R] Matrix n n R ≃ₐ[R] _).toLinearMap :
        Matrix m m R ⊗[R] Matrix n n R →ₗ[R] Matrix (m × n) (m × n) R) =
      (TensorProduct.toKronecker : Matrix m m R ⊗[R] Matrix n n R →ₗ[R] Matrix (m × n) (m × n) R) :=
  rfl

end
