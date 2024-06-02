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

This file contains the definition of `tensor_toKronecker` and `kronecker_to_tensor`, the linear equivalences between `⊗ₜ` and `⊗ₖ`.

-/


open scoped TensorProduct BigOperators Kronecker

section

variable {R m n : Type _} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

noncomputable def TensorProduct.toKronecker : Matrix m m R ⊗[R] Matrix n n R →ₗ[R] Matrix (m × n) (m × n) R
    where
  toFun x ij kl := (matrixEquivTensor _ _ _).symm x ij.2 kl.2 ij.1 kl.1
  map_add' x y := by simp_rw [AlgEquiv.map_add, Matrix.add_apply]; rfl
  map_smul' r x :=
    by
    simp only [AlgEquiv.map_smul, Pi.smul_apply, Algebra.id.smul_eq_mul, RingHom.id_apply]
    rfl

theorem TensorProduct.toKronecker_apply (x : Matrix m m R) (y : Matrix n n R) :
    toKronecker (x ⊗ₜ[R] y) = x ⊗ₖ y :=
  by
  simp_rw [TensorProduct.toKronecker, LinearMap.coe_mk]
  simp only [AddHom.coe_mk, matrixEquivTensor_apply_symm, Matrix.map_apply,
    Algebra.algebraMap_eq_smul_one, Matrix.mul_apply,
    Pi.smul_apply, Matrix.one_apply, smul_eq_mul, mul_boole, mul_ite, MulZeroClass.mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.kroneckerMap, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, mul_one]
  rfl

noncomputable def Matrix.kroneckerToTensorProduct : Matrix (m × n) (m × n) R →ₗ[R] Matrix m m R ⊗[R] Matrix n n R
    where
  toFun x := (matrixEquivTensor _ (Matrix m m R) n) fun i j k l => x (k, i) (l, j)
  map_add' x y := by simp_rw [Matrix.add_apply, ← AlgEquiv.map_add]; rfl
  map_smul' r x := by
    simp_rw [Matrix.smul_apply, ← AlgEquiv.map_smul, RingHom.id_apply]
    rfl

theorem TensorProduct.toKronecker_to_tensorProduct (x : Matrix m m R ⊗[R] Matrix n n R) :
    Matrix.kroneckerToTensorProduct (toKronecker x) = x := by
  simp_rw [TensorProduct.toKronecker, Matrix.kroneckerToTensorProduct, LinearMap.coe_mk,
    AddHom.coe_mk, AlgEquiv.apply_symm_apply]

theorem Matrix.kroneckerToTensorProduct_apply (x : Matrix m m R) (y : Matrix n n R) :
    kroneckerToTensorProduct (x ⊗ₖ y) = x ⊗ₜ[R] y := by
  rw [← TensorProduct.toKronecker_apply, TensorProduct.toKronecker_to_tensorProduct]

theorem Matrix.kroneckerToTensorProduct_toKronecker (x : Matrix (m × n) (m × n) R) :
    TensorProduct.toKronecker (kroneckerToTensorProduct x) = x := by
  simp_rw [Matrix.kroneckerToTensorProduct, TensorProduct.toKronecker, LinearMap.coe_mk,
    AddHom.coe_mk, AlgEquiv.symm_apply_apply]

open scoped Matrix

theorem TensorProduct.matrix_star {R m n : Type _} [Field R] [StarRing R] [Fintype m] [Fintype n]
    (x : Matrix m m R) (y : Matrix n n R) : star (x ⊗ₜ[R] y) = xᴴ ⊗ₜ yᴴ :=
  TensorProduct.star_tmul _ _

theorem TensorProduct.toKronecker_star {R m n : Type _} [RCLike R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (x : Matrix m m R) (y : Matrix n n R) :
    star (toKronecker (x ⊗ₜ y)) = toKronecker (star (x ⊗ₜ y)) := by
  simp_rw [TensorProduct.matrix_star, TensorProduct.toKronecker_apply, Matrix.star_eq_conjTranspose,
    Matrix.kronecker_conjTranspose]

theorem Matrix.kroneckerToTensorProduct_star {R m n : Type _} [RCLike R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (x : Matrix m m R) (y : Matrix n n R) :
    star (kroneckerToTensorProduct (x ⊗ₖ y)) = kroneckerToTensorProduct (star (x ⊗ₖ y)) := by
  simp only [Matrix.kroneckerToTensorProduct_apply, TensorProduct.matrix_star,
    Matrix.star_eq_conjTranspose, Matrix.kronecker_conjTranspose]

open Matrix

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem Matrix.kronecker_eq_sum_std_basis (x : Matrix (m × n) (m × n) R) :
    x = ∑ i, ∑ j, ∑ k, ∑ l, x (i, k) (j, l) • stdBasisMatrix i j 1 ⊗ₖ stdBasisMatrix k l 1 :=
  kmul_representation _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem TensorProduct.matrix_eq_sum_std_basis (x : Matrix m m R ⊗[R] Matrix n n R) :
    x =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (toKronecker x) (i, k) (j, l) • stdBasisMatrix i j 1 ⊗ₜ stdBasisMatrix k l 1 :=
  by
  rw [eq_comm]
  calc
    ∑ i, ∑ j, ∑ k, ∑ l,
          (toKronecker x) (i, k) (j, l) •
            stdBasisMatrix i j (1 : R) ⊗ₜ stdBasisMatrix k l (1 : R) =
        ∑ i, ∑ j, ∑ k, ∑ l,
          (toKronecker x) (i, k) (j, l) •
            kroneckerToTensorProduct (toKronecker (stdBasisMatrix i j (1 : R) ⊗ₜ
                  stdBasisMatrix k l (1 : R))) :=
      by simp_rw [TensorProduct.toKronecker_to_tensorProduct]
    _ =
        ∑ i, ∑ j, ∑ k, ∑ l,
          toKronecker x (i, k) (j, l) •
            kroneckerToTensorProduct (stdBasisMatrix i j (1 : R) ⊗ₖ
                stdBasisMatrix k l (1 : R)) :=
      by simp_rw [TensorProduct.toKronecker_apply]
    _ =
        kroneckerToTensorProduct (∑ i, ∑ j, ∑ k, ∑ l,
            toKronecker x (i, k) (j, l) •
              stdBasisMatrix i j (1 : R) ⊗ₖ
                stdBasisMatrix k l (1 : R)) :=
      by simp_rw [map_sum, _root_.map_smul]
    _ = kroneckerToTensorProduct (toKronecker x) := by rw [← Matrix.kronecker_eq_sum_std_basis]
    _ = x := TensorProduct.toKronecker_to_tensorProduct _

set_option maxHeartbeats 500000 in
theorem TensorProduct.toKronecker_hMul (x y : Matrix m m R ⊗[R] Matrix n n R) :
    toKronecker (x * y) = toKronecker x * toKronecker y :=
  by
  nth_rw 1 [x.matrix_eq_sum_std_basis]
  nth_rw 1 [y.matrix_eq_sum_std_basis]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, map_sum]
  simp only [_root_.map_smul, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.toKronecker_apply, Matrix.mul_kronecker_mul, ← smul_mul_smul, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← x.toKronecker.kronecker_eq_sum_std_basis, ← y.toKronecker.kronecker_eq_sum_std_basis]

theorem Matrix.kroneckerToTensorProduct_hMul (x y : Matrix m m R) (z w : Matrix n n R) :
    kroneckerToTensorProduct (x ⊗ₖ z * y ⊗ₖ w) =
      kroneckerToTensorProduct (x ⊗ₖ z) * kroneckerToTensorProduct (y ⊗ₖ w) :=
  by
  simp_rw [← Matrix.mul_kronecker_mul, Matrix.kroneckerToTensorProduct_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

@[simps]
noncomputable def tensorToKronecker : Matrix m m R ⊗[R] Matrix n n R ≃ₐ[R] Matrix (m × n) (m × n) R
    where
  toFun := TensorProduct.toKronecker
  invFun := Matrix.kroneckerToTensorProduct
  left_inv := TensorProduct.toKronecker_to_tensorProduct
  right_inv := kroneckerToTensorProduct_toKronecker
  map_add' _ _ := map_add _ _ _
  map_mul' := TensorProduct.toKronecker_hMul
  commutes' r := by
    simp only [Algebra.TensorProduct.algebraMap_apply]
    simp_rw [Algebra.algebraMap_eq_smul_one]
    rw [TensorProduct.toKronecker_apply, smul_kronecker,
      one_kronecker_one]

@[simps!]
noncomputable def kroneckerToTensor : Matrix (m × n) (m × n) R ≃ₐ[R] Matrix m m R ⊗[R] Matrix n n R :=
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
