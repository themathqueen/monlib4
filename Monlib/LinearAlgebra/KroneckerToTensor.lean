/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Matrix.Basic
import Monlib.LinearAlgebra.TensorProduct.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Kronecker product to the tensor product

This file contains the definition of `tensor_toKronecker` and `kronecker_to_tensor`, the linear equivalences between `⊗ₜ` and `⊗ₖ`.

-/


open scoped TensorProduct BigOperators Kronecker

section

variable {R m n : Type _} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

-- set_option synthInstance.maxHeartbeats 0 in
noncomputable def TensorProduct.toKronecker : Matrix m m R ⊗[R] Matrix n n R →ₗ[R] Matrix (m × n) (m × n) R
    where
  toFun x ij kl := (matrixEquivTensor _ _ _).symm x ij.2 kl.2 ij.1 kl.1
  map_add' x y := by simp_rw [_root_.map_add, Matrix.add_apply]; rfl
  map_smul' r x :=
    by
    simp only [_root_.map_smul (matrixEquivTensor n R (Matrix m m R)).symm,
      Matrix.smul_apply, Algebra.id.smul_eq_mul, RingHom.id_apply]
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

set_option synthInstance.maxHeartbeats 0 in
noncomputable def Matrix.kroneckerToTensorProduct : Matrix (m × n) (m × n) R →ₗ[R] Matrix m m R ⊗[R] Matrix n n R
    where
  toFun x := (matrixEquivTensor n R (Matrix m m R)) fun i j k l => x (k, i) (l, j)
  map_add' x y := by simp_rw [Matrix.add_apply, ← _root_.map_add]; rfl
  map_smul' r x := by
    simp_rw [Matrix.smul_apply, ← _root_.map_smul (matrixEquivTensor n R (Matrix m m R)),
      RingHom.id_apply]
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

set_option synthInstance.maxHeartbeats 22296 in
theorem TensorProduct.toKronecker_star {R m n : Type _} [Field R] [StarRing R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (x : Matrix m m R ⊗[R] Matrix n n R) :
    star (toKronecker x) = toKronecker (star x) := by
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset x
  simp only [map_sum, star_sum,
    TensorProduct.matrix_star, TensorProduct.toKronecker_apply, Matrix.star_eq_conjTranspose,
    Matrix.kronecker_conjTranspose]

open Matrix

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem Matrix.kronecker_eq_sum_std_basis (x : Matrix (m × n) (m × n) R) :
    x = ∑ i, ∑ j, ∑ k, ∑ l, x (i, k) (j, l) • single i j 1 ⊗ₖ single k l 1 :=
  kmul_representation _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem TensorProduct.matrix_eq_sum_std_basis (x : Matrix m m R ⊗[R] Matrix n n R) :
    x =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (toKronecker x) (i, k) (j, l) • single i j 1 ⊗ₜ single k l 1 :=
  by
  rw [eq_comm]
  calc
    ∑ i, ∑ j, ∑ k, ∑ l,
          (toKronecker x) (i, k) (j, l) •
            single i j (1 : R) ⊗ₜ single k l (1 : R) =
        ∑ i, ∑ j, ∑ k, ∑ l,
          (toKronecker x) (i, k) (j, l) •
            kroneckerToTensorProduct (toKronecker (single i j (1 : R) ⊗ₜ
                  single k l (1 : R))) :=
      by simp_rw [TensorProduct.toKronecker_to_tensorProduct]
    _ =
        ∑ i, ∑ j, ∑ k, ∑ l,
          toKronecker x (i, k) (j, l) •
            kroneckerToTensorProduct (single i j (1 : R) ⊗ₖ
                single k l (1 : R)) :=
      by simp_rw [TensorProduct.toKronecker_apply]
    _ =
        kroneckerToTensorProduct (∑ i, ∑ j, ∑ k, ∑ l,
            toKronecker x (i, k) (j, l) •
              single i j (1 : R) ⊗ₖ
                single k l (1 : R)) :=
      by simp_rw [map_sum, _root_.map_smul]
    _ = kroneckerToTensorProduct (toKronecker x) := by rw [← Matrix.kronecker_eq_sum_std_basis]
    _ = x := TensorProduct.toKronecker_to_tensorProduct _

-- set_option maxHeartbeats 900000 in
theorem TensorProduct.toKronecker_hMul (x y : Matrix m m R ⊗[R] Matrix n n R) :
    toKronecker (x * y) = toKronecker x * toKronecker y :=
x.induction_on
 (by simp only [zero_mul, map_zero])
 (y.induction_on
  (by simp only [mul_zero, map_zero, implies_true])
  (λ _ _ _ _ => by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, toKronecker_apply, Matrix.mul_kronecker_mul])
  (λ _ _ h1 h2 _ _ => by simp only [_root_.map_add, h1, h2, mul_add]))
  (λ _ _ h1 h2 => by simp only [_root_.map_add, add_mul, h1, h2])

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

theorem Matrix.kroneckerToTensorProduct_star {R m n : Type _} [Field R] [StarRing R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (x : Matrix (m × n) (m × n) R) :
    star (kroneckerToTensorProduct x) = kroneckerToTensorProduct (star x) := by
  apply_fun TensorProduct.toKronecker using AlgEquiv.injective tensorToKronecker
  simp only [← TensorProduct.toKronecker_star, kroneckerToTensorProduct_toKronecker]

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
