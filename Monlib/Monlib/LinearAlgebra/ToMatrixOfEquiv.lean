/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyMatrix.Basic
import LinearAlgebra.InnerAut
import LinearAlgebra.MyMatrix.Reshape

#align_import linear_algebra.to_matrix_of_equiv

/-!

# to_matrix_of_equiv

This defines the identification $L(M_{n \times m})\cong_{a} M_{n \times m}$
  (see `linear_map.to_matrix_of_alg_equiv`; also see `matrix.to_lin_of_alg_equiv`).

-/


variable {R I J 𝕜 : Type _} [Fintype I] [Fintype J] [IsROrC 𝕜] [CommSemiring R] [DecidableEq I]
  [DecidableEq J]

open scoped BigOperators

open Matrix

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- the star-algebraic isomorphism from `E →ₗ[𝕜] E` to the matrix ring `M_n(𝕜)` given by
  the orthonormal basis `b` on `E` -/
noncomputable def OrthonormalBasis.toMatrix {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) : (E →ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜
    where
  toFun x k p := inner (b k) (x (b p))
  invFun x := ∑ (i) (j), x i j • (rankOne (b i) (b j) : E →L[𝕜] E)
  map_add' x y := by simp only [LinearMap.add_apply, inner_add_right]; rfl
  map_smul' r x := by simp only [LinearMap.smul_apply, inner_smul_right]; rfl
  map_mul' x y := by ext1;
    simp only [LinearMap.mul_apply, mul_eq_mul, Matrix.mul_apply, ← LinearMap.adjoint_inner_left x,
      OrthonormalBasis.sum_inner_mul_inner]
  map_star' x := by ext1;
    simp only [star_eq_conj_transpose, conj_transpose_apply, LinearMap.star_eq_adjoint,
      LinearMap.adjoint_inner_right, IsROrC.star_def, inner_conj_symm]
  right_inv x := by
    ext1;
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      rankOne_apply, inner_sum, smul_smul, inner_smul_right]
    simp only [orthonormal_iff_ite.mp b.orthonormal, mul_boole, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  left_inv x := by
    ext1;
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      rankOne_apply, ← LinearMap.adjoint_inner_left x, smul_smul, ← Finset.sum_smul,
      OrthonormalBasis.sum_inner_mul_inner]
    simp_rw [LinearMap.adjoint_inner_left, ← OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.sum_repr]

theorem OrthonormalBasis.toMatrix_apply {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) (x : E →ₗ[𝕜] E) (i j : n) :
    b.toMatrix x i j = inner (b i) (x (b j)) :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem OrthonormalBasis.toMatrix_symm_apply {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) (x : Matrix n n 𝕜) :
    b.toMatrix.symm x = ∑ (i) (j), x i j • (rankOne (b i) (b j) : E →L[𝕜] E) :=
  rfl

theorem OrthonormalBasis.toMatrix_symm_apply' {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) (x : Matrix n n 𝕜) :
    b.toMatrix.symm x = b.repr.symm.conj (mulVecLin x) :=
  by
  ext1 a
  simp only [LinearEquiv.conj_apply, LinearEquiv.conj_apply_apply,
    LinearIsometryEquiv.toLinearEquiv_symm, LinearIsometryEquiv.symm_symm]
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    mul_vec_lin, LinearMap.coe_mk, OrthonormalBasis.toMatrix_symm_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, ContinuousLinearMap.coe_coe, rankOne_apply, smul_smul, mul_comm (x _ _), ←
    smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, ← OrthonormalBasis.repr_apply_apply]
  have : ∀ i j, x i j = x.mul_vec (b.repr (b j)) i := by
    simp_rw [mul_vec, dot_product, OrthonormalBasis.repr_self, EuclideanSpace.single_apply,
      mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true, eq_self_iff_true, forall₂_true_iff]
  simp_rw [this, OrthonormalBasis.sum_repr_symm, ← SMulHomClass.map_smul, ← mul_vec_smul_assoc, ←
    LinearIsometryEquiv.map_smul, ← map_sum, ← mul_vec_sum, ← map_sum, OrthonormalBasis.sum_repr]

theorem orthonormalBasis_toMatrix_eq_basis_toMatrix {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) : LinearMap.toMatrixAlgEquiv b.toBasis = b.toMatrix.toAlgEquiv :=
  by
  ext
  simp_rw [StarAlgEquiv.coe_toAlgEquiv, OrthonormalBasis.toMatrix_apply,
    LinearMap.toMatrixAlgEquiv_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]

noncomputable def EuclideanSpace.orthonormalBasis (n 𝕜 : Type _) [IsROrC 𝕜] [Fintype n]
    [DecidableEq n] : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  by
  refine' Basis.toOrthonormalBasis (Pi.basisFun 𝕜 n) _
  rw [orthonormal_iff_ite]
  intro x y
  simp_rw [inner, Pi.basisFun_apply, LinearMap.coe_stdBasis, Pi.single, Function.update_apply,
    starRingEnd_apply, star_ite, Pi.zero_apply, star_one, star_zero, boole_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem EuclideanSpace.orthonormalBasis.repr_eq_one {n : Type _} [Fintype n] [DecidableEq n] :
    (EuclideanSpace.orthonormalBasis n 𝕜 : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)).repr = 1 :=
  rfl

theorem LinearIsometryEquiv.toLinearEquiv_one {R E : Type _} [_inst_1 : Semiring R]
    [_inst_25 : SeminormedAddCommGroup E] [_inst_29 : Module R E] :
    (1 : E ≃ₗᵢ[R] E).toLinearEquiv = 1 :=
  rfl

theorem LinearEquiv.one_symm {R E : Type _} [Semiring R] [AddCommMonoid E] [Module R E] :
    (1 : E ≃ₗ[R] E).symm = 1 :=
  rfl

theorem LinearEquiv.toLinearMap_one {R E : Type _} [Semiring R] [AddCommMonoid E] [Module R E] :
    (1 : E ≃ₗ[R] E).toLinearMap = 1 :=
  rfl

theorem LinearEquiv.refl_conj {R E : Type _} [CommSemiring R] [AddCommMonoid E] [Module R E] :
    (LinearEquiv.refl R E).conj = 1 := by
  ext
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.refl_apply, LinearEquiv.refl_symm]
  rfl

theorem LinearEquiv.conj_hMul {R E F : Type _} [CommSemiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R E] [Module R F] (f : E ≃ₗ[R] F) (x y : Module.End R E) :
    f.conj (x * y) = f.conj x * f.conj y := by
  simp only [LinearMap.mul_eq_comp, LinearEquiv.conj_comp]

theorem LinearEquiv.conj_apply_one {R E F : Type _} [CommSemiring R] [AddCommMonoid E]
    [AddCommMonoid F] [Module R E] [Module R F] (f : E ≃ₗ[R] F) : f.conj 1 = 1 :=
  LinearEquiv.conj_id _

theorem LinearEquiv.conj_one {R E : Type _} [CommSemiring R] [AddCommMonoid E] [Module R E] :
    (1 : E ≃ₗ[R] E).conj = 1 := by
  ext
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rfl

theorem LinearEquiv.one_apply {R E : Type _} [CommSemiring R] [AddCommMonoid E] [Module R E]
    (x : E) : (1 : E ≃ₗ[R] E) x = x :=
  rfl

theorem OrthonormalBasis.std_toMatrix {n : Type _} [Fintype n] [DecidableEq n] :
    (@OrthonormalBasis.toMatrix 𝕜 _ _ _ _ _ _ _ (@EuclideanSpace.instFiniteDimensional n 𝕜 _ _)
              (EuclideanSpace.orthonormalBasis n 𝕜 :
                OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n))).symm.toAlgEquiv.toLinearEquiv =
      toEuclideanLin :=
  by
  ext1
  rw [AlgEquiv.toLinearEquiv_apply, StarAlgEquiv.coe_toAlgEquiv,
    OrthonormalBasis.toMatrix_symm_apply', EuclideanSpace.orthonormalBasis.repr_eq_one, ←
    LinearIsometryEquiv.toLinearEquiv_symm, LinearIsometryEquiv.toLinearEquiv_one,
    LinearEquiv.one_symm, LinearEquiv.conj_one, LinearEquiv.one_apply]
  rfl

theorem Matrix.stdBasis_repr_eq_reshape : (Matrix.stdBasis R I J).equivFun = reshape :=
  by
  ext x ij
  simp_rw [Basis.equivFun_apply]
  rw [Basis.repr_apply_eq]
  · intro x y
    simp_rw [map_add]
  · intro c x
    simp_rw [SMulHomClass.map_smul]
  · intro i
    ext1
    simp_rw [reshape_apply, Matrix.stdBasis, Basis.reindex_apply, Pi.basis_apply]
    simp only [Pi.basisFun_apply, LinearMap.stdBasis_apply, Function.update_apply, Pi.zero_apply]
    simp only [ite_apply, Pi.zero_apply, Function.update_apply, Finsupp.single_apply, ← ite_and,
      @eq_comm _ i x_1, Equiv.sigmaEquivProd_symm_apply]
    congr
    nth_rw_lhs 1 [← Prod.eq_iff_fst_eq_snd_eq]

def LinearEquiv.innerConj {R E F : Type _} [CommSemiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R E] [Module R F] (ϱ : E ≃ₗ[R] F) : (E →ₗ[R] E) ≃ₐ[R] F →ₗ[R] F :=
  by
  apply AlgEquiv.ofLinearEquiv ϱ.conj (LinearEquiv.conj_hMul _)
  intro r
  simp only [Algebra.algebraMap_eq_smul_one, SMulHomClass.map_smul, LinearEquiv.conj_apply_one]

namespace LinearMap

open scoped Matrix ComplexConjugate BigOperators

open IsROrC Matrix

theorem toMatrix_stdBasis_stdBasis {I J K L : Type _} [Fintype I] [Fintype J] [Fintype K]
    [Fintype L] [DecidableEq I] [DecidableEq J] (x : Matrix I J R →ₗ[R] Matrix K L R) :
    toMatrix (Matrix.stdBasis R I J) (Matrix.stdBasis R K L) x =
      ((reshape : Matrix K L R ≃ₗ[R] _).toLinearMap ∘ₗ
          x ∘ₗ (reshape : Matrix I J R ≃ₗ[R] _).symm.toLinearMap).toMatrix' :=
  rfl

theorem toLin_stdBasis_stdBasis {I J K L : Type _} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [DecidableEq I] [DecidableEq J] (x : Matrix (K × L) (I × J) R) :
    (toLin (Matrix.stdBasis R I J) (Matrix.stdBasis R K L)) x =
      (reshape : Matrix K L R ≃ₗ[R] _).symm.toLinearMap ∘ₗ
        x.toLin' ∘ₗ (reshape : Matrix I J R ≃ₗ[R] _).toLinearMap :=
  rfl

def toMatrixOfAlgEquiv : (Matrix I J R →ₗ[R] Matrix I J R) ≃ₐ[R] Matrix (I × J) (I × J) R :=
  (reshape : Matrix I J R ≃ₗ[R] _).innerConj.trans toMatrixAlgEquiv'

theorem toMatrixOfAlgEquiv_apply (x : Matrix I J R →ₗ[R] Matrix I J R) :
    x.toMatrixOfAlgEquiv =
      ((reshape : Matrix I J R ≃ₗ[R] _).toLinearMap ∘ₗ
          x ∘ₗ (reshape : Matrix I J R ≃ₗ[R] _).symm.toLinearMap).toMatrixAlgEquiv' :=
  rfl

theorem toMatrixOfAlgEquiv_symm_apply (x : Matrix (I × J) (I × J) R) :
    toMatrixOfAlgEquiv.symm x =
      (reshape : Matrix I J R ≃ₗ[R] _).symm.toLinearMap ∘ₗ
        toMatrixAlgEquiv'.symm x ∘ₗ (reshape : Matrix I J R ≃ₗ[R] _).toLinearMap :=
  rfl

theorem toMatrixOfAlgEquiv_apply' (x : Matrix I J R →ₗ[R] Matrix I J R) (ij kl : I × J) :
    x.toMatrixOfAlgEquiv ij kl = x (stdBasisMatrix kl.1 kl.2 (1 : R)) ij.1 ij.2 :=
  by
  simp_rw [to_matrix_of_alg_equiv_apply, to_matrix_alg_equiv'_apply, LinearMap.comp_apply,
    LinearEquiv.toLinearMap_eq_coe, LinearEquiv.coe_coe, reshape_apply, std_basis_matrix, ←
    Prod.mk.inj_iff, Prod.mk.eta, eq_comm]
  rfl

end LinearMap

namespace Matrix

def toLinOfAlgEquiv : Matrix (I × J) (I × J) R ≃ₐ[R] Matrix I J R →ₗ[R] Matrix I J R :=
  LinearMap.toMatrixOfAlgEquiv.symm

theorem toLinOfAlgEquiv_apply (x : Matrix (I × J) (I × J) R) (y : Matrix I J R) :
    x.toLinOfAlgEquiv y =
      (reshape : Matrix I J R ≃ₗ[R] I × J → R).symm (x.toLinAlgEquiv' (reshape y)) :=
  rfl

def rankOneStdBasis {I J : Type _} [DecidableEq I] [DecidableEq J] (ij kl : I × J) (r : R) :
    Matrix I J R →ₗ[R] Matrix I J R
    where
  toFun x := stdBasisMatrix ij.1 ij.2 (r • r • x kl.1 kl.2)
  map_add' x y := by simp_rw [Pi.add_apply, smul_add, std_basis_matrix_add]
  map_smul' r x := by
    simp_rw [RingHom.id_apply, Pi.smul_apply, smul_std_basis_matrix, smul_smul, mul_rotate']

theorem rankOneStdBasis_apply {I J : Type _} [DecidableEq I] [DecidableEq J] (ij kl : I × J) (r : R)
    (x : Matrix I J R) :
    rankOneStdBasis ij kl r x = stdBasisMatrix ij.1 ij.2 (r • r • x kl.1 kl.2) :=
  rfl

open scoped BigOperators

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (ij kl) -/
theorem toLinOfAlgEquiv_eq (x : Matrix (I × J) (I × J) R) :
    x.toLinOfAlgEquiv = ∑ (ij : I × J) (kl : I × J), x ij kl • rankOneStdBasis ij kl (1 : R) := by
  simp_rw [LinearMap.ext_iff, ← ext_iff, to_lin_of_alg_equiv_apply, reshape_symm_apply,
    LinearMap.sum_apply, Finset.sum_apply, to_lin_alg_equiv'_apply, mul_vec, dot_product,
    reshape_apply, LinearMap.smul_apply, Pi.smul_apply, rank_one_std_basis_apply, std_basis_matrix,
    smul_ite, ← Prod.mk.inj_iff, Prod.mk.eta, one_smul, smul_zero, smul_eq_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    eq_self_iff_true, forall₃_true_iff]

-- MOVE:
theorem toLinOfAlgEquiv_toMatrixOfAlgEquiv (x : Matrix (I × J) (I × J) R) :
    x.toLinOfAlgEquiv.toMatrixOfAlgEquiv = x := by
  rw [to_lin_of_alg_equiv, AlgEquiv.apply_symm_apply]

end Matrix

open Matrix

variable {n : Type _} [Fintype n] [DecidableEq n]

-- MOVE:
theorem LinearMap.toMatrixOfAlgEquiv_toLinOfAlgEquiv (x : Matrix I J R →ₗ[R] Matrix I J R) :
    x.toMatrixOfAlgEquiv.toLinOfAlgEquiv = x := by
  rw [to_lin_of_alg_equiv, AlgEquiv.symm_apply_apply]

open scoped Kronecker Matrix

theorem innerAut_coord (U : unitaryGroup n 𝕜) : (innerAut U).toMatrixOfAlgEquiv = U ⊗ₖ Uᴴᵀ :=
  by
  ext1
  simp_rw [LinearMap.toMatrixOfAlgEquiv_apply', inner_aut_apply', mul_apply, std_basis_matrix,
    mul_ite, mul_one, MulZeroClass.mul_zero, Finset.sum_mul, ite_mul, MulZeroClass.zero_mul,
    ite_and, ← unitary_group.star_coe_eq_coe_star, star_apply, kronecker_map_apply, conj_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem Matrix.innerAut_coord (U : unitaryGroup n 𝕜) (ij kl : n × n) :
    (innerAut U).toMatrixOfAlgEquiv ij kl = U ij.1 kl.1 * star (U ij.2 kl.2) := by
  rw [innerAut_coord]; rfl

theorem innerAut_inv_coord (U : unitaryGroup n ℂ) (ij kl : n × n) :
    (innerAut U⁻¹).toMatrixOfAlgEquiv ij kl = U kl.2 ij.2 * star (U kl.1 ij.1) := by
  simp_rw [innerAut_coord, unitary_group.inv_apply, star_eq_conj_transpose, kronecker_map_apply,
    conj_apply, conj_transpose_apply, star_star, mul_comm]

