/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Monlib.LinearAlgebra.Ips.Pos
import Monlib.LinearAlgebra.Matrix.Basic
import Monlib.LinearAlgebra.End
import Monlib.LinearAlgebra.Ips.RankOne
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Monlib.Preq.Ites
import Monlib.Preq.RCLikeLe

#align_import linear_algebra.my_matrix.pos_eq_linear_map_is_positive

/-!

# the correspondence between matrix.pos_semidef and linear_map.is_positive

In this file, we show that
`x ∈ Mₙ` being positive semi-definite is equivalent to
`x.to_euclidean_lin.is_positive`

-/


-------------------------------
--copied from old mathlib
namespace Matrix

variable {𝕜 m n : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [RCLike 𝕜]

open scoped ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the linear map associated to the
 conjugate transpose of that matrix. -/
theorem conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    toLin' A.conjTranspose =
      @LinearMap.adjoint 𝕜 (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) _ _ _ _ _ _ _ (toLin' A) :=
Matrix.toEuclideanLin_conjTranspose_eq_adjoint _

end Matrix

-------------------------------
variable {n 𝕜 : Type _} [RCLike 𝕜]

open scoped Matrix ComplexOrder

alias Matrix.posSemidef_star_mul_self := Matrix.posSemidef_conjTranspose_mul_self
alias Matrix.posSemidef_mul_star_self := Matrix.posSemidef_self_mul_conjTranspose

theorem Matrix.toEuclideanLin_eq_piLp_linearEquiv [Fintype n] [DecidableEq n] (x : Matrix n n 𝕜) :
    Matrix.toEuclideanLin x =
      (toLin' x) :=
  rfl

lemma Matrix.of_isHermitian' [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
  (hx : x.IsHermitian) :
    ∀ x_1 : n → 𝕜, ↑(RCLike.re (Finset.sum Finset.univ fun i ↦
      (star x_1 i * Finset.sum Finset.univ fun x_2 ↦ x i x_2 * x_1 x_2))) =
          Finset.sum Finset.univ fun x_2 ↦ star x_1 x_2 * Finset.sum Finset.univ fun x_3 ↦ x x_2 x_3 * x_1 x_3 :=
  by
  simp_rw [← RCLike.conj_eq_iff_re]
  have : ∀ (x_1 : n → 𝕜),
    (Finset.sum Finset.univ fun i ↦ star x_1 i
      * Finset.sum Finset.univ fun x_2 ↦ x i x_2 * x_1 x_2)
      = ⟪(EuclideanSpace.equiv n 𝕜).symm x_1,
      (toEuclideanLin x) ((EuclideanSpace.equiv n 𝕜).symm x_1)⟫_𝕜 := λ x_1 => by
    calc (Finset.sum Finset.univ fun i ↦ star x_1 i
      * Finset.sum Finset.univ fun x_2 ↦ x i x_2 * x_1 x_2)
      = ⟪x_1, x *ᵥ x_1⟫_𝕜 := rfl
    _ = ⟪(EuclideanSpace.equiv n 𝕜).symm x_1, (EuclideanSpace.equiv n 𝕜).symm (x *ᵥ x_1)⟫_𝕜 := rfl
    _ = ⟪(EuclideanSpace.equiv n 𝕜).symm x_1,
      (toEuclideanLin x) ((EuclideanSpace.equiv n 𝕜).symm x_1)⟫_𝕜 := rfl
  simp_rw [this, inner_conj_symm, ← LinearMap.adjoint_inner_left,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hx.eq, forall_true_iff]

theorem Matrix.posSemidef_eq_linearMap_positive [Fintype n] [DecidableEq n] (x : Matrix n n 𝕜) :
    x.PosSemidef ↔ x.toEuclideanLin.IsPositive :=
  by
  simp_rw [LinearMap.IsPositive, ← Matrix.isHermitian_iff_isSymmetric, Matrix.PosSemidef,
    Matrix.toEuclideanLin_eq_piLp_linearEquiv, PiLp.inner_apply, RCLike.inner_apply, map_sum,
    ← RCLike.star_def, Matrix.dotProduct, Pi.star_apply, Matrix.mulVec,
    Matrix.dotProduct, @RCLike.nonneg_def' 𝕜, ← map_sum, ← Pi.star_apply]
  refine ⟨fun h => ⟨h.1, fun y => (h.2 _).2⟩,
    fun h => ⟨h.1, fun y => ⟨Matrix.of_isHermitian' h.1 _, (h.2 _)⟩⟩⟩

theorem Matrix.posSemidef_iff [Fintype n] [DecidableEq n] (x : Matrix n n 𝕜) :
    x.PosSemidef ↔ ∃ y : Matrix n n 𝕜, x = yᴴ * y :=
  by
  simp_rw [Matrix.posSemidef_eq_linearMap_positive,
    LinearMap.isPositive_iff_exists_adjoint_hMul_self,
    ← LinearEquiv.eq_symm_apply]
  have thisor : ∀ x y : (PiLp 2 fun _x : n => 𝕜) →ₗ[𝕜] (PiLp 2 fun _x : n => 𝕜),
    toEuclideanLin.symm (x * y) = (toEuclideanLin.symm x) * (toEuclideanLin.symm y) := λ x y => by
    calc toEuclideanLin.symm (x * y) = LinearMap.toMatrix' (x * y) := rfl
      _ = LinearMap.toMatrix' x * LinearMap.toMatrix' y := LinearMap.toMatrix'_mul _ _
      _ = toEuclideanLin.symm x * toEuclideanLin.symm y := rfl
  simp_rw [thisor]
  constructor
  . rintro ⟨S, rfl⟩
    let A := toEuclideanLin.symm S
    use A
    have : Aᴴ = (toEuclideanLin.symm (LinearMap.adjoint S)) := by
      simp_rw [LinearEquiv.eq_symm_apply, toEuclideanLin_conjTranspose_eq_adjoint, A,
        LinearEquiv.apply_symm_apply]
    rw [this]
  . rintro ⟨A, rfl⟩
    use toEuclideanLin A
    simp_rw [← toEuclideanLin_conjTranspose_eq_adjoint, LinearEquiv.symm_apply_apply]

local notation "⟪" x "," y "⟫_𝕜" => @inner 𝕜 _ _ x y

open scoped BigOperators

theorem Matrix.dotProduct_eq_inner {n : Type _} [Fintype n] (x y : n → 𝕜) :
    Matrix.dotProduct (star x) y = ∑ i : n, ⟪x i,y i⟫_𝕜 :=
  rfl

theorem Matrix.PosSemidef.invertible_iff_posDef {n : Type _} [Fintype n] [DecidableEq n]
    {x : Matrix n n 𝕜} (hx : x.PosSemidef) :
  Function.Bijective (toLin' x) ↔ x.PosDef :=
  by
  simp_rw [Matrix.PosDef, hx.1, true_and_iff]
  cases' (Matrix.posSemidef_iff x).mp hx with y hy
  constructor
  · intro h v hv
    rw [hy]
    have :
      (star v ⬝ᵥ (yᴴ * y) *ᵥ v) = (star (y *ᵥ v) ⬝ᵥ y *ᵥ v) := by
      simp_rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    simp_rw [this, Matrix.dotProduct, Pi.star_apply, RCLike.star_def, ← RCLike.inner_apply,
      inner_self_eq_norm_sq_to_K]
    clear this
    apply Finset.sum_pos'
    · simp_rw [Finset.mem_univ, forall_true_left]
      intro i
      norm_cast
      exact pow_two_nonneg _
    · simp_rw [Finset.mem_univ, true_and]
      suffices y *ᵥ v ≠ 0
        by
        simp_rw [ne_eq, Function.funext_iff, Pi.zero_apply] at this
        push_neg at this
        cases' this with j hj
        rw [← norm_ne_zero_iff] at hj
        use j
        norm_cast
        exact sq_pos_iff.mpr hj
      by_contra!
      apply hv
      apply_fun (toLin' x)
      · simp_rw [map_zero]
        rw [Matrix.mulVec_eq] at hy
        specialize hy v
        simp_rw [← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero] at hy
        rw [Matrix.toLin'_apply]
        exact hy
      · exact h.1
  · intro h
    by_contra!
    rw [Function.Bijective, ← LinearMap.injective_iff_surjective, and_self_iff,
      injective_iff_map_eq_zero] at this
    push_neg at this
    cases' this with a ha
    specialize h a ha.2
    rw [← Matrix.toLin'_apply, ha.1, Matrix.dotProduct_zero, lt_self_iff_false] at h
    exact h

theorem Matrix.isHermitian_self_hMul_conjTranspose {m n : Type*} [Fintype m] (A : Matrix m n 𝕜) :
    (Aᴴ * A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem Matrix.trace_star [Fintype n] {A : Matrix n n 𝕜} : star A.trace = Aᴴ.trace := by
  simp_rw [Matrix.trace, Matrix.diag, star_sum, Matrix.conjTranspose_apply]

theorem Matrix.nonneg_eigenvalues_of_posSemidef [Fintype n] [DecidableEq n] {μ : ℝ} {A : Matrix n n 𝕜}
    (hμ : Module.End.HasEigenvalue (toEuclideanLin A) ↑μ) (H : A.PosSemidef) : 0 ≤ μ :=
  by
  apply eigenvalue_nonneg_of_nonneg hμ
  simp_rw [Matrix.toEuclideanLin_eq_toLin, Matrix.toLin_apply, inner_sum, inner_smul_right,
    PiLp.basisFun_apply, WithLp.equiv_symm_single, EuclideanSpace.inner_single_right, one_mul]
  intro x
  have :
    (∑ x_1 : n, (A *ᵥ ⇑((PiLp.basisFun 2 𝕜 n).repr x)) x_1 * (starRingEnd 𝕜) (x x_1)) =
      (star x) ⬝ᵥ (A *ᵥ x) :=
    by
    simp_rw [mul_comm, Matrix.dotProduct]
    congr
  rw [this]
  exact (RCLike.nonneg_def.mp (H.2 _)).1

theorem Matrix.IsHermitian.nonneg_eigenvalues_of_posSemidef [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  Matrix.nonneg_eigenvalues_of_posSemidef (hA.1.eigenvalues_hasEigenvalue _) hA

noncomputable
def Matrix.invertible_of_bij_toLin' [Fintype n] [DecidableEq n] {Q : Matrix n n 𝕜}
  (h : Function.Bijective (toLin' Q)) :
    Invertible Q :=
  by
  have h : Invertible (toLin' Q) := by
    refine' IsUnit.invertible _
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective h.1
  refine' IsUnit.invertible _
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [← LinearMap.det_toLin']
  apply LinearMap.isUnit_det
  rw [← nonempty_invertible_iff_isUnit]
  exact Nonempty.intro h
lemma Matrix.bij_toLin'_of_invertible [Fintype n] [DecidableEq n] {Q : Matrix n n 𝕜}
  (h : Invertible Q) :
  Function.Bijective (toLin' Q) :=
  by
  simp_rw [Function.bijective_iff_has_inverse]
  use (toLin' ⅟ Q)
  simp only [Function.LeftInverse, Function.RightInverse, ← forall_and, ← toLin'_mul_apply,
    Invertible.invOf_mul_self, mul_invOf_self, toLin'_one, and_self, LinearMap.id_apply,
    forall_true_iff]

@[instance]
noncomputable def Matrix.PosDef.invertible [Fintype n] [DecidableEq n] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    Invertible Q :=
  by
  suffices Function.Bijective (toLin' Q) by exact Matrix.invertible_of_bij_toLin' this
  rw [Matrix.PosSemidef.invertible_iff_posDef hQ.posSemidef]
  exact hQ

theorem Matrix.mulVec_sum {n m k R : Type _} [NonUnitalNonAssocSemiring R] [Fintype n] [Fintype m] [Fintype k]
  (x : Matrix m n R) (y : k → n → R) :
    x.mulVec (∑ i : k, y i) = ∑ i : k, x.mulVec (y i) :=
  by
  ext
  simp only [Finset.sum_apply, Matrix.mulVec, Matrix.dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem Matrix.vecMul_sum {n m k R : Type _} [NonUnitalNonAssocSemiring R] [Fintype m] [Fintype n] [Fintype k]
  (x : Matrix n m R) (y : k → n → R) :
  (∑ i : k, y i) ᵥ* x = ∑ i : k, (y i) ᵥ* x :=
  by
  ext
  simp only [Finset.sum_apply, Matrix.vecMul, Matrix.dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

open Matrix

open scoped Matrix

theorem Matrix.toLin_piLp_eq_toLin' {n : Type _} [Fintype n] [DecidableEq n] :
    toLin (PiLp.basisFun 2 𝕜 n) (PiLp.basisFun 2 𝕜 n) = toLin' :=
  rfl

theorem Matrix.posSemidef_iff_eq_rankOne [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
        x =
          ∑ i : Fin m,
            LinearMap.toMatrix' (rankOne 𝕜 (v i) (v i)).toLinearMap :=
  by
  simp_rw [posSemidef_eq_linearMap_positive, LinearMap.isPositive_iff_eq_sum_rankOne,
    toEuclideanLin_eq_toLin, Matrix.toLin_piLp_eq_toLin', ← map_sum]
  constructor <;> rintro ⟨m, y, hy⟩ <;> refine' ⟨m, y, _⟩
  · rw [← hy]
    exact (LinearMap.toMatrix'_toLin' _).symm
  · rw [hy]
    exact (toLin'_toMatrix' _)

theorem Matrix.posSemidef_iff_eq_rankOne' [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → (n → 𝕜)),
        x = ∑ i : Fin m,
          LinearMap.toMatrix' (rankOne 𝕜 ((EuclideanSpace.equiv _ _).symm (v i)) ((EuclideanSpace.equiv _ _).symm (v i))).toLinearMap :=
Matrix.posSemidef_iff_eq_rankOne
theorem Matrix.posSemidef_iff_eq_rankOne'' [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : Type) (hm : Fintype m) (v : m → (n → 𝕜)),
        x =
          ∑ i : m,
            LinearMap.toMatrix' (rankOne 𝕜 ((EuclideanSpace.equiv _ _).symm (v i)) ((EuclideanSpace.equiv _ _).symm (v i))).toLinearMap :=
by
  rw [Matrix.posSemidef_iff_eq_rankOne']
  constructor
  . rintro ⟨m, v, rfl⟩
    exact ⟨Fin m, by infer_instance, v, rfl⟩
  . rintro ⟨m, hm, v, rfl⟩
    let v' : Fin (Fintype.card m) → (n → 𝕜) := fun i j => v ((Fintype.equivFin m).symm i) j
    use Fintype.card m, v'
    apply Finset.sum_bijective ((Fintype.equivFin m))
    . simp only [Multiset.bijective_iff_map_univ_eq_univ, Multiset.map_univ_val_equiv]
    . simp only [Finset.mem_univ, implies_true]
    . simp_rw [v', Finset.mem_univ, Equiv.symm_apply_apply, forall_true_left, implies_true]

theorem rankOne.EuclideanSpace.toEuclideanLin_symm {𝕜 : Type _} [RCLike 𝕜] {n m : Type _} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m]
    (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    toEuclideanLin.symm (rankOne 𝕜 x y).toLinearMap =
      col (x : n → 𝕜) * (col (y : m → 𝕜))ᴴ :=
  by
  simp_rw [← Matrix.ext_iff, toEuclideanLin_eq_toLin, toLin_symm, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, PiLp.basisFun_repr, PiLp.basisFun_apply,
    PiLp.smul_apply]
  have : ∀ j, (WithLp.equiv 2 (m → 𝕜)).symm (Pi.single j 1) = EuclideanSpace.single j 1 := λ j => rfl
  simp_rw [this, EuclideanSpace.inner_single_right, one_mul, conjTranspose_col, ← vecMulVec_eq,
    vecMulVec_apply, smul_eq_mul, Pi.star_apply, mul_comm]
  intro i j
  rfl

theorem rankOne.EuclideanSpace.toMatrix' {𝕜 : Type _} [RCLike 𝕜] {n m : Type _}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    LinearMap.toMatrix' ((rankOne 𝕜 x y).toLinearMap : (m → 𝕜) →ₗ[𝕜] (n → 𝕜)) =
      col (x : n → 𝕜) * (col (y : m → 𝕜))ᴴ :=
rankOne.EuclideanSpace.toEuclideanLin_symm _ _
theorem rankOne.Pi.toMatrix'' {𝕜 : Type _} [RCLike 𝕜] {n : Type _} [Fintype n]
    [DecidableEq n] (x y : n → 𝕜) :
    LinearMap.toMatrix' (((rankOne 𝕜 ((EuclideanSpace.equiv _ _).symm x) ((EuclideanSpace.equiv _ _).symm y)) : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n)
        : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)) =
      col (x : n → 𝕜) * (col (y : n → 𝕜))ᴴ :=
rankOne.EuclideanSpace.toEuclideanLin_symm _ _

/-- a matrix $x$ is positive semi-definite if and only if there exists vectors $(v_i)$ such that
  $\sum_i v_iv_i^*=x$  -/
theorem Matrix.posSemidef_iff_col_mul_conjTranspose_col [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
        x =
          ∑ i : Fin m, col (v i : n → 𝕜) * (col (v i : n → 𝕜))ᴴ :=
  by
  simp_rw [Matrix.posSemidef_iff_eq_rankOne, rankOne.EuclideanSpace.toMatrix']
theorem Matrix.posSemidef_iff_col_mul_conjTranspose_col' [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : Type) (hm : Fintype m) (v : m → EuclideanSpace 𝕜 n),
        x =
          ∑ i : m, col (v i : n → 𝕜) * (col (v i : n → 𝕜))ᴴ :=
by
simp_rw [Matrix.posSemidef_iff_eq_rankOne'', rankOne.EuclideanSpace.toMatrix']
rfl

theorem Matrix.posSemidef_iff_vecMulVec [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
  x.PosSemidef ↔ ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
    x = ∑ i : Fin m, vecMulVec (v i) (star (v i)) :=
by simp_rw [Matrix.posSemidef_iff_col_mul_conjTranspose_col, vecMulVec_eq, conjTranspose_col]
theorem Matrix.posSemidef_iff_vecMulVec' [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
  x.PosSemidef ↔ ∃ (m : Type) (hm : Fintype m) (v : m → EuclideanSpace 𝕜 n),
    x = ∑ i : m, vecMulVec (v i) (star (v i)) :=
by simp_rw [Matrix.posSemidef_iff_col_mul_conjTranspose_col', vecMulVec_eq, conjTranspose_col]

theorem vecMulVec_posSemidef [Fintype n] [DecidableEq n] (x : n → 𝕜) :
    (vecMulVec x (star x)).PosSemidef :=
  by
  rw [vecMulVec_eq, ← conjTranspose_col]
  exact Matrix.posSemidef_self_mul_conjTranspose _

lemma inner_self_nonneg' {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x : E} :
  0 ≤ ⟪x, x⟫_𝕜 :=
by
simp_rw [@RCLike.nonneg_def 𝕜, inner_self_nonneg, true_and, inner_self_im]

lemma inner_self_nonpos' {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x : E} :
  ⟪x, x⟫_𝕜 ≤ 0 ↔ x = 0 :=
by
simp_rw [@RCLike.nonpos_def 𝕜, inner_self_nonpos, inner_self_im, and_true]

section
variable {M₁ M₂ : Type _} [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [InnerProductSpace ℂ M₁]
  [InnerProductSpace ℂ M₂]

/-- we say a linear map $T \colon L(M_1) \to L(M_2)$ is a positive map
  if for all positive $x \in L(M_1)$, we also get $T(x)$ is positive  -/
def LinearMap.PositiveMap (T : (M₁ →ₗ[ℂ] M₁) →ₗ[ℂ] M₂ →ₗ[ℂ] M₂) : Prop :=
  ∀ x : M₁ →ₗ[ℂ] M₁, x.IsPositive → (T x).IsPositive

/-- a $^*$-homomorphism from $L(M_1)$ to $L(M_2)$ is a positive map -/
theorem LinearMap.PositiveMap.starHom [FiniteDimensional ℂ M₁] [FiniteDimensional ℂ M₂]
    (φ : StarAlgHom ℂ (M₁ →ₗ[ℂ] M₁) (M₂ →ₗ[ℂ] M₂)) :
    φ.toAlgHom.toLinearMap.PositiveMap := by
  intro x hx
  rcases(LinearMap.isPositive_iff_exists_adjoint_hMul_self x).mp hx with ⟨w, rfl⟩
  have : ∀ h, φ.toAlgHom.toLinearMap h = φ h := fun h => rfl
  simp_rw [LinearMap.IsPositive, LinearMap.IsSymmetric, this, _root_.map_mul, ←
    LinearMap.star_eq_adjoint, map_star, LinearMap.mul_apply, LinearMap.star_eq_adjoint,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, forall₂_true_iff,
    true_and_iff, inner_self_nonneg, forall_const]
end

/-- the identity is a positive definite matrix -/
theorem Matrix.posDefOne [Fintype n] [DecidableEq n] : (1 : Matrix n n 𝕜).PosDef :=
  by
  simp_rw [Matrix.PosDef, Matrix.IsHermitian, Matrix.conjTranspose_one,
    true_and_iff, Matrix.one_mulVec, Matrix.dotProduct_eq_inner, ← Matrix.vec_ne_zero]
  intro x h
  apply Finset.sum_pos'
  simp only [Finset.mem_univ, forall_true_left]
  intro i
  exact inner_self_nonneg'
  cases' h with i hi
  use i
  simp_rw [Finset.mem_univ, true_and_iff]
  simp_rw [ne_eq] at hi
  contrapose! hi
  simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.zero_lt_real] at hi
  push_neg at hi
  simp_rw [@norm_sq_eq_inner 𝕜] at hi
  rw [← @inner_self_nonpos' 𝕜, RCLike.nonpos_def, inner_self_im]
  exact ⟨hi, rfl⟩

-- /-- each eigenvalue of a positive definite matrix is positive -/
alias Matrix.PosDef.pos_eigenvalues := Matrix.PosDef.eigenvalues_pos

theorem Matrix.PosDef.pos_trace [Fintype n] [DecidableEq n] [Nonempty n] {x : Matrix n n 𝕜}
    (hx : x.PosDef) : 0 < RCLike.re x.trace :=
  by
  simp_rw [IsHermitian.trace_eq hx.1, RCLike.ofReal_re]
  apply Finset.sum_pos
  · exact fun _ _ => hx.pos_eigenvalues _
  · exact Finset.univ_nonempty

/-- the trace of a positive definite matrix is non-zero -/
theorem Matrix.PosDef.trace_ne_zero [Fintype n] [DecidableEq n] [Nonempty n] {x : Matrix n n 𝕜}
    (hx : x.PosDef) : x.trace ≠ 0 :=
  by
  rw [Matrix.IsHermitian.trace_eq hx.1]
  norm_num
  rw [← RCLike.ofReal_sum, RCLike.ofReal_eq_zero, Finset.sum_eq_zero_iff_of_nonneg _]
  · simp_rw [Finset.mem_univ, true_imp_iff]
    simp only [Classical.not_forall]
    let i : n := (Nonempty.some (by infer_instance))
    exact ⟨i,( NeZero.of_pos (Matrix.PosDef.pos_eigenvalues hx i)).out⟩
  · intros
    exact le_of_lt (Matrix.PosDef.pos_eigenvalues hx _)

open scoped ComplexOrder

lemma Matrix.toEuclideanLin_apply' {n : Type _} [Fintype n] [DecidableEq n] (x : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin x v = x.mulVec v := rfl

theorem PosSemidef.complex [Fintype n] [DecidableEq n] (x : Matrix n n ℂ) :
    x.PosSemidef ↔ ∀ y : n → ℂ, 0 ≤ star y ⬝ᵥ x.mulVec y :=
  by
  simp_rw [posSemidef_eq_linearMap_positive x, LinearMap.complex_isPositive,
    toEuclideanLin_apply', @RCLike.nonneg_def' ℂ]
  rfl

theorem StdBasisMatrix.sum_eq_one [Fintype n] [DecidableEq n] (a : 𝕜) : ∑ k : n, stdBasisMatrix k k a = a • 1 :=
  by
  simp_rw [← Matrix.ext_iff, Matrix.sum_apply, Matrix.smul_apply, stdBasisMatrix, one_apply, smul_ite,
    ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul, MulZeroClass.mul_zero,
    mul_one, forall₂_true_iff]

theorem stdBasisMatrix_hMul [Fintype n] [DecidableEq n] (i j k l : n) (a b : 𝕜) :
    stdBasisMatrix i j a * stdBasisMatrix k l b =
      ite (j = k) (1 : 𝕜) (0 : 𝕜) • stdBasisMatrix i l (a * b) :=
  by
  ext
  simp_rw [Matrix.mul_apply, stdBasisMatrix, ite_mul, MulZeroClass.zero_mul, mul_ite,
    MulZeroClass.mul_zero, Matrix.smul_apply, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ← ite_and, ← and_assoc, ite_smul, zero_smul,
    smul_eq_mul, one_mul, stdBasisMatrix, ← ite_and, ← and_assoc, @and_comm (j = k), eq_comm]

theorem Matrix.smul_stdBasisMatrix' {n R : Type _} [CommSemiring R] [DecidableEq n] (i j : n)
    (c : R) : stdBasisMatrix i j c = c • stdBasisMatrix i j 1 := by
  rw [smul_stdBasisMatrix, smul_eq_mul, mul_one]

theorem Matrix.trace_iff' [Fintype n] (x : Matrix n n 𝕜) : x.trace = ∑ i : n, x i i :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_1 x_2) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_1 x_2) -/
theorem existsUnique_trace [Fintype n] [DecidableEq n] [Nontrivial n] :
    ∃! φ : Matrix n n 𝕜 →ₗ[𝕜] 𝕜, (∀ a b : Matrix n n 𝕜, φ (a * b) = φ (b * a)) ∧ φ 1 = 1 :=
  by
  use(1 / Fintype.card n : 𝕜) • traceLinearMap n 𝕜 𝕜
  have trace_functional_iff :
    ∀ φ : Matrix n n 𝕜 →ₗ[𝕜] 𝕜,
      (∀ a b : Matrix n n 𝕜, φ (a * b) = φ (b * a)) ∧ φ 1 = 1 ↔
        φ = (1 / Fintype.card n : 𝕜) • traceLinearMap n 𝕜 𝕜 :=
    by
    intro φ
    have : (↑(Fintype.card n) : 𝕜)⁻¹ * ↑Finset.univ.card = 1 :=
      by
      rw [inv_mul_eq_one₀]
      · rfl
      · simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero]
        exact not_false
    constructor
    · intro h
      rw [LinearMap.ext_iff]
      intro x
      have :
        ∀ i j : n,
          φ (stdBasisMatrix i j (1 : 𝕜)) =
            (1 / (Fintype.card n : 𝕜)) • ite (j = i) (1 : 𝕜) (0 : 𝕜) :=
        by
        intro i j
        calc
          φ (stdBasisMatrix i j (1 : 𝕜)) =
              (1 / (Fintype.card n : 𝕜)) •
                ∑ k, φ (stdBasisMatrix i k 1 * (stdBasisMatrix k j 1 : Matrix n n 𝕜)) :=
            ?_
          _ =
              (1 / (Fintype.card n : 𝕜)) •
                ∑ k, φ (stdBasisMatrix k j 1 * stdBasisMatrix i k 1) :=
            ?_
          _ = (1 / (Fintype.card n : 𝕜)) • ite (j = i) (φ (∑ k, stdBasisMatrix k k 1)) 0 := ?_
          _ = (1 / (Fintype.card n : 𝕜)) • ite (j = i) (φ 1) 0 := ?_
          _ = (1 / (Fintype.card n : 𝕜)) • ite (j = i) 1 0 := ?_
        · simp_rw [StdBasisMatrix.mul_same, one_mul]
          simp only [one_div, Finset.sum_const, nsmul_eq_mul, Algebra.id.smul_eq_mul]
          rw [← mul_assoc]
          simp_rw [this, one_mul]
        · simp_rw [h.1]
        ·
          simp_rw [stdBasisMatrix_hMul, one_mul, _root_.map_smul, smul_eq_mul, boole_mul,
            Finset.sum_ite_irrel, Finset.sum_const_zero, map_sum]
        · simp_rw [StdBasisMatrix.sum_eq_one, one_smul]
        · simp_rw [h.2]
      rw [LinearMap.smul_apply, Matrix.traceLinearMap_apply]
      nth_rw 1 [matrix_eq_sum_std_basis x]
      simp_rw [Matrix.smul_stdBasisMatrix' _ _ (x _ _), map_sum, _root_.map_smul]
      calc
        ∑ x_1, ∑ x_2, x x_1 x_2 • φ (stdBasisMatrix x_1 x_2 1) =
            ∑ x_1, ∑ x_2, x x_1 x_2 • (1 / (Fintype.card n : 𝕜)) • ite (x_2 = x_1) (1 : 𝕜) 0 :=
          ?_
        _ = ∑ x_1, x x_1 x_1 • (1 / Fintype.card n : 𝕜) := ?_
        _ = (1 / Fintype.card n : 𝕜) • x.trace := ?_
      · simp_rw [← this]
      ·
        simp_rw [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul,
          mul_one]
      · simp_rw [← Finset.sum_smul, Matrix.trace_iff' x, smul_eq_mul, mul_comm]
    · rintro rfl
      simp_rw [LinearMap.smul_apply, traceLinearMap_apply, Matrix.trace_iff' 1, one_apply_eq,
        Finset.sum_const, one_div, nsmul_eq_mul, mul_one]
      refine' ⟨fun x y => _, this⟩
      rw [trace_mul_comm]
  simp only [trace_functional_iff, imp_self, forall_true_iff, and_true_iff]

theorem Matrix.stdBasisMatrix.trace [Fintype n] [DecidableEq n] (i j : n) (a : 𝕜) :
    (stdBasisMatrix i j a).trace = ite (i = j) a 0 := by
  simp_rw [Matrix.trace_iff', stdBasisMatrix, ite_and, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, eq_comm]

theorem Matrix.stdBasisMatrix_eq {R n m : Type _} [Semiring R]
  [DecidableEq n] [DecidableEq m] (i : n) (j : m) (a : R) :
    stdBasisMatrix i j a = fun i' j' => ite (i = i' ∧ j = j') a 0 :=
  rfl

theorem vecMulVec_eq_zero_iff (x : n → 𝕜) : vecMulVec x (star x) = 0 ↔ x = 0 :=
  by
  simp_rw [← Matrix.ext_iff, vecMulVec_apply, Matrix.zero_apply, Pi.star_apply,
    mul_comm _ (star _), Function.funext_iff, Pi.zero_apply]
  constructor
  · intro h i
    specialize h i i
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
      RCLike.ofReal_eq_zero, sq_eq_zero_iff, norm_eq_zero] at h
    exact h
  · intro h i j
    simp_rw [h, MulZeroClass.mul_zero]

theorem Matrix.PosDef.diagonal [Fintype n] [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosDef ↔ ∀ i, 0 < x i :=
  by
  constructor
  · intro h i
    have h' := h.2
    simp only [dotProduct, mulVec, diagonal, ite_mul, of_apply, MulZeroClass.zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h'
    let g : n → 𝕜 := fun p => ite (i = p) 1 0
    have : g ≠ 0 := by
      rw [ne_eq, Function.funext_iff, Classical.not_forall]
      simp_rw [Pi.zero_apply]
      use i
      simp_rw [g, if_true]
      exact one_ne_zero
    specialize h' g this
    simp_rw [Finset.mul_sum, mul_rotate', Pi.star_apply, g, star_ite, star_zero, star_one, boole_mul, ← ite_and,
      mul_boole, ite_and] at h'
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.diagonal_apply_eq] at h'
    exact h'
  · intro h
    simp_rw [PosDef, IsHermitian, diagonal_conjTranspose, diagonal_eq_diagonal_iff, Pi.star_apply,
      RCLike.star_def, RCLike.conj_eq_iff_im]
    refine ⟨fun _ => (RCLike.pos_def.mp (h _)).2, ?_⟩
    intro y hy
    simp only [mulVec, dotProduct_diagonal, dotProduct, diagonal, ite_mul,
      MulZeroClass.zero_mul, mul_ite, MulZeroClass.mul_zero, of_apply, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    simp_rw [Pi.star_apply, Finset.mul_sum, mul_rotate' (star (y _)), mul_comm (y _), RCLike.star_def,
      diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      @RCLike.conj_mul 𝕜 _ (y _), ← RCLike.ofReal_pow]
    apply Finset.sum_pos'
      (fun i _ => mul_nonneg (le_of_lt (h i)) (RCLike.zero_le_real.mpr (sq_nonneg _)))
    simp_rw [ne_eq, Function.funext_iff, Pi.zero_apply, Classical.not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    exact ⟨i, Finset.mem_univ _, mul_pos (h _) (by simp only [RCLike.ofReal_pow, gt_iff_lt,
      RCLike.zero_lt_real, norm_pos_iff, ne_eq, hi, not_false_eq_true, pow_pos])⟩

lemma norm_ite {α : Type*} [Norm α] (P : Prop) [Decidable P] (a b : α) :
    ‖(ite P a b : α)‖ = (ite P ‖a‖ ‖b‖) :=
  by
  split_ifs <;> rfl

theorem Matrix.PosSemidef.diagonal [Fintype n] [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosSemidef ↔ ∀ i, 0 ≤ x i :=
  by
  simp only [PosSemidef, dotProduct, mulVec, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.star_apply, mul_rotate',
    ← starRingEnd_apply, mul_comm (_) (starRingEnd 𝕜 (_)), RCLike.conj_mul, IsHermitian,
    ← Matrix.ext_iff, conjTranspose_apply]
  simp only [starRingEnd_apply, star_ite, star_zero, @eq_comm _ _ _]
  constructor
  · rintro ⟨_, h2⟩ i
    let g : n → 𝕜 := fun p => ite (i = p) 1 0
    specialize h2 g
    simp_rw [g, ← RCLike.ofReal_pow, norm_ite, norm_one, norm_zero, ite_pow,
      one_pow, zero_pow two_ne_zero] at h2
    have : ∀ i j : n, ((if i = j then (1 : ℝ) else 0 : ℝ) : 𝕜) = if i = j then (1 : 𝕜) else 0 :=
    λ i j => by split_ifs <;> simp only [algebraMap.coe_one, algebraMap.coe_zero]
    simp_rw [this, mul_boole, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
    exact h2
  · intro h
    constructor
    · intro i j
      split_ifs with hh
      { simp_rw [hh, RCLike.star_def, @eq_comm _ (x j), RCLike.conj_eq_iff_re]
        exact (RCLike.nonneg_def'.mp (h _)).1 }
      { rfl }
    · intro y
      apply Finset.sum_nonneg'
      simp_rw [← RCLike.ofReal_pow]
      exact fun _ => mul_nonneg (h _) (RCLike.zero_le_real.mpr (sq_nonneg _))

namespace Matrix

theorem trace_conjTranspose_hMul_self_nonneg {m : Type*} [Fintype m] [Fintype n]
  (x : Matrix m n 𝕜) : 0 ≤ (xᴴ * x).trace :=
  by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_nonneg'
  intro i
  apply Finset.sum_nonneg'
  intro j
  simp_rw [RCLike.star_def, ← RCLike.inner_apply]
  exact inner_self_nonneg'

/-- given a positive definite matrix $Q$, we have
  $0\leq\operatorname{Tr}(Qx^*x)$ for any matrix $x$ -/
theorem PosSemidef.trace_conjTranspose_hMul_self_nonneg {m : Type*}
  [Fintype m] [Fintype n] [DecidableEq m] {Q : Matrix m m 𝕜}
  (hQ : Q.PosSemidef) (x : Matrix n m 𝕜) :
  0 ≤ (Q * xᴴ * x).trace :=
  by
  rcases (Matrix.posSemidef_iff Q).mp hQ with ⟨y, rfl⟩
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  nth_rw 1 [← conjTranspose_conjTranspose x]
  rw [← Matrix.conjTranspose_mul]
  simp_rw [Matrix.mul_assoc]
  exact Matrix.trace_conjTranspose_hMul_self_nonneg _

open scoped BigOperators

@[simp]
theorem Finset.sum_abs_eq_zero_iff' {s : Type _} [Fintype s] {x : s → 𝕜} :
    ∑ i : s in Finset.univ, ‖x i‖ ^ 2 = 0 ↔ ∀ i : s, ‖x i‖ ^ 2 = 0 :=
  by
  have : ∀ i : s, 0 ≤ ‖x i‖ ^ 2 := fun i => sq_nonneg _
  constructor
  · intro h i
    have h' : ∀ i : s, i ∈ Finset.univ → 0 ≤ ‖x i‖ ^ 2 := by intro i _; exact this _
    have h'' : ∑ i : s in _, ‖(x i : 𝕜)‖ ^ 2 = 0 := h
    rw [Finset.sum_eq_zero_iff_of_nonneg h'] at h''
    simp only [Finset.mem_univ, RCLike.normSq_eq_zero, forall_true_left] at h''
    exact h'' i
  · intro h
    simp_rw [h, Finset.sum_const_zero]

theorem trace_conjTranspose_hMul_self_eq_zero {m : Type*} [Fintype n] [Fintype m]
  (x : Matrix n m 𝕜) : (xᴴ * x).trace = 0 ↔ x = 0 :=
  by
  simp_rw [← Matrix.ext_iff, Matrix.zero_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul,
    ← RCLike.ofReal_pow]
  norm_cast
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_product', Finset.univ_product_univ, Finset.sum_abs_eq_zero_iff',
    pow_eq_zero_iff two_ne_zero, norm_eq_zero, Prod.forall]

/-- given a positive definite matrix $Q$, we get
  $\textnormal{Tr}(Qx^*x)=0$ if and only if $x=0$ for any matrix $x$ -/
theorem Nontracial.trace_conjTranspose_hMul_self_eq_zero {m : Type*}
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {Q : Matrix m m 𝕜}
  (hQ : Q.PosDef) {x : Matrix n m 𝕜} : (Q * xᴴ * x).trace = 0 ↔ x = 0 :=
  by
  rcases(posSemidef_iff Q).mp hQ.posSemidef with ⟨y, rfl⟩
  rw [trace_mul_cycle, ← Matrix.mul_assoc]
  nth_rw 1 [← conjTranspose_conjTranspose x]
  rw [← conjTranspose_mul]
  simp_rw [Matrix.mul_assoc]
  rw [Matrix.trace_conjTranspose_hMul_self_eq_zero _]
  refine' ⟨fun h => _, fun h => by rw [h, conjTranspose_zero, Matrix.mul_zero]⟩
  rw [← conjTranspose_eq_zero, mulVec_eq]
  intro u
  apply_fun (Matrix.toLin' (yᴴ * y)) using
    (Function.Bijective.injective (Matrix.bij_toLin'_of_invertible hQ.invertible))
  simp_rw [← toLin'_apply, ← LinearMap.comp_apply, ← toLin'_mul, Matrix.mul_assoc,
    h, Matrix.mul_zero]

theorem IsHermitian.trace_conj_symm_star_hMul {m : Type*} [Fintype m] [Fintype n]
  {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
  (x y : Matrix n m 𝕜) : (starRingEnd 𝕜) (Q * yᴴ * x).trace = (Q * xᴴ * y).trace :=
  by
  simp_rw [starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, hQ.eq, Matrix.mul_assoc]
  rw [trace_mul_cycle']

theorem conjTranspose_hMul_self_eq_zero {m : Type*} [Fintype m] [Fintype n]
  (x : Matrix n m 𝕜) : xᴴ * x = 0 ↔ x = 0 :=
  by
  refine' ⟨_, fun h => by rw [h, Matrix.mul_zero]⟩
  simp_rw [← Matrix.ext_iff, mul_apply, conjTranspose_apply, Matrix.zero_apply]
  intro h i j
  specialize h j j
  simp_rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_sum,
    ← @RCLike.ofReal_zero 𝕜, RCLike.ofReal_inj, Finset.sum_abs_eq_zero_iff',
    sq_eq_zero_iff, norm_eq_zero] at h
  exact h i

theorem PosSemidef.smul [Fintype n]
  {x : Matrix n n 𝕜} (hx : x.PosSemidef) (α : NNReal) :
  (((α : ℝ) : 𝕜) • x).PosSemidef := by
  constructor
  · calc
      (((α : ℝ) : 𝕜) • x)ᴴ = star ((α : ℝ) : 𝕜) • xᴴ := by rw [conjTranspose_smul]
      _ = ((α : ℝ) : 𝕜) • x := by rw [RCLike.star_def, RCLike.conj_ofReal, hx.1.eq]
  . intro y
    simp_rw [smul_mulVec_assoc, dotProduct_smul]
    exact mul_nonneg (RCLike.zero_le_real.mpr (NNReal.coe_nonneg _)) (hx.2 y)

end Matrix

namespace Matrix

theorem PosSemidef.colMulConjTransposeCol [Fintype n] [DecidableEq n]
    (x : n → 𝕜) : (col x * (col x)ᴴ : Matrix n n 𝕜).PosSemidef :=
Matrix.posSemidef_self_mul_conjTranspose _

alias PosSemidef.mulConjTransposeSelf := Matrix.posSemidef_self_mul_conjTranspose

end Matrix
