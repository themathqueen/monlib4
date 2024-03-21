/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyMatrix.PosEqLinearMapIsPositive
import Preq.IsROrCLe
import LinearAlgebra.IsReal
import LinearAlgebra.MyMatrix.IncludeBlock

#align_import linear_algebra.my_ips.functional

/-!

# Linear functionals

This file contains results for linear functionals on the set of $n \times n$ matrices $M_n$ over $\mathbb{C}$.

## Main results
- `module.dual.apply`
- `module.dual.is_pos_map_iff`
- `module.dual.is_faithful_pos_map_iff`
- `module.dual.is_tracial_faithful_pos_map_iff`
- `module.dual.is_faithful_pos_map_iff_is_inner`

-/


variable {𝕜 R n : Type _} [IsROrC 𝕜] [CommSemiring R] [Fintype n] [DecidableEq n]

open scoped Matrix BigOperators

open Matrix

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- the matrix of a linear map `φ : M_n →ₗ[R] R` is given by
  `∑ i j, std_basis_matrix j i (φ (std_basis_matrix i j 1))`. -/
def Module.Dual.matrix (φ : Module.Dual R (Matrix n n R)) :=
  ∑ (i : n) (j : n), Matrix.stdBasisMatrix j i (φ (Matrix.stdBasisMatrix i j 1))

/-- given any linear functional `φ : M_n →ₗ[R] R`, we get `φ a = (φ.matrix ⬝ a).trace`. -/
theorem Module.Dual.apply (φ : Module.Dual R (Matrix n n R)) (a : Matrix n n R) :
    φ a = (φ.Matrix ⬝ a).trace :=
  by
  simp_rw [Module.Dual.matrix, smul_std_basis_matrix' _ _ (φ _)]
  simp_rw [Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, Matrix.trace, Matrix.diag,
    mul_apply, std_basis_matrix, boole_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ← ite_and, smul_eq_mul, mul_comm (φ _) _, ←
    smul_eq_mul, ← SMulHomClass.map_smul, ← map_sum]
  have :
    ∀ ⦃i : n⦄ ⦃j : n⦄ ⦃a : R⦄,
      std_basis_matrix i j (a : R) = fun k l => ite (i = k ∧ j = l) (a : R) (0 : R) :=
    fun i j a => rfl
  simp_rw [← this, smul_std_basis_matrix, smul_eq_mul, mul_one]
  rw [← matrix_eq_sum_std_basis a]

/--
we linear maps `φ_i : M_[n_i] →ₗ[R] R`, we define its direct sum as the linear map `(Π i, M_[n_i]) →ₗ[R] R`. -/
@[simps]
def Module.Dual.pi {k : Type _} [Fintype k] {s : k → Type _}
    (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R)) : Module.Dual R (∀ i, Matrix (s i) (s i) R)
    where
  toFun a := ∑ i : k, φ i (a i)
  map_add' x y := by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [SMulHomClass.map_smul, Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

/-- for direct sums, we get `φ x = ∑ i, ((φ i).matrix ⬝ x i).trace` -/
theorem Module.Dual.pi.apply {k : Type _} [Fintype k] {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R))
    (x : ∀ i, Matrix (s i) (s i) R) : Module.Dual.pi φ x = ∑ i, ((φ i).Matrix ⬝ x i).trace := by
  simp_rw [Module.Dual.pi_apply, Module.Dual.apply]

theorem Module.Dual.pi.apply' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R))
    (x : ∀ i, Matrix (s i) (s i) R) :
    Module.Dual.pi φ x = ∑ i, (blockDiagonal' (φ i).Matrix.includeBlock ⬝ blockDiagonal' x).trace :=
  by
  symm
  simp_rw [← block_diagonal'_mul, ← mul_eq_mul]
  calc
    ∑ x_1 : k, (block_diagonal' fun k_1 : k => (φ x_1).Matrix.includeBlock k_1 * x k_1).trace =
        ∑ x_1 : k, (block_diagonal' fun k_1 => ((φ x_1).Matrix.includeBlock * x) k_1).trace :=
      rfl
    _ = ∑ x_1 : k, (block_diagonal' fun k_1 => ((φ x_1).Matrix * x x_1).includeBlock k_1).trace :=
      by
      congr
      ext
      congr
      ext
      simp only [include_block_mul]
    _ = ∑ x_1, ((φ x_1).Matrix * x x_1).trace :=
      by
      simp only [include_block_apply, trace_iff, block_diagonal'_apply, dite_apply,
        eq_self_iff_true, dif_pos, Pi.zero_apply, eq_mp_eq_cast, cast_eq]
      rw [Finset.sum_comm]
      simp only [Finset.sum_dite_eq', Finset.mem_univ, if_true]
      simp_rw [Finset.sum_sigma']
      rfl
    _ = Module.Dual.pi φ x := (Module.Dual.pi.apply _ _).symm

theorem Module.Dual.apply_eq_of (φ : Module.Dual R (Matrix n n R)) (x : Matrix n n R)
    (h : ∀ a, φ a = (x ⬝ a).trace) : x = φ.Matrix :=
  by
  simp_rw [Module.Dual.apply, ← Matrix.ext_iff_trace] at h
  exact h.symm

/--
Any linear functional $f$ on $M_n$ is given by a unique matrix $Q \in M_n$ such that $f(x)=\operatorname{Tr}(Qx)$ for any $x \in M_n$. -/
theorem Module.Dual.eq_trace_unique (φ : Module.Dual R (Matrix n n R)) :
    ∃! Q : Matrix n n R, ∀ a : Matrix n n R, φ a = (Q ⬝ a).trace :=
  by
  use φ.matrix
  simp_rw [Module.Dual.apply, eq_self_iff_true, forall_true_iff, true_and_iff, ←
    Matrix.ext_iff_trace, eq_comm, imp_self, forall_true_iff]

def Module.Dual.pi' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R)) :
    Module.Dual R { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal } :=
  Module.Dual.pi φ ∘ₗ isBlockDiagonalPiAlgEquiv.toLinearMap

/-- `⨁_i φ_i ι_i (x_i) = φ_i (x_i)` -/
theorem Module.Dual.pi.apply_single_block {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (φ : ∀ i, Matrix (s i) (s i) R →ₗ[R] R)
    (x : ∀ i, Matrix (s i) (s i) R) (i : k) : (Module.Dual.pi φ) (includeBlock (x i)) = φ i (x i) :=
  by
  simp_rw [Module.Dual.pi_apply, Module.Dual.apply, include_block_apply, ← mul_eq_mul, hMul_dite,
    MulZeroClass.mul_zero, trace_iff, dite_apply, Pi.zero_apply, Finset.sum_dite_irrel,
    Finset.sum_const_zero, Finset.sum_dite_eq, Finset.mem_univ, if_true]
  rfl

open scoped ComplexOrder

open scoped DirectSum

/-- A linear functional $φ$ on $M_n$ is positive if $0 ≤ φ (x^*x)$ for all $x \in M_n$. -/
def Module.Dual.IsPosMap {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
    (φ : Module.Dual 𝕜 A) : Prop :=
  ∀ a : A, 0 ≤ φ (star a * a)

/-- A linear functional $φ$ on $M_n$ is unital if $φ(1) = 1$. -/
def Module.Dual.IsUnital {A : Type _} [AddCommMonoid A] [Module R A] [One A] (φ : Module.Dual R A) :
    Prop :=
  φ (1 : A) = 1

/-- A linear functional is called a state if it is positive and unital -/
def Module.Dual.IsState {A : Type _} [Semiring A] [StarRing A] [Module 𝕜 A] (φ : Module.Dual 𝕜 A) :
    Prop :=
  φ.IsPosMap ∧ φ.IsUnital

theorem Module.Dual.isPosMap_of_matrix (φ : Module.Dual 𝕜 (Matrix n n 𝕜)) :
    φ.IsPosMap ↔ ∀ a : Matrix n n 𝕜, a.PosSemidef → 0 ≤ φ a := by
  simp_rw [pos_semidef_iff, exists_imp, Module.Dual.IsPosMap, mul_eq_mul, forall_eq_apply_imp_iff,
    star_eq_conj_transpose]

/--
A linear functional $f$ on $M_n$ is said to be faithful if $f(x^*x)=0$ if and only if $x=0$ for any $x \in M_n$. -/
def Module.Dual.IsFaithful {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
    (φ : Module.Dual 𝕜 A) : Prop :=
  ∀ a : A, φ (star a * a) = 0 ↔ a = 0

theorem Module.Dual.isFaithful_of_matrix (φ : Module.Dual 𝕜 (Matrix n n 𝕜)) :
    φ.IsFaithful ↔ ∀ a : Matrix n n 𝕜, a.PosSemidef → (φ a = 0 ↔ a = 0) := by
  simp_rw [pos_semidef_iff, exists_imp, Module.Dual.IsFaithful, mul_eq_mul, forall_eq_apply_imp_iff,
    conj_transpose_mul_self_eq_zero, star_eq_conj_transpose]

/--
A linear functional $f$ is positive if and only if there exists a unique positive semi-definite matrix $Q\in M_n$ such $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$.  -/
theorem Module.Dual.isPosMap_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsPosMap ↔ φ.Matrix.PosSemidef := by
  constructor
  · intro hs
    rw [Module.Dual.isPosMap_of_matrix] at hs
    simp only [Module.Dual.apply] at hs
    have thiseq : ∀ y, star y ⬝ᵥ φ.matrix.mul_vec y = (φ.matrix ⬝ vec_mul_vec y (star y)).trace :=
      by
      intro y
      rw [vec_mul_vec_eq, trace_mul_cycle', ← col_mul_vec]
      simp_rw [Matrix.trace_iff', row_mul_col_apply, Fintype.univ_punit, Finset.sum_const,
        Finset.card_singleton, nsmul_eq_mul, algebraMap.coe_one, one_mul]
    simp_rw [PosSemidef.complex, thiseq]
    intro y
    -- rw [thiseq, ← is_R_or_C.re_to_complex, ← is_R_or_C.nonneg_def'],
    refine' hs _ _
    exact VecMulVec.posSemidef _
  · intro hy y
    rw [φ.apply, mul_eq_mul, ← Matrix.mul_assoc, IsROrC.nonneg_def']
    exact hy.trace_conj_transpose_mul_self_nonneg _

/--
A linear functional $f$ is a state if and only if there exists a unique positive semi-definite matrix $Q\in M_n$ such that its trace equals $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
theorem Module.Dual.isState_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsState ↔ φ.Matrix.PosSemidef ∧ φ.Matrix.trace = 1 := by
  rw [Module.Dual.IsState, Module.Dual.isPosMap_iff_of_matrix, Module.Dual.IsUnital,
    Module.Dual.apply, Matrix.mul_one]

/--
A positive linear functional $f$ is faithful if and only if there exists a positive definite matrix such that $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
theorem Module.Dual.IsPosMap.isFaithful_iff_of_matrix {φ : Module.Dual ℂ (Matrix n n ℂ)}
    (hs : φ.IsPosMap) : φ.IsFaithful ↔ φ.Matrix.PosDef :=
  by
  have hs' := hs
  rw [Module.Dual.isPosMap_of_matrix] at hs'
  rw [Module.Dual.isFaithful_of_matrix]
  constructor
  · rw [Module.Dual.isPosMap_iff_of_matrix] at hs
    intro HHH
    · refine' ⟨hs.1, _⟩
      intro x hx
      have : star x ⬝ᵥ φ.matrix.mul_vec x = (φ.matrix ⬝ vec_mul_vec x (star x)).trace :=
        by
        rw [vec_mul_vec_eq, trace_mul_cycle', ← col_mul_vec]
        simp_rw [Matrix.trace_iff', row_mul_col_apply, Fintype.univ_punit, Finset.sum_const,
          Finset.card_singleton, nsmul_eq_mul, algebraMap.coe_one, one_mul]
      rw [this]
      have this2 := HHH (vec_mul_vec x (star x)) (VecMulVec.posSemidef _)
      have this3 := hs' (vec_mul_vec x (star x)) (VecMulVec.posSemidef _)
      rw [le_iff_eq_or_lt] at this3
      rcases this3 with (this3 | this32)
      · rw [eq_comm, this3, this2, vecMulVec_eq_zero_iff] at this3
        contradiction
      · rw [← Module.Dual.apply]
        exact (is_R_or_C.pos_def.mp this32).1
  · intro hQ a ha
    refine' ⟨fun h => _, fun h => by rw [h, map_zero]⟩
    obtain ⟨b, rfl⟩ := (pos_semidef_iff _).mp ha
    rw [Module.Dual.apply, ← Matrix.mul_assoc,
      nontracial.trace_conj_transpose_mul_self_eq_zero hQ] at h
    rw [h, Matrix.mul_zero]

def Module.Dual.IsFaithfulPosMap {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
    (φ : Module.Dual 𝕜 A) : Prop :=
  φ.IsPosMap ∧ φ.IsFaithful

/--
A linear functional $φ$ is a faithful and positive if and only if there exists a unique positive definite matrix $Q$ such that $φ(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
theorem Module.Dual.isFaithfulPosMap_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ↔ φ.Matrix.PosDef :=
  by
  refine' ⟨fun h => h.1.isFaithful_iff_of_matrix.mp h.2, _⟩
  intro hQ
  simp_rw [Module.Dual.IsFaithfulPosMap, Module.Dual.IsFaithful, Module.Dual.isPosMap_iff_of_matrix,
    hQ.pos_semidef, true_and_iff, Module.Dual.apply, mul_eq_mul, star_eq_conj_transpose, ←
    Matrix.mul_assoc, nontracial.trace_conj_transpose_mul_self_eq_zero hQ, iff_self_iff,
    forall_const]

/--
A state is faithful $f$ if and only if there exists a unique positive definite matrix $Q\in M_n$ with trace equal to $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x \in M_n$. -/
theorem Module.Dual.IsState.isFaithful_iff_of_matrix {φ : Module.Dual ℂ (Matrix n n ℂ)}
    (hs : φ.IsState) : φ.IsFaithful ↔ φ.Matrix.PosDef ∧ φ.Matrix.trace = 1 :=
  by
  rw [hs.1.isFaithful_iff_of_matrix]
  refine' ⟨fun hQ => ⟨hQ, _⟩, fun hQ => hQ.1⟩
  · rw [Module.Dual.isState_iff_of_matrix] at hs
    exact hs.2

theorem Module.Dual.isFaithful_state_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsState ∧ φ.IsFaithful ↔ φ.Matrix.PosDef ∧ φ.Matrix.trace = 1 :=
  by
  refine' ⟨fun h => h.1.isFaithful_iff_of_matrix.mp h.2, _⟩
  intro hQ
  simp_rw [Module.Dual.IsFaithful, Module.Dual.isState_iff_of_matrix, hQ.2, hQ.1.PosSemidef,
    eq_self_iff_true, true_and_iff]
  rw [← Module.Dual.isFaithfulPosMap_iff_of_matrix] at hQ
  exact hQ.1.2

/-- A linear functional $f$ is tracial if and only if $f(xy)=f(yx)$ for all $x,y$. -/
def Module.Dual.IsTracial {A : Type _} [NonUnitalSemiring A] [Module 𝕜 A] (φ : Module.Dual 𝕜 A) :
    Prop :=
  ∀ x y : A, φ (x * y) = φ (y * x)

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/--
A linear functional is tracial and positive if and only if there exists a non-negative real $α$ such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
theorem Module.Dual.isTracial_pos_map_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsPosMap ∧ φ.IsTracial ↔ ∃ α : NNReal, φ.Matrix = ((α : ℝ) : ℂ) • 1 :=
  by
  constructor
  · simp_rw [Module.Dual.isPosMap_iff_of_matrix]
    rintro ⟨hQ, h2⟩
    simp_rw [Module.Dual.IsTracial, Module.Dual.apply, Matrix.trace, Matrix.diag, mul_eq_mul,
      mul_apply] at h2
    let Q := φ.matrix
    have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 := fun p q r =>
      calc
        Q p q =
            ∑ (i) (j), Q i j * ∑ k, (std_basis_matrix q r 1) j k * (std_basis_matrix r p 1) k i :=
          by
          simp only [std_basis_matrix, boole_mul, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, eq_self_iff_true, if_true,
            mul_ite, MulZeroClass.mul_zero, mul_one]
        _ = ∑ (i) (j), Q i j * ∑ k, (std_basis_matrix r p 1) j k * (std_basis_matrix q r 1) k i :=
          by rw [h2]
        _ = ite (p = q) (Q r r) 0 := by
          simp only [std_basis_matrix, boole_mul, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite,
            MulZeroClass.mul_zero, mul_one]
    by_cases h : IsEmpty n
    · use 1
      haveI := h
      simp only [eq_iff_true_of_subsingleton]
    rw [not_isEmpty_iff] at h
    let i : n := h.some
    have HH : Q = diagonal fun x_1 : n => Q i i :=
      by
      ext1
      exact this _ _ i
    have this' : ∀ p, Q p p = IsROrC.re (Q p p) :=
      by
      intro p
      rw [eq_comm, ← IsROrC.conj_eq_iff_re, ← IsROrC.star_def, ← Matrix.star_apply,
        star_eq_conj_transpose, hQ.1.Eq]
    have : 0 ≤ Q i i := by
      rw [PosSemidef.complex] at hQ
      specialize hQ fun j => ite (i = j) 1 0
      simp_rw [dot_product, mul_vec, dot_product, Pi.star_apply, star_ite, star_zero, star_one,
        boole_mul, mul_boole, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hQ
      exact hQ
    have thisthis : 0 ≤ IsROrC.re (Q i i) :=
      by
      rw [IsROrC.nonneg_def'] at this
      exact this.2
    let α : NNReal := ⟨IsROrC.re (Q i i), thisthis⟩
    have hα : (α : ℂ) = IsROrC.re (Q i i) := rfl
    have hα' : IsROrC.re (Q i i) = α := rfl
    refine' ⟨α, _⟩
    · simp only [smul_eq_diagonal_mul, ← hα', Matrix.mul_one]
      rw [← this']
      exact HH
  · rintro ⟨α, hα1⟩
    simp_rw [Module.Dual.IsPosMap, Module.Dual.IsTracial, Module.Dual.apply, hα1,
      IsROrC.nonneg_def', ← IsROrC.conj_eq_iff_re, starRingEnd_apply, Matrix.smul_mul,
      Matrix.one_mul, trace_star, conj_transpose_smul, mul_eq_mul, star_eq_conj_transpose,
      conj_transpose_mul, conj_transpose_conj_transpose, IsROrC.star_def, IsROrC.conj_ofReal,
      trace_smul, smul_eq_mul, IsROrC.re_ofReal_mul,
      mul_nonneg (NNReal.coe_nonneg _) (trace_conj_transpose_mul_self_re_nonneg _), and_true_iff]
    exact ⟨fun _ => rfl, fun _ _ => by rw [trace_mul_comm]⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/--
A linear functional is tracial and positive if and only if there exists a unique non-negative real $α$ such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
theorem Module.Dual.isTracial_pos_map_iff'_of_matrix [Nonempty n]
    (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsPosMap ∧ φ.IsTracial ↔ ∃! α : NNReal, φ.Matrix = ((α : ℝ) : ℂ) • 1 :=
  by
  constructor
  · simp_rw [Module.Dual.isPosMap_iff_of_matrix]
    rintro ⟨hQ, h2⟩
    simp_rw [Module.Dual.IsTracial, Module.Dual.apply, Matrix.trace, Matrix.diag, mul_eq_mul,
      mul_apply] at h2
    let Q := φ.matrix
    have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 := fun p q r =>
      calc
        Q p q =
            ∑ (i) (j), Q i j * ∑ k, (std_basis_matrix q r 1) j k * (std_basis_matrix r p 1) k i :=
          by
          simp only [std_basis_matrix, boole_mul, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, eq_self_iff_true, if_true,
            mul_ite, MulZeroClass.mul_zero, mul_one]
        _ = ∑ (i) (j), Q i j * ∑ k, (std_basis_matrix r p 1) j k * (std_basis_matrix q r 1) k i :=
          by rw [h2]
        _ = ite (p = q) (Q r r) 0 := by
          simp only [std_basis_matrix, boole_mul, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite,
            MulZeroClass.mul_zero, mul_one]
    let i : n := _inst_5.some
    have HH : Q = diagonal fun x_1 : n => Q i i :=
      by
      ext1
      exact this _ _ i
    have this' : ∀ p, Q p p = IsROrC.re (Q p p) :=
      by
      intro p
      rw [eq_comm, ← IsROrC.conj_eq_iff_re, ← IsROrC.star_def, ← Matrix.star_apply,
        star_eq_conj_transpose, hQ.1.Eq]
    have : 0 ≤ Q i i := by
      rw [PosSemidef.complex] at hQ
      specialize hQ fun j => ite (i = j) 1 0
      simp_rw [dot_product, mul_vec, dot_product, Pi.star_apply, star_ite, star_zero, star_one,
        boole_mul, mul_boole, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hQ
      exact hQ
    have thisthis : 0 ≤ IsROrC.re (Q i i) :=
      by
      rw [IsROrC.nonneg_def'] at this
      exact this.2
    let α : NNReal := ⟨IsROrC.re (Q i i), thisthis⟩
    have hα : (α : ℂ) = IsROrC.re (Q i i) := rfl
    have hα' : IsROrC.re (Q i i) = α := rfl
    refine' ⟨α, ⟨_, _⟩⟩
    · simp only [smul_eq_diagonal_mul, ← hα', Matrix.mul_one]
      rw [← this']
      exact HH
    · intro y hy
      simp only [Q] at *
      simp only [smul_eq_diagonal_mul, Matrix.mul_one] at hy
      rw [HH, diagonal_eq_diagonal_iff, this'] at hy
      specialize hy i
      norm_cast at hy
      simp_rw [α, Q, hy, Subtype.coe_eta]
  · rintro ⟨α, ⟨hα1, hα2⟩⟩
    simp_rw [Module.Dual.IsPosMap, Module.Dual.IsTracial, Module.Dual.apply, hα1,
      IsROrC.nonneg_def', ← IsROrC.conj_eq_iff_re, starRingEnd_apply, Matrix.smul_mul,
      Matrix.one_mul, trace_star, conj_transpose_smul, mul_eq_mul, star_eq_conj_transpose,
      conj_transpose_mul, conj_transpose_conj_transpose, IsROrC.star_def, IsROrC.conj_ofReal,
      trace_smul, smul_eq_mul, IsROrC.re_ofReal_mul,
      mul_nonneg (NNReal.coe_nonneg _) (trace_conj_transpose_mul_self_re_nonneg _), and_true_iff]
    exact ⟨fun _ => rfl, fun _ _ => by rw [trace_mul_comm]⟩

/--
A linear functional $f$ is tracial positive and faithful if and only if there exists a positive real number $\alpha$ such that $f\colon x\mapsto \alpha \operatorname{Tr}(x)$. -/
theorem Module.Dual.isTracial_faithful_pos_map_iff_of_matrix [Nonempty n]
    (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ∧ φ.IsTracial ↔
      ∃! α : { x : NNReal // 0 < x }, φ.Matrix = (((α : NNReal) : ℝ) : ℂ) • 1 :=
  by
  rw [Module.Dual.IsFaithfulPosMap, and_comm' φ.is_pos_map _, and_assoc',
    Module.Dual.isTracial_pos_map_iff'_of_matrix]
  constructor
  · rintro ⟨h1, ⟨α, hα, h⟩⟩
    have : 0 < (α : ℝ) := by
      rw [NNReal.coe_pos, pos_iff_ne_zero]
      intro HH
      rw [Module.Dual.IsFaithful] at h1
      specialize h1 ((1 : Matrix n n ℂ)ᴴ ⬝ (1 : Matrix n n ℂ))
      simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Module.Dual.apply,
        mul_eq_mul, star_eq_conj_transpose] at h1
      simp_rw [HH, NNReal.coe_zero, Complex.ofReal_zero, zero_smul] at hα
      rw [hα, trace_zero, eq_self_iff_true, true_iff_iff] at h1
      simp only [one_ne_zero'] at h1
      exact h1
    let α' : { x : NNReal // 0 < x } := ⟨α, this⟩
    have : α = α' := rfl
    refine' ⟨α', hα, fun y hy => _⟩
    simp_rw [← Subtype.coe_inj, Subtype.coe_mk] at hy ⊢
    norm_cast
    exact h _ hy
  · rintro ⟨α, ⟨h1, h2⟩⟩
    have : 0 < (α : NNReal) := Subtype.mem α
    refine' ⟨_, ⟨α, h1, fun y hy => _⟩⟩
    ·
      simp_rw [Module.Dual.IsFaithful, Module.Dual.apply, h1, Matrix.smul_mul, Matrix.one_mul,
        trace_smul, smul_eq_zero, IsROrC.ofReal_eq_zero, NNReal.coe_eq_zero, ne_zero_of_lt this,
        false_or_iff, star_eq_conj_transpose, mul_eq_mul, trace_conj_transpose_mul_self_eq_zero,
        iff_self_iff, forall_true_iff]
    rw [h1, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at hy
    simp only [one_ne_zero', or_false_iff, IsROrC.ofReal_inj, NNReal.coe_inj] at hy
    rw [hy]

-- lemma linear_map.is_tracial_state_iff [nonempty n] (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
--   (φ.is_state ∧ φ.is_tracial) ↔ ∃ α : ℂ, φ.matrix = α • 1 ∧ α * (1 : matrix n n ℂ).trace = 1 :=
-- begin
--   split,
--   { simp_rw [linear_map.is_state_iff],
--     -- rintros ⟨⟨Q, ⟨hQ1, hQ2, hQ3⟩, h1⟩, h2⟩,
--     simp_rw [linear_map.is_tracial, hQ3, matrix.trace, matrix.diag, mul_apply] at h2,
--     have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 :=
--     λ p q r, calc Q p q = ∑ i j, Q i j
--       * ∑ k, (std_basis_matrix q r 1) j k * (std_basis_matrix r p 1) k i :
--     by { simp only [std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
--       finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, eq_self_iff_true, if_true,
--       mul_ite, mul_zero, mul_one], }
--       ... = ∑ i j, Q i j
--       * ∑ k, (std_basis_matrix r p 1) j k * (std_basis_matrix q r 1) k i : by rw h2
--       ... = ite (p = q) (Q r r) 0 :
--     by { simp only [std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
--       finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, if_true, mul_ite,
--       mul_zero, mul_one], },
--     let i : n := _inst_5.some,
--     use Q i i,
--     simp_rw [trace_one, ← hQ2],
--     split,
--     { intros x,
--       simp_rw [hQ3, matrix.trace, matrix.diag, mul_apply],
--       calc ∑ k j, Q k j * x j k = ∑ k j, ite (k = j) (Q i i) 0 * x j k : by simp_rw ← this _ _ i
--         ... = Q i i * ∑ k, x k k : _,
--       simp_rw [ite_mul, zero_mul, finset.sum_ite_eq, finset.mem_univ, if_true,
--         finset.mul_sum], },
--     { rw eq_comm,
--       calc ∑ k, Q k k = ∑ k : n, ite (k = k) (Q i i) 0 : by simp_rw ← this _ _ i
--         ... = ∑ k : n, Q i i : by simp_rw [eq_self_iff_true, if_true]
--         ... = Q i i * ↑(fintype.card n) : _,
--       simp_rw [finset.sum_const, nsmul_eq_mul, mul_comm],
--       refl, }, },
--   { rintros ⟨α, ⟨hα1, hα2⟩⟩,
--     simp_rw [linear_map.is_state_iff, hα1],
--     split,
--     { use α • 1,
--       split,
--       { simp only [matrix.smul_mul, trace_smul, smul_eq_mul, matrix.one_mul],
--         refine ⟨_, hα2, λ _, rfl⟩,
--         simp only [← diagonal_one, ← diagonal_smul, pos_semidef.diagonal],
--         intros i,
--         simp_rw [pi.smul_apply, ← is_R_or_C.conj_eq_iff_re, star_ring_end_apply,
--           smul_eq_mul, mul_one],
--         have : α = 1 / (1 : matrix n n ℂ).trace,
--         { rw [← hα2, trace_one, ← mul_div, div_self, mul_one],
--           { simp only [ne.def, nat.cast_eq_zero],
--             exact fintype.card_ne_zero, }, },
--         simp_rw [this, trace_one, star_div', star_one, star_nat_cast, eq_self_iff_true, and_true],
--         simp only [one_div, is_R_or_C.re_to_complex, complex.inv_re, complex.nat_cast_re],
--         apply div_nonneg,
--         { exact (nat.cast_nonneg _), },
--         { simp_rw [complex.norm_sq_nonneg], }, },
--       { simp only,
--         rintros y ⟨hy1, hy2, hy3⟩,
--         ext1 i j,
--         simp_rw [pi.smul_apply, one_apply, smul_eq_mul, mul_boole],
--         specialize hy3 (std_basis_matrix j i (1 : ℂ)),
--         simp_rw [std_basis_matrix.trace, matrix.trace, matrix.diag, mul_apply,
--           std_basis_matrix, mul_boole, ite_and] at hy3,
--         simp only [finset.sum_ite_eq, finset.mem_univ, if_true] at hy3,
--         simp_rw @eq_comm _ j i at hy3,
--         exact hy3.symm, }, },
--     { intros x y,
--       rw [hα1, trace_mul_comm, ← hα1], }, },
-- end
theorem Matrix.ext_iff_trace' {R m n : Type _} [Semiring R] [StarRing R] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (A B : Matrix m n R) :
    (∀ x, (xᴴ ⬝ A).trace = (xᴴ ⬝ B).trace) ↔ A = B :=
  by
  refine' ⟨fun h => _, fun h x => by rw [h]⟩
  ext i j
  specialize h (std_basis_matrix i j (1 : R))
  simp_rw [std_basis_matrix_conj_transpose, star_one, Matrix.stdBasisMatrix_hMul_trace] at h
  exact h

theorem Module.Dual.isReal_iff {φ : Module.Dual ℂ (Matrix n n ℂ)} :
    φ.IsReal ↔ φ.Matrix.IsHermitian := by
  simp_rw [LinearMap.IsReal, Module.Dual.apply, trace_star, conj_transpose_mul,
    star_eq_conj_transpose, trace_mul_comm φ.matrix, Matrix.ext_iff_trace', is_hermitian, eq_comm]

theorem Module.Dual.IsPosMap.isReal {φ : Module.Dual ℂ (Matrix n n ℂ)} (hφ : φ.IsPosMap) :
    φ.IsReal := by
  rw [Module.Dual.isPosMap_iff_of_matrix] at hφ
  rw [Module.Dual.isReal_iff]
  exact hφ.1

theorem Module.Dual.pi.IsPosMap.isReal {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    (hψ : ∀ i, (ψ i).IsPosMap) : (Module.Dual.pi ψ).IsReal := by
  simp_rw [LinearMap.IsReal, Module.Dual.pi_apply, star_sum, Pi.star_apply, (hψ _).IsReal _,
    eq_self_iff_true, forall_true_iff]

/-- A function $H \times H \to 𝕜$ defines an inner product if it satisfies the following. -/
def IsInner {H : Type _} [AddCommMonoid H] [Module 𝕜 H] (φ : H × H → 𝕜) : Prop :=
  (∀ x y : H, φ (x, y) = star (φ (y, x))) ∧
    (∀ x : H, 0 ≤ IsROrC.re (φ (x, x))) ∧
      (∀ x : H, φ (x, x) = 0 ↔ x = 0) ∧
        (∀ x y z : H, φ (x + y, z) = φ (x, z) + φ (y, z)) ∧
          ∀ (x y : H) (α : 𝕜), φ (α • x, y) = starRingEnd 𝕜 α * φ (x, y)

/--
A linear functional $f$ on $M_n$ is positive and faithful if and only if $(x,y)\mapsto f(x^*y)$ defines an inner product on $M_n$. -/
theorem Module.Dual.isFaithfulPosMap_iff_isInner_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ↔ IsInner fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ ⬝ xy.2) :=
  by
  let ip := fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ ⬝ xy.2)
  have hip : ∀ x y, ip (x, y) = φ (xᴴ ⬝ y) := fun x y => rfl
  have Hip :
    (∀ x y z, ip (x + y, z) = ip (x, z) + ip (y, z)) ∧
      ∀ (x y) (α : ℂ), ip (α • x, y) = starRingEnd ℂ α * ip (x, y) :=
    by
    simp only [ip]
    simp_rw [conj_transpose_add, Matrix.add_mul, map_add, conj_transpose_smul, Matrix.smul_mul,
      SMulHomClass.map_smul, Complex.star_def, smul_eq_mul, eq_self_iff_true, forall₃_true_iff,
      true_and_iff]
  simp_rw [IsInner, ← hip, Hip, eq_self_iff_true, forall₃_true_iff, true_and_iff, and_true_iff]
  constructor
  · intro h
    simp_rw [hip, ← h.1.IsReal _, star_eq_conj_transpose, conj_transpose_mul,
      conj_transpose_conj_transpose]
    have := fun x => h.1 x
    simp only [IsROrC.nonneg_def'] at this
    exact ⟨fun x y => rfl, ⟨fun x => (this x).2, h.2⟩⟩
  · intro h
    refine' ⟨_, h.2.2⟩
    simp_rw [Module.Dual.IsPosMap, star_eq_conj_transpose, mul_eq_mul, ← hip, IsROrC.nonneg_def',
      IsROrC.re_eq_complex_re, ← Complex.conj_eq_iff_re, starRingEnd_apply, ← h.1, eq_self_iff_true,
      true_and_iff]
    exact h.2.1

theorem Module.Dual.isFaithfulPosMap_of_matrix_tFAE (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    TFAE
      [φ.IsFaithfulPosMap, φ.Matrix.PosDef,
        IsInner fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ ⬝ xy.2)] :=
  by
  tfae_have 1 ↔ 2
  · exact φ.is_faithful_pos_map_iff_of_matrix
  tfae_have 1 ↔ 3
  · exact φ.is_faithful_pos_map_iff_is_inner_of_matrix
  tfae_finish

@[instance, reducible]
noncomputable def Module.Dual.IsFaithfulPosMap.normedAddCommGroup {φ : Module.Dual ℂ (Matrix n n ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] : NormedAddCommGroup (Matrix n n ℂ) :=
  haveI := φ.is_faithful_pos_map_iff_is_inner_of_matrix.mp hφ.elim
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Matrix n n ℂ) _ _ _
    { inner := fun x y => φ (xᴴ ⬝ y)
      conj_symm := fun x y => (this.1 _ _).symm
      nonneg_re := fun x => this.2.1 _
      definite := fun x hx => (this.2.2.1 _).mp hx
      add_left := fun x y z => this.2.2.2.1 _ _ _
      smul_left := fun x y r => this.2.2.2.2 _ _ _ }

@[instance, reducible]
noncomputable def Module.Dual.IsFaithfulPosMap.innerProductSpace {φ : Module.Dual ℂ (Matrix n n ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] : InnerProductSpace ℂ (Matrix n n ℂ) :=
  InnerProductSpace.ofCore _

@[instance, reducible]
noncomputable def Module.Dual.pi.normedAddCommGroup {k : Type _} [Fintype k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {φ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] : NormedAddCommGroup (∀ i, Matrix (s i) (s i) ℂ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (∀ i, Matrix (s i) (s i) ℂ) _ _ _
    { inner := fun x y => ∑ i, inner (x i) (y i)
      conj_symm := fun x y => by simp only [inner, map_sum, inner_conj_symm]
      nonneg_re := fun x => by
        simp only [inner, map_sum]
        apply Finset.sum_nonneg
        intro i hi
        exact inner_self_nonneg
      definite := fun x hx => by
        simp_rw [inner] at hx
        rw [Finset.sum_eq_zero_iff_of_nonneg] at hx
        simp_rw [Finset.mem_univ, true_imp_iff, inner_self_eq_zero] at hx
        ext1 i
        exact hx i
        · intro i hi
          rw [IsROrC.nonneg_def', ← IsROrC.conj_eq_iff_re]
          exact ⟨inner_self_conj _, inner_self_nonneg⟩
      add_left := fun x y z => by
        simp_rw [inner, Pi.add_apply, inner_add_left, Finset.sum_add_distrib]
      smul_left := fun x y r => by simp_rw [inner, Pi.smul_apply, inner_smul_left, Finset.mul_sum] }

@[instance, reducible]
noncomputable def Module.Dual.pi.innerProductSpace {k : Type _} [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    {φ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] :
    InnerProductSpace ℂ (∀ i, Matrix (s i) (s i) ℂ) :=
  InnerProductSpace.ofCore _

scoped[Functional] attribute [instance] Module.Dual.IsFaithfulPosMap.normedAddCommGroup

scoped[Functional] attribute [instance] Module.Dual.IsFaithfulPosMap.innerProductSpace

scoped[Functional] attribute [instance] Module.Dual.pi.normedAddCommGroup

scoped[Functional] attribute [instance] Module.Dual.pi.innerProductSpace

