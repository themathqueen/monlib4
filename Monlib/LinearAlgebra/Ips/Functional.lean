/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Matrix.PosEqLinearMapIsPositive
import Monlib.Preq.RCLikeLe
import Monlib.LinearAlgebra.IsReal
import Monlib.LinearAlgebra.Matrix.IncludeBlock
import Monlib.LinearAlgebra.PosMap_isReal

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


open scoped Matrix BigOperators

section

variable {R k : Type _} {s : k → Type _}

theorem Matrix.cast_apply {i j : k} (x : Matrix (s i) (s i) R) (h : i = j) (p q : s j) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp x p q =
    x (by rw [h]; exact p) (by rw [h]; exact q) :=
by aesop
theorem Matrix.cast_apply' {i j : k} (x : Matrix (s j) (s j) R) (h : j = i) (p q : s i) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mpr x p q =
    x (by rw [h]; exact p) (by rw [h]; exact q) :=
by aesop

theorem Matrix.cast_hMul [Semiring R] [Π i, Fintype (s i)]
  {i j : k} (x y : Matrix (s i) (s i) R) (h : i = j) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp (x * y) =
    (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp x *
      (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp y :=
by aesop

open Matrix in
lemma includeBlock_apply_mul [CommSemiring R] [DecidableEq k] [Π i, Fintype (s i)] {i j : k} (x : Matrix (s i) (s i) R)
  (y : Matrix (s j) (s j) R) (p q : s j) :
  (includeBlock x j * y) p q
    = if i = j then (includeBlock x j * y) p q else 0 :=
by simp_rw [includeBlock_apply, dite_hMul, zero_mul]; aesop
open Matrix in
lemma includeBlock_mul_apply [CommSemiring R] [DecidableEq k]
  [Π i, Fintype (s i)] {i j : k} (x : Matrix (s j) (s j) R)
  (y : Matrix (s i) (s i) R) (p q : s j) :
  (x * includeBlock y j) p q
    = if i = j then (x * includeBlock y j) p q else 0 :=
by simp_rw [includeBlock_apply, hMul_dite, mul_zero]; aesop

lemma dite_apply' {i β : Type*} {α : i → Type*} (P : Prop) [Decidable P]
  {j : i} (f : P → (β → α j)) [Zero (α j)] (a : β) :
  (if h : P then (f h) else 0) a = if h : P then f h a else 0 :=
by aesop

end

section
variable {n : Type _} [Fintype n] [DecidableEq n]
variable {𝕜 R : Type _} [RCLike 𝕜] [CommSemiring R]

open Matrix

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- the matrix of a linear map `φ : M_n →ₗ[R] R` is given by
  `∑ i j, stdBasisMatrix j i (φ (stdBasisMatrix i j 1))`. -/
def Module.Dual.matrix (φ : Module.Dual R (Matrix n n R)) :=
∑ i : n, ∑ j : n, Matrix.stdBasisMatrix j i (φ (Matrix.stdBasisMatrix i j 1))

/-- given any linear functional `φ : M_n →ₗ[R] R`, we get `φ a = (φ.matrix ⬝ a).trace`. -/
theorem Module.Dual.apply (φ : Module.Dual R (Matrix n n R)) (a : Matrix n n R) :
    φ a = (φ.matrix * a).trace :=
  by
  simp_rw [Module.Dual.matrix, smul_stdBasisMatrix' _ _ (φ _)]
  simp_rw [Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, Matrix.trace, Matrix.diag,
    mul_apply, stdBasisMatrix_eq, boole_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ← ite_and, smul_eq_mul, mul_comm (φ _) _, ←
    smul_eq_mul, ← _root_.map_smul, ← map_sum]
  have :
    ∀ ⦃i : n⦄ ⦃j : n⦄ ⦃a : R⦄,
      stdBasisMatrix i j (a : R) = fun k l => ite (i = k ∧ j = l) (a : R) (0 : R) :=
    fun i j a => rfl
  simp_rw [← this, smul_stdBasisMatrix, smul_eq_mul, mul_one]
  rw [← matrix_eq_sum_std_basis a]

/--
we linear maps `φ_i : M_[n_i] →ₗ[R] R`, we define its direct sum as the linear map `(Π i, M_[n_i]) →ₗ[R] R`. -/
@[simps]
def Module.Dual.pi {k : Type _} [Fintype k] {s : k → Type _}
    (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R)) : Module.Dual R (PiMat R k s)
    where
  toFun a := ∑ i : k, φ i (a i)
  map_add' x y := by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [_root_.map_smul, Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

@[simps!]
def Module.Dual.pi_of {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    (φ : Module.Dual R (PiMat R k s)) :
    Π i, Module.Dual R (Matrix (s i) (s i) R) :=
λ _ => φ ∘ₗ includeBlock

/-- for direct sums, we get `φ x = ∑ i, ((φ i).matrix ⬝ x i).trace` -/
theorem Module.Dual.pi.apply {k : Type _} [Fintype k] {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R))
    (x : PiMat R k s) : Module.Dual.pi φ x = ∑ i, ((φ i).matrix * x i).trace := by
  simp_rw [Module.Dual.pi_apply, Module.Dual.apply]

lemma Module.Dual.eq_pi_of_pi {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
  (φ : Π i, Module.Dual R (Matrix (s i) (s i) R)) :
  φ = pi_of (pi φ) :=
  by
  ext i y
  simp_rw [Module.Dual.pi_of_apply, pi_apply,
    Module.Dual.apply]
  symm
  calc ∑ j : k, trace (matrix (φ j) * includeBlock y j)
    = ∑ j : k, trace (if i = j then (matrix (φ j) * includeBlock y j) else 0) :=
      by congr; ext; congr; simp only [includeBlock_apply, hMul_dite, mul_zero]; aesop
    _ = ∑ j : k, if i = j then trace (matrix (φ j) * includeBlock y j) else 0 :=
      by congr; ext; aesop
    _ = trace (matrix (φ i) * includeBlock y i) :=
      by simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = trace (matrix (φ i) * y) := by simp only [includeBlock_apply_same]

lemma Module.Dual.eq_pi_pi_of {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
  (φ : Module.Dual R (PiMat R k s) ) :
  φ = pi (pi_of φ) :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp_rw [Module.Dual.pi_apply, Module.Dual.pi_of_apply, ← map_sum,
    sum_includeBlock]

theorem Module.Dual.pi.apply' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R))
    (x : PiMat R k s) :
    Module.Dual.pi φ x
      = ∑ i, (blockDiagonal' (includeBlock (φ i).matrix) * blockDiagonal' x).trace :=
  by
  symm
  simp_rw [← blockDiagonal'_mul]
  calc
    ∑ x_1 : k, (blockDiagonal' fun k_1 : k => includeBlock (φ x_1).matrix k_1 * x k_1).trace =
        ∑ x_1 : k, (blockDiagonal' fun k_1 => (includeBlock (φ x_1).matrix * x) k_1).trace :=
      rfl
    _ = ∑ x_1 : k, (blockDiagonal' fun k_1 =>
      ((includeBlock ((φ x_1).matrix * x x_1)) k_1)).trace :=
        by
        congr
        ext
        congr
        ext
        simp only [includeBlock_hMul]
    _ = ∑ x_1 : k, (blockDiagonal' (includeBlock
      ((φ x_1).matrix * x x_1))).trace := rfl
    _ = ∑ x_1 : k, (blockDiagonal' (includeBlock
      ((fun i => (φ i).matrix * x i) x_1))).trace := rfl
    _ = ∑ x_1, ((φ x_1).matrix * x x_1).trace :=
      by
      congr
      ext i
      rw [blockDiagonal'_includeBlock_trace (fun i => (φ i).matrix * x i) i]
    _ = pi φ x := (Module.Dual.pi.apply _ _).symm

theorem Module.Dual.pi_apply'' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    (φ : Module.Dual R (PiMat R k s))
    (x : PiMat R k s) :
    φ x = ∑ i, ((pi_of φ i).matrix * x i).trace :=
by simp_rw [← Module.Dual.apply, ← pi_apply, ← eq_pi_pi_of]

theorem Module.Dual.apply_eq_of (φ : Module.Dual R (Matrix n n R)) (x : Matrix n n R)
    (h : ∀ a, φ a = (x * a).trace) : x = φ.matrix :=
  by
  simp_rw [Module.Dual.apply, ← Matrix.ext_iff_trace] at h
  exact h.symm

/--
Any linear functional $f$ on $M_n$ is given by a unique matrix $Q \in M_n$ such that $f(x)=\operatorname{Tr}(Qx)$ for any $x \in M_n$. -/
theorem Module.Dual.eq_trace_unique (φ : Module.Dual R (Matrix n n R)) :
    ∃! Q : Matrix n n R, ∀ a : Matrix n n R, φ a = (Q * a).trace :=
  by
  use φ.matrix
  simp_rw [Module.Dual.apply, forall_true_iff, true_and_iff, ←
    Matrix.ext_iff_trace, eq_comm, imp_self, forall_true_iff]

def Module.Dual.pi' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
  [∀ i, DecidableEq (s i)] (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R)) :
  Module.Dual R (BlockDiagonals R k s) :=
Module.Dual.pi φ ∘ₗ isBlockDiagonalPiAlgEquiv.toLinearMap

/-- `⨁_i φ_i ι_i (x_i) = φ_i (x_i)` -/
theorem Module.Dual.pi.apply_single_block {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (φ : Π i, Matrix (s i) (s i) R →ₗ[R] R)
  (x : Π i, Matrix (s i) (s i) R) (i : k) :
  (Module.Dual.pi φ) (includeBlock (x i)) = φ i (x i) :=
  by
  simp_rw [Module.Dual.pi_apply, Module.Dual.apply]
  calc ∑ x_1 : k, trace (matrix (φ x_1) * includeBlock (x i) x_1)
      = ∑ x_1 : k, trace (if i = x_1 then matrix (φ x_1) * x x_1 else 0) :=
      by
        congr; ext; congr
        simp_rw [includeBlock_apply, hMul_dite, mul_zero]
        aesop
    _ = ∑ x_1 : k, ∑ x_2 : s x_1, (if i = x_1 then matrix (φ x_1) * x x_1 else 0) x_2 x_2 := rfl
    _ = ∑ x_1 : k, ∑ x_2 : s x_1, (if i = x_1 then (matrix (φ x_1) * x x_1) x_2 x_2 else 0) :=
      by congr; ext; congr; ext; rw [ite_apply, ite_apply, zero_apply]
    _ = trace (matrix (φ i) * x i) := ?_
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rfl

theorem Module.Dual.pi.apply_single_block' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (φ : Π i, Matrix (s i) (s i) R →ₗ[R] R)
  {i : k} (x : Matrix (s i) (s i) R) :
  (Module.Dual.pi φ) (includeBlock x) = φ i x :=
by
  let x' := includeBlock x
  have hx : includeBlock x = includeBlock (x' i) := by simp_rw [x', includeBlock_apply_same]
  rw [hx, apply_single_block]
  simp_rw [x', includeBlock_apply_same]

open scoped ComplexOrder

open scoped DirectSum

/-- A linear functional $φ$ on $M_n$ is positive if $0 ≤ φ (x^*x)$ for all $x \in M_n$. -/
def Module.Dual.IsPosMap {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
    (φ : Module.Dual 𝕜 A) : Prop :=
  ∀ a : A, 0 ≤ φ (star a * a)

open scoped MatrixOrder
lemma Matrix.nonneg_iff {k : Type*} [Fintype k]
  [DecidableEq k] {x : Matrix k k ℂ} :
  0 ≤ x ↔ ∃ y : Matrix k k ℂ, x = star y * y :=
by rw [nonneg_def]; exact posSemidef_iff_eq_transpose_mul_self
lemma PiMat.nonneg_iff {k : Type _} [Fintype k]
  [DecidableEq k] {s : k → Type _} [Π i, Fintype (s i)] [Π i, DecidableEq (s i)]
  {x : PiMat ℂ k s} :
  0 ≤ x ↔ ∃ y : PiMat ℂ k s, x = star y * y :=
by
  simp_rw [Pi.le_def, Pi.zero_apply, Pi.mul_def, Pi.star_apply, Matrix.nonneg_iff,
    Function.funext_iff]
  exact ⟨λ h => ⟨(λ i => (h i).choose), λ _ => (h _).choose_spec⟩,
    λ h a => ⟨h.choose a, h.choose_spec _⟩⟩

lemma dual_isPosMap_of_linearMap_isPosMap {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
  [PartialOrder A] [StarOrderedRing A] {φ : Module.Dual 𝕜 A} (h : LinearMap.IsPosMap φ) :
  φ.IsPosMap :=
λ _ => h (star_mul_self_nonneg _)

lemma Module.Dual.piIsPosMap_iff {k : Type _} [Fintype k]
  [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
  (φ : Module.Dual 𝕜 (PiMat 𝕜 k s)) :
  φ.IsPosMap ↔ ∀ i, (pi_of φ i).IsPosMap :=
by
  constructor
  . intro h i x
    specialize h (includeBlock x)
    simp_rw [includeBlock_conjTranspose, includeBlock_hMul_same] at h
    exact h
  . intro h x
    simp_rw [IsPosMap, pi_of_apply] at h
    nth_rw 1 [← sum_includeBlock x]
    simp_rw [star_sum, Finset.sum_mul, includeBlock_conjTranspose,
      includeBlock_hMul, map_sum]
    exact Finset.sum_nonneg (fun _ _ => h _ _)

lemma Module.Dual.pi_isPosMap_iff {k : Type _} [Fintype k]
  [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
  (φ : Π i, Module.Dual 𝕜 (Matrix (s i) (s i) 𝕜)) :
  (pi φ).IsPosMap ↔ ∀ i, (φ i).IsPosMap :=
by
  rw [Module.Dual.piIsPosMap_iff]
  simp_rw [← eq_pi_of_pi]

/-- A linear functional $φ$ on $M_n$ is unital if $φ(1) = 1$. -/
def Module.Dual.IsUnital {A : Type _} [AddCommMonoid A] [Module R A] [One A] (φ : Module.Dual R A) :
    Prop :=
  φ (1 : A) = 1

/-- A linear functional is called a state if it is positive and unital -/
class Module.Dual.IsState {A : Type _} [Semiring A] [StarRing A] [Module 𝕜 A] (φ : Module.Dual 𝕜 A) :
    Prop :=
toIsPosMap : φ.IsPosMap
toIsUnital : φ.IsUnital

lemma Module.Dual.IsState_iff {A : Type _} [Semiring A] [StarRing A] [Module 𝕜 A]
  (φ : Module.Dual 𝕜 A) : φ.IsState ↔ φ.IsPosMap ∧ φ.IsUnital :=
⟨fun h => ⟨h.toIsPosMap, h.toIsUnital⟩, fun h => ⟨h.1, h.2⟩⟩

theorem Module.Dual.isPosMap_of_matrix (φ : Module.Dual 𝕜 (Matrix n n 𝕜)) :
    φ.IsPosMap ↔ ∀ a : Matrix n n 𝕜, a.PosSemidef → 0 ≤ φ a := by
  simp_rw [posSemidef_iff, exists_imp, Module.Dual.IsPosMap, forall_eq_apply_imp_iff,
    star_eq_conjTranspose]

/--
A linear functional $f$ on $M_n$ is said to be faithful if $f(x^*x)=0$ if and only if $x=0$ for any $x \in M_n$. -/
def Module.Dual.IsFaithful {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
    (φ : Module.Dual 𝕜 A) : Prop :=
  ∀ a : A, φ (star a * a) = 0 ↔ a = 0

lemma Matrix.includeBlock_eq_zero {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {i : k}
  {x : Matrix (s i) (s i) R} :
  includeBlock x = 0 ↔ x = 0 :=
by
  simp_rw [Function.funext_iff, Pi.zero_apply, includeBlock_apply,
    dite_eq_right_iff, eq_mp_eq_cast]
  exact ⟨λ h => (h i rfl), by rintro rfl a rfl; rfl⟩

lemma Module.Dual.piIsFaithful_iff {k : Type _} [Fintype k]
  [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
  {φ : Module.Dual 𝕜 (PiMat 𝕜 k s)} (hφ : φ.IsPosMap) :
  φ.IsFaithful ↔ ∀ i, (pi_of φ i).IsFaithful :=
by
  constructor
  . intro h i x
    specialize h (includeBlock x)
    simp_rw [includeBlock_conjTranspose, includeBlock_hMul_same,
      includeBlock_eq_zero] at h
    exact h
  . intro h x
    simp_rw [IsFaithful, pi_of_apply] at h
    nth_rw 1 [← sum_includeBlock x]
    simp_rw [star_sum, Finset.sum_mul, includeBlock_conjTranspose,
      includeBlock_hMul, map_sum]
    refine ⟨λ h1 => ?_, λ h => by simp_rw [h, Pi.zero_apply, mul_zero, map_zero,
      Finset.sum_const_zero]⟩
    ext1 i
    rw [Pi.zero_apply]
    rw [Finset.sum_eq_zero_iff_of_nonneg] at h1
    simp only [Finset.mem_univ, forall_true_left, ← star_eq_conjTranspose, h] at h1
    exact h1 i
    . intro i hi
      rw [piIsPosMap_iff] at hφ
      exact hφ _ _

theorem Module.Dual.isFaithful_of_matrix (φ : Module.Dual 𝕜 (Matrix n n 𝕜)) :
    φ.IsFaithful ↔ ∀ a : Matrix n n 𝕜, a.PosSemidef → (φ a = 0 ↔ a = 0) := by
  simp_rw [posSemidef_iff, exists_imp, Module.Dual.IsFaithful, forall_eq_apply_imp_iff,
    conjTranspose_mul_self_eq_zero, star_eq_conjTranspose]

/--
A linear functional $f$ is positive if and only if there exists a unique positive semi-definite matrix $Q\in M_n$ such $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$.  -/
theorem Module.Dual.isPosMap_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsPosMap ↔ φ.matrix.PosSemidef := by
  constructor
  · intro hs
    rw [Module.Dual.isPosMap_of_matrix] at hs
    simp only [Module.Dual.apply] at hs
    have thiseq : ∀ y, star y ⬝ᵥ φ.matrix *ᵥ y = (φ.matrix * vecMulVec y (star y)).trace :=
      by
      intro y
      rw [vecMulVec_eq, trace_mul_cycle', ← col_mulVec]
      simp_rw [Matrix.trace_iff', row_mul_col_apply, Fintype.univ_punit, Finset.sum_const,
        Finset.card_singleton, nsmul_eq_mul, Nat.cast_one, one_mul]
    simp_rw [PosSemidef.complex, thiseq]
    intro y
    refine' hs _ _
    exact vecMulVec_posSemidef _
  · intro hy y
    rw [φ.apply, ← Matrix.mul_assoc]
    exact hy.trace_conjTranspose_hMul_self_nonneg _

/--
A linear functional $f$ is a state if and only if there exists a unique positive semi-definite matrix $Q\in M_n$ such that its trace equals $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
theorem Module.Dual.isState_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsState ↔ φ.matrix.PosSemidef ∧ φ.matrix.trace = 1 := by
  simp_rw [Module.Dual.IsState_iff, Module.Dual.isPosMap_iff_of_matrix, Module.Dual.IsUnital,
    Module.Dual.apply, Matrix.mul_one]

/--
A positive linear functional $f$ is faithful if and only if there exists a positive definite matrix such that $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
theorem Module.Dual.IsPosMap.isFaithful_iff_of_matrix {φ : Module.Dual ℂ (Matrix n n ℂ)}
    (hs : φ.IsPosMap) : φ.IsFaithful ↔ φ.matrix.PosDef :=
  by
  have hs' := hs
  rw [Module.Dual.isPosMap_of_matrix] at hs'
  rw [Module.Dual.isFaithful_of_matrix]
  constructor
  · rw [Module.Dual.isPosMap_iff_of_matrix] at hs
    intro HHH
    · refine' ⟨hs.1, _⟩
      intro x hx
      have : star x ⬝ᵥ φ.matrix.mulVec x = (φ.matrix * vecMulVec x (star x)).trace :=
        by
        rw [vecMulVec_eq, trace_mul_cycle', ← col_mulVec]
        simp_rw [Matrix.trace_iff', row_mul_col_apply, Fintype.univ_punit, Finset.sum_const,
          Finset.card_singleton, nsmul_eq_mul, Nat.cast_one, one_mul]
      rw [this]
      have this2 := HHH (vecMulVec x (star x)) (vecMulVec_posSemidef _)
      have this3 := hs' (vecMulVec x (star x)) (vecMulVec_posSemidef _)
      rw [le_iff_eq_or_lt] at this3
      rcases this3 with (this3 | this32)
      · rw [eq_comm, this2, vecMulVec_eq_zero_iff] at this3
        contradiction
      · rw [← Module.Dual.apply]
        exact this32
  · intro hQ a ha
    refine' ⟨fun h => _, fun h => by rw [h, map_zero]⟩
    obtain ⟨b, rfl⟩ := (posSemidef_iff _).mp ha
    rw [Module.Dual.apply, ← Matrix.mul_assoc,
      Nontracial.trace_conjTranspose_hMul_self_eq_zero hQ] at h
    rw [h, Matrix.mul_zero]

-- def Module.Dual.IsFaithfulPosMap {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
--     (φ : Module.Dual 𝕜 A) : Prop :=
--   φ.IsPosMap ∧ φ.IsFaithful
@[class]
structure Module.Dual.IsFaithfulPosMap {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A] (φ : Module.Dual 𝕜 A) : Prop :=
toIsPosMap : φ.IsPosMap
toIsFaithful : φ.IsFaithful

lemma Module.Dual.IsFaithfulPosMap_iff {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
  (φ : Module.Dual 𝕜 A) : φ.IsFaithfulPosMap ↔ φ.IsPosMap ∧ φ.IsFaithful :=
⟨fun h => ⟨h.toIsPosMap, h.toIsFaithful⟩, fun h => ⟨h.1, h.2⟩⟩

/--
A linear functional $φ$ is a faithful and positive if and only if there exists a unique positive definite matrix $Q$ such that $φ(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
theorem Module.Dual.isFaithfulPosMap_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ↔ φ.matrix.PosDef :=
  by
  refine' ⟨fun h => h.1.isFaithful_iff_of_matrix.mp h.2, _⟩
  intro hQ
  simp_rw [Module.Dual.IsFaithfulPosMap_iff, Module.Dual.IsFaithful, Module.Dual.isPosMap_iff_of_matrix,
    hQ.posSemidef, true_and_iff, Module.Dual.apply, star_eq_conjTranspose,
    ← Matrix.mul_assoc, Nontracial.trace_conjTranspose_hMul_self_eq_zero hQ,
    forall_const]

/--
A state is faithful $f$ if and only if there exists a unique positive definite matrix $Q\in M_n$ with trace equal to $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x \in M_n$. -/
theorem Module.Dual.IsState.isFaithful_iff_of_matrix {φ : Module.Dual ℂ (Matrix n n ℂ)}
    (hs : φ.IsState) : φ.IsFaithful ↔ φ.matrix.PosDef ∧ φ.matrix.trace = 1 :=
  by
  rw [hs.1.isFaithful_iff_of_matrix]
  refine' ⟨fun hQ => ⟨hQ, _⟩, fun hQ => hQ.1⟩
  · rw [Module.Dual.isState_iff_of_matrix] at hs
    exact hs.2

theorem Module.Dual.isFaithful_state_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsState ∧ φ.IsFaithful ↔ φ.matrix.PosDef ∧ φ.matrix.trace = 1 :=
  by
  refine' ⟨fun h => h.1.isFaithful_iff_of_matrix.mp h.2, _⟩
  intro hQ
  simp_rw [Module.Dual.IsFaithful, Module.Dual.isState_iff_of_matrix, hQ.2, hQ.1.posSemidef,
    true_and_iff]
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
    φ.IsPosMap ∧ φ.IsTracial ↔ ∃ α : NNReal, φ.matrix = ((α : ℝ) : ℂ) • 1 :=
  by
  constructor
  · simp_rw [Module.Dual.isPosMap_iff_of_matrix]
    rintro ⟨hQ, h2⟩
    simp_rw [Module.Dual.IsTracial, Module.Dual.apply, Matrix.trace, Matrix.diag,
      mul_apply] at h2
    let Q := φ.matrix
    have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 := fun p q r =>
      calc
        Q p q =
            ∑ i, ∑ j, Q i j * ∑ k, (stdBasisMatrix q r 1) j k * (stdBasisMatrix r p 1) k i :=
          by
          simp only [stdBasisMatrix, boole_mul, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, eq_self_iff_true, if_true,
            mul_ite, MulZeroClass.mul_zero, mul_one]
        _ = ∑ i, ∑ j, Q i j * ∑ k, (stdBasisMatrix r p 1) j k * (stdBasisMatrix q r 1) k i :=
          by rw [h2]
        _ = ite (p = q) (Q r r) 0 := by
          simp only [stdBasisMatrix, boole_mul, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite,
            MulZeroClass.mul_zero, mul_one]
    by_cases h : IsEmpty n
    · use 1
      haveI := h
      simp only [eq_iff_true_of_subsingleton]
    rw [not_isEmpty_iff] at h
    let i : n := h.some
    have HH : Q = diagonal fun _ : n => Q i i :=
      by
      ext
      exact this _ _ i
    have this' : ∀ p, Q p p = RCLike.re (Q p p) :=
      by
      intro p
      rw [eq_comm]
      simp_rw [RCLike.re_eq_complex_re, ← Complex.conj_eq_iff_re, ← RCLike.star_def, ← Matrix.star_apply,
        star_eq_conjTranspose, hQ.1.eq]
    have : 0 ≤ Q i i := by
      rw [PosSemidef.complex] at hQ
      specialize hQ fun j => ite (i = j) 1 0
      simp_rw [dotProduct, mulVec, dotProduct, Pi.star_apply, star_ite, star_zero, star_one,
        boole_mul, mul_boole, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hQ
      exact hQ
    have thisthis : 0 ≤ RCLike.re (Q i i) :=
      by
      rw [RCLike.nonneg_def'] at this
      exact this.2
    let α : NNReal := ⟨RCLike.re (Q i i), thisthis⟩
    have hα' : RCLike.re (Q i i) = α := rfl
    refine' ⟨α, _⟩
    · simp only [smul_eq_diagonal_mul, ← hα', Matrix.mul_one]
      rw [← this']
      exact HH
  · rintro ⟨α, hα1⟩
    simp_rw [Module.Dual.IsPosMap, Module.Dual.IsTracial, Module.Dual.apply, hα1,
      smul_mul, one_mul, trace_smul, smul_eq_mul, star_eq_conjTranspose]
    exact ⟨fun _ => mul_nonneg (RCLike.zero_le_real.mpr (NNReal.coe_nonneg α))
        (Matrix.trace_conjTranspose_hMul_self_nonneg _),
      fun _ _ => by rw [trace_mul_comm]⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/--
A linear functional is tracial and positive if and only if there exists a unique non-negative real $α$ such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
theorem Module.Dual.isTracial_pos_map_iff'_of_matrix [Nonempty n]
    (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsPosMap ∧ φ.IsTracial ↔ ∃! α : NNReal, φ.matrix = ((α : ℝ) : ℂ) • 1 :=
  by
  constructor
  · simp_rw [Module.Dual.isPosMap_iff_of_matrix]
    rintro ⟨hQ, h2⟩
    simp_rw [Module.Dual.IsTracial, Module.Dual.apply, Matrix.trace, Matrix.diag,
      mul_apply] at h2
    let Q := φ.matrix
    have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 := fun p q r =>
      calc
        Q p q =
            ∑ i, ∑ j, Q i j * ∑ k, (stdBasisMatrix q r 1) j k * (stdBasisMatrix r p 1) k i :=
          by
          simp only [stdBasisMatrix, boole_mul, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, eq_self_iff_true, if_true,
            mul_ite, MulZeroClass.mul_zero, mul_one]
        _ = ∑ i, ∑ j, Q i j * ∑ k, (stdBasisMatrix r p 1) j k * (stdBasisMatrix q r 1) k i :=
          by rw [h2]
        _ = ite (p = q) (Q r r) 0 := by
          simp only [stdBasisMatrix, boole_mul, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite,
            MulZeroClass.mul_zero, mul_one]
    let i : n := Nonempty.some (by infer_instance)
    have HH : Q = diagonal fun _ : n => Q i i :=
      by
      ext
      exact this _ _ i
    have this' : ∀ p, Q p p = RCLike.re (Q p p) :=
      by
      intro p
      rw [eq_comm]
      simp_rw [RCLike.re_eq_complex_re, ← Complex.conj_eq_iff_re, ← RCLike.star_def, ← Matrix.star_apply,
        star_eq_conjTranspose, hQ.1.eq]
    have : 0 ≤ Q i i := by
      rw [PosSemidef.complex] at hQ
      specialize hQ fun j => ite (i = j) 1 0
      simp_rw [dotProduct, mulVec, dotProduct, Pi.star_apply, star_ite, star_zero, star_one,
        boole_mul, mul_boole, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hQ
      exact hQ
    have thisthis : 0 ≤ RCLike.re (Q i i) :=
      by
      rw [RCLike.nonneg_def'] at this
      exact this.2
    let α : NNReal := ⟨RCLike.re (Q i i), thisthis⟩
    have hα' : RCLike.re (Q i i) = α := rfl
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
      simp_rw [α, Q, hy]
      rfl
  · rintro ⟨α, ⟨hα1, _⟩⟩
    simp_rw [Module.Dual.IsPosMap, Module.Dual.IsTracial, Module.Dual.apply, hα1,
      smul_mul, one_mul, trace_smul]
    exact ⟨fun _ =>  mul_nonneg (RCLike.zero_le_real.mpr (NNReal.coe_nonneg α))
        (Matrix.trace_conjTranspose_hMul_self_nonneg _),
      fun _ _ => by rw [trace_mul_comm]⟩

/--
A linear functional $f$ is tracial positive and faithful if and only if there exists a positive real number $\alpha$ such that $f\colon x\mapsto \alpha \operatorname{Tr}(x)$. -/
theorem Module.Dual.isTracial_faithful_pos_map_iff_of_matrix [Nonempty n]
    (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ∧ φ.IsTracial ↔
      ∃! α : { x : NNReal // 0 < x }, φ.matrix = (((α : NNReal) : ℝ) : ℂ) • 1 :=
  by
  rw [Module.Dual.IsFaithfulPosMap_iff, @and_comm φ.IsPosMap, and_assoc,
    Module.Dual.isTracial_pos_map_iff'_of_matrix]
  constructor
  · rintro ⟨h1, ⟨α, hα, h⟩⟩
    have : 0 < (α : ℝ) := by
      rw [NNReal.coe_pos, pos_iff_ne_zero]
      intro HH
      rw [Module.Dual.IsFaithful] at h1
      specialize h1 ((1 : Matrix n n ℂ)ᴴ * (1 : Matrix n n ℂ))
      simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Module.Dual.apply,
        star_eq_conjTranspose] at h1
      simp_rw [HH, NNReal.coe_zero, Complex.ofReal_zero, zero_smul] at hα
      rw [hα, trace_zero, eq_self_iff_true, true_iff_iff] at h1
      simp only [one_ne_zero'] at h1
    let α' : { x : NNReal // 0 < x } := ⟨α, this⟩
    have : α = α' := rfl
    refine' ⟨α', hα, fun y hy => _⟩
    simp_rw [← Subtype.coe_inj] at hy ⊢
    norm_cast
    exact h _ hy
  · rintro ⟨α, ⟨h1, _⟩⟩
    have : 0 < (α : NNReal) := Subtype.mem α
    refine' ⟨_, ⟨α, h1, fun y hy => _⟩⟩
    ·
      simp_rw [Module.Dual.IsFaithful, Module.Dual.apply, h1, Matrix.smul_mul, Matrix.one_mul,
        trace_smul, smul_eq_zero, Complex.ofReal_eq_zero, NNReal.coe_eq_zero, ne_zero_of_lt this,
        false_or_iff, star_eq_conjTranspose,
        trace_conjTranspose_hMul_self_eq_zero, forall_true_iff]
    rw [h1, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at hy
    simp only [one_ne_zero', or_false_iff, RCLike.ofReal_inj, NNReal.coe_inj,
      Complex.ofReal_inj, NNReal.coe_inj] at hy
    exact hy.symm

-- lemma linear_map.is_tracial_state_iff [nonempty n] (φ : matrix n n ℂ →ₗ[ℂ] ℂ) :
--   (φ.is_state ∧ φ.is_tracial) ↔ ∃ α : ℂ, φ.matrix = α • 1 ∧ α * (1 : matrix n n ℂ).trace = 1 :=
-- begin
--   split,
--   { simp_rw [linear_map.is_state_iff],
--     -- rintros ⟨⟨Q, ⟨hQ1, hQ2, hQ3⟩, h1⟩, h2⟩,
--     simp_rw [linear_map.is_tracial, hQ3, matrix.trace, matrix.diag, mul_apply] at h2,
--     have : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 :=
--     λ p q r, calc Q p q = ∑ i j, Q i j
--       * ∑ k, (stdBasisMatrix q r 1) j k * (stdBasisMatrix r p 1) k i :
--     by { simp only [stdBasisMatrix, boole_mul, ite_and, finset.sum_ite_irrel,
--       finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, eq_self_iff_true, if_true,
--       mul_ite, mul_zero, mul_one], }
--       ... = ∑ i j, Q i j
--       * ∑ k, (stdBasisMatrix r p 1) j k * (stdBasisMatrix q r 1) k i : by rw h2
--       ... = ite (p = q) (Q r r) 0 :
--     by { simp only [stdBasisMatrix, boole_mul, ite_and, finset.sum_ite_irrel,
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
--         simp only [← diagonal_one, ← diagonal_smul, posSemidef.diagonal],
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
--         specialize hy3 (stdBasisMatrix j i (1 : ℂ)),
--         simp_rw [stdBasisMatrix.trace, matrix.trace, matrix.diag, mul_apply,
--           stdBasisMatrix, mul_boole, ite_and] at hy3,
--         simp only [finset.sum_ite_eq, finset.mem_univ, if_true] at hy3,
--         simp_rw @eq_comm _ j i at hy3,
--         exact hy3.symm, }, },
--     { intros x y,
--       rw [hα1, trace_mul_comm, ← hα1], }, },
-- end
theorem Matrix.ext_iff_trace' {R m n : Type _} [Semiring R] [StarRing R] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (A B : Matrix m n R) :
    (∀ x, (xᴴ * A).trace = (xᴴ * B).trace) ↔ A = B :=
  by
  refine' ⟨fun h => _, fun h x => by rw [h]⟩
  ext i j
  specialize h (stdBasisMatrix i j (1 : R))
  simp_rw [stdBasisMatrix_conjTranspose, star_one, Matrix.stdBasisMatrix_hMul_trace] at h
  exact h

theorem Module.Dual.isReal_iff {φ : Module.Dual ℂ (Matrix n n ℂ)} :
    LinearMap.IsReal φ ↔ φ.matrix.IsHermitian := by
  simp_rw [LinearMap.IsReal, Module.Dual.apply, trace_star, conjTranspose_mul,
    star_eq_conjTranspose, trace_mul_comm φ.matrix, Matrix.ext_iff_trace', IsHermitian, eq_comm]

theorem Module.Dual.IsPosMap.isReal {φ : Module.Dual ℂ (Matrix n n ℂ)} (hφ : φ.IsPosMap) :
    LinearMap.IsReal φ := by
  rw [Module.Dual.isPosMap_iff_of_matrix] at hφ
  rw [Module.Dual.isReal_iff]
  exact hφ.1

theorem Module.Dual.pi.IsPosMap.isReal {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    (hψ : ∀ i, (ψ i).IsPosMap) : LinearMap.IsReal (Module.Dual.pi ψ) := by
  simp_rw [LinearMap.IsReal, Module.Dual.pi_apply, star_sum, Pi.star_apply, (hψ _).isReal _,
    forall_true_iff]

/-- A function $H \times H \to 𝕜$ defines an inner product if it satisfies the following. -/
def IsInner {H : Type _} [AddCommMonoid H] [Module 𝕜 H] (φ : H × H → 𝕜) : Prop :=
  (∀ x y : H, φ (x, y) = star (φ (y, x))) ∧
    (∀ x : H, 0 ≤ RCLike.re (φ (x, x))) ∧
      (∀ x : H, φ (x, x) = 0 ↔ x = 0) ∧
        (∀ x y z : H, φ (x + y, z) = φ (x, z) + φ (y, z)) ∧
          ∀ (x y : H) (α : 𝕜), φ (α • x, y) = starRingEnd 𝕜 α * φ (x, y)

/--
A linear functional $f$ on $M_n$ is positive and faithful if and only if $(x,y)\mapsto f(x^*y)$ defines an inner product on $M_n$. -/
theorem Module.Dual.isFaithfulPosMap_iff_isInner_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ↔ IsInner fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ * xy.2) :=
  by
  let ip := fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ * xy.2)
  have hip : ∀ x y, ip (x, y) = φ (xᴴ * y) := fun x y => rfl
  have Hip :
    (∀ x y z, ip (x + y, z) = ip (x, z) + ip (y, z)) ∧
      ∀ (x y) (α : ℂ), ip (α • x, y) = starRingEnd ℂ α * ip (x, y) :=
    by
    simp only [ip]
    simp_rw [conjTranspose_add, Matrix.add_mul, map_add, conjTranspose_smul, Matrix.smul_mul,
      _root_.map_smul, Complex.star_def, smul_eq_mul, forall₃_true_iff,
      true_and_iff]
  simp_rw [IsInner, ← hip, Hip, forall₃_true_iff, true_and_iff, and_true_iff]
  constructor
  · intro h
    simp_rw [hip, ← h.1.isReal _, star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose]
    have := fun x => h.1 x
    simp only [@RCLike.nonneg_def' ℂ] at this
    exact ⟨fun _ _ => trivial, ⟨fun x => (this x).2, h.2⟩⟩
  · intro h
    refine' ⟨_, h.2.2⟩
    simp_rw [Module.Dual.IsPosMap, star_eq_conjTranspose, ← hip, @RCLike.nonneg_def' ℂ,
      ← @RCLike.conj_eq_iff_re ℂ _ (ip (_,_)),
      starRingEnd_apply, ← h.1, true_and_iff]
    exact h.2.1

theorem Module.Dual.isFaithfulPosMap_of_matrix_tfae (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    List.TFAE
      [φ.IsFaithfulPosMap, φ.matrix.PosDef,
        IsInner fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ * xy.2)] :=
  by
  tfae_have 1 ↔ 2
  · exact φ.isFaithfulPosMap_iff_of_matrix
  tfae_have 1 ↔ 3
  · exact φ.isFaithfulPosMap_iff_isInner_of_matrix
  tfae_finish

end
section

variable {n : Type _} [Fintype n] [DecidableEq n] (φ : Module.Dual ℂ (Matrix n n ℂ))

@[reducible]
noncomputable def Module.Dual.NormedAddCommGroup [hφ : φ.IsFaithfulPosMap] :
  _root_.NormedAddCommGroup (Matrix n n ℂ) :=
  -- have := φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Matrix n n ℂ) _ _ _
    { inner := fun x y => φ (xᴴ * y)
      conj_symm := fun _ _ => ((φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).1 _ _).symm
      nonneg_re := fun _ => (φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).2.1 _
      definite := fun _ hx => ((φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).2.2.1 _).mp hx
      add_left := fun _ _ _ => (φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).2.2.2.1 _ _ _
      smul_left := fun _ _ _ => (φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).2.2.2.2 _ _ _ }


-- set_option trace.Meta.synthInstance true
-- set_option pp.all true
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.isLevelDefEq true
-- set_option synthInstance.maxHeartbeats 100000
-- set_option synthInstance.maxSize 100000

set_option synthInstance.checkSynthOrder false in
scoped[Functional] attribute [instance] Module.Dual.NormedAddCommGroup
open scoped Functional

variable [hφ : φ.IsFaithfulPosMap]

-- #synth _root_.NormedAddCommGroup (Matrix n n ℂ)
-- #check inferInstanceAs (NormedAddCommGroup (Matrix n n ℂ))
-- #check @inferInstance _ (hφ)

@[reducible]
noncomputable def Module.Dual.InnerProductSpace :
    -- letI := hφ.NormedAddCommGroup
  _root_.InnerProductSpace ℂ (Matrix n n ℂ) :=
InnerProductSpace.ofCore _

scoped[Functional] attribute [instance] Module.Dual.InnerProductSpace

end

open scoped Functional

variable {k : Type _} [Fintype k] {s : k → Type _}
    [Π i, Fintype (s i)] [Π i, DecidableEq (s i)]

@[reducible]
noncomputable def Module.Dual.PiNormedAddCommGroup
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [Π i, (φ i).IsFaithfulPosMap] :
  _root_.NormedAddCommGroup (PiMat ℂ k s) :=
-- by
  -- letI := fun i => (hφ i).NormedAddCommGroup
  PiLp.normedAddCommGroup 2 _
  -- letI := fun i => (hφ i).InnerProductSpace
  -- @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Π i, Matrix (s i) (s i) ℂ) _ _ _
  --   { inner := fun x y => ∑ i, inner (x i) (y i)
  --     conj_symm := fun x y => by
  --       simp_rw [map_sum]
  --       congr; ext
  --       rw [inner_conj_symm]
  --     nonneg_re := fun x => by
  --       simp only [inner, map_sum]
  --       apply Finset.sum_nonneg
  --       intro i hi
  --       exact inner_self_nonneg
  --     definite := fun x hx => by
  --       simp_rw [inner] at hx
  --       rw [Finset.sum_eq_zero_iff_of_nonneg] at hx
  --       simp_rw [Finset.mem_univ, true_imp_iff, inner_self_eq_zero] at hx
  --       ext1 i
  --       exact hx i
  --       · intro i hi
  --         rw [RCLike.nonneg_def', ← RCLike.conj_eq_iff_re]
  --         exact ⟨inner_self_conj _, inner_self_nonneg⟩
  --     add_left := fun x y z => by
  --       simp_rw [inner, Pi.add_apply, inner_add_left, Finset.sum_add_distrib]
  --     smul_left := fun x y r => by simp_rw [inner, Pi.smul_apply, inner_smul_left, Finset.mul_sum] }

set_option synthInstance.checkSynthOrder false in
scoped[Functional] attribute [instance] Module.Dual.PiNormedAddCommGroup

@[reducible]
noncomputable def Module.Dual.pi.InnerProductSpace
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [Π i, (φ i).IsFaithfulPosMap] :
    -- letI := Module.Dual.PiNormedAddCommGroup hφ
  _root_.InnerProductSpace ℂ (PiMat ℂ k s) :=
-- letI := fun i => (hφ i).NormedAddCommGroup
-- letI := fun i => (hφ i).InnerProductSpace
PiLp.innerProductSpace _
  -- InnerProductSpace.ofCore _

scoped[Functional] attribute [instance] Module.Dual.pi.InnerProductSpace
