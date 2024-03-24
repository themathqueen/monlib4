/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis
import Monlib.Preq.Dite
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Monlib.LinearAlgebra.MyTensorProduct
import Mathlib.Data.Matrix.Kronecker
import Monlib.LinearAlgebra.ToMatrixOfEquiv

#align_import linear_algebra.my_matrix.includeBlock

/-!

# Include block

 This file defines `matrix.includeBlock` which immitates `direct_sum.component_of` but for `pi` instead of `direct_sum` :TODO:

 The direct sum in these files are sort of misleading.

-/


open scoped BigOperators

theorem Finset.sum_sigma_univ {β α : Type _} [AddCommMonoid β] [Fintype α] {σ : α → Type _}
    [∀ i, Fintype (σ i)] (f : (Σ i, σ i) → β) :
    ∑ x : Σ i : α, σ i, f x = ∑ a : α, ∑ s : σ a, f (⟨a, s⟩ : Σ i, σ i) :=
  Finset.sum_sigma _ _ _

namespace Matrix

def blockDiagonal'AlgHom {o : Type _} {m' : o → Type _} {α : Type _} [Fintype o] [DecidableEq o]
    [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α] :
    (∀ i : o, Matrix (m' i) (m' i) α) →ₐ[α] Matrix (Σ i : o, m' i) (Σ i : o, m' i) α
    where
  toFun a := blockDiagonal' a
  map_one' := blockDiagonal'_one
  map_mul' a b := blockDiagonal'_mul _ _
  map_zero' := blockDiagonal'_zero
  map_add' a b := blockDiagonal'_add _ _
  commutes' a := by
    simp_rw [Algebra.algebraMap_eq_smul_one, blockDiagonal'_smul, blockDiagonal'_one]

theorem blockDiagonal'AlgHom_apply {o : Type _} {m' : o → Type _} {α : Type _} [Fintype o]
    [DecidableEq o] [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α]
    (x : ∀ i : o, Matrix (m' i) (m' i) α) : Matrix.blockDiagonal'AlgHom x = blockDiagonal' x :=
  rfl

def blockDiag'LinearMap {o : Type _} {m' n' : o → Type _} {α : Type _} [Semiring α] :
    Matrix (Σ i : o, m' i) (Σ i : o, n' i) α →ₗ[α] ∀ i : o, Matrix (m' i) (n' i) α
    where
  toFun x := Matrix.blockDiag' x
  map_add' x y := blockDiag'_add x y
  map_smul' r x := blockDiag'_smul r x

theorem blockDiag'LinearMap_apply {o : Type _} {m' : o → Type _} {n' : o → Type _} {α : Type _}
    [Semiring α] (x : Matrix (Σ i : o, m' i) (Σ i : o, n' i) α) :
    Matrix.blockDiag'LinearMap x = blockDiag' x :=
  rfl

theorem blockDiag'LinearMap_blockDiagonal'AlgHom {o : Type _} {m' : o → Type _} {α : Type _}
    [Fintype o] [DecidableEq o] [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α]
    (x : ∀ i : o, Matrix (m' i) (m' i) α) :
    Matrix.blockDiag'LinearMap (Matrix.blockDiagonal'AlgHom x) = x :=
  blockDiag'_blockDiagonal' x

theorem blockDiagonal'_ext {R : Type _} {k : Type _} {s : k → Type _}
    (x y : Matrix (Σ i, s i) (Σ i, s i) R) : x = y ↔ ∀ i j k l, x ⟨i, j⟩ ⟨k, l⟩ = y ⟨i, j⟩ ⟨k, l⟩ :=
  by
  simp only [← Matrix.ext_iff, Sigma.forall]

def IsBlockDiagonal {o : Type _} {m' n' : o → Type _} {α : Type _} [DecidableEq o] [Zero α]
    (x : Matrix (Σ i, m' i) (Σ i, n' i) α) : Prop :=
  blockDiagonal' (blockDiag' x) = x

def includeBlock {o : Type _} [DecidableEq o] {m' : o → Type _} {α : Type _} [Semiring α]
  {i : o} : Matrix (m' i) (m' i) α →ₗ[α] (Π j : o, Matrix (m' j) (m' j) α) :=
@LinearMap.single α o _ (fun j => Matrix (m' j) (m' j) α) _ _ _ i

theorem includeBlock_apply {o : Type _} [DecidableEq o] {m' : o → Type _} {α : Type _}
    [CommSemiring α] {i : o} (x : Matrix (m' i) (m' i) α) :
    (includeBlock : Matrix (m' i) (m' i) α →ₗ[α] ∀ j, Matrix (m' j) (m' j) α) x = fun j : o =>
      dite (i = j) (fun h => Eq.mp (by rw [h]) x) fun _ => 0 :=
  by
  ext j₁ j₂ j₃
  simp only [includeBlock, LinearMap.coe_single, Pi.single, Function.update, eq_comm,
    Pi.zero_apply]
  split_ifs with h <;> aesop

theorem includeBlock_hMul_same {o : Type _} [Fintype o] [DecidableEq o] {m' : o → Type _}
    {α : Type _} [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α] {i : o}
    (x y : Matrix (m' i) (m' i) α) : includeBlock x * includeBlock y = includeBlock (x * y) :=
  by
  ext i x_1 x_2
  simp_rw [includeBlock_apply, Pi.mul_apply, hMul_dite, dite_hMul, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul]
  simp only [eq_mp_eq_cast, dite_eq_ite, ite_self]
  aesop

theorem includeBlock_hMul_ne_same {o : Type _} [Fintype o] [DecidableEq o] {m' : o → Type _}
    {α : Type _} [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α] {i j : o}
    (h : i ≠ j) (x : Matrix (m' i) (m' i) α) (y : Matrix (m' j) (m' j) α) :
    includeBlock x * includeBlock y = 0 := by
  ext
  simp_rw [includeBlock_apply, Pi.mul_apply, hMul_dite, dite_hMul, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Pi.zero_apply]
  simp only [eq_mp_eq_cast, dite_eq_ite, ite_self]
  aesop

theorem includeBlock_hMul {o : Type _} [Fintype o] [DecidableEq o] {m' : o → Type _} {α : Type _}
    [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α] {i : o}
    (x : Matrix (m' i) (m' i) α) (y : ∀ j, Matrix (m' j) (m' j) α) :
    includeBlock x * y = includeBlock (x * y i) :=
  by
  ext
  simp only [includeBlock_apply, Pi.mul_apply, dite_hMul, MulZeroClass.zero_mul, dite_apply,
    Pi.zero_apply]
  split_ifs <;> aesop

theorem hMul_includeBlock {o : Type _} [Fintype o] [DecidableEq o] {m' : o → Type _} {α : Type _}
    [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommSemiring α] {i : o}
    (x : ∀ j, Matrix (m' j) (m' j) α) (y : Matrix (m' i) (m' i) α) :
    x * includeBlock y = includeBlock (x i * y) :=
  by
  ext
  simp only [includeBlock_apply, Pi.mul_apply, dite_hMul, MulZeroClass.zero_mul, dite_apply,
    Pi.zero_apply]
  split_ifs <;> aesop

open scoped BigOperators

theorem sum_includeBlock {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (x : ∀ i, Matrix (s i) (s i) R) :
    ∑ i, includeBlock (x i) = x := by
  ext
  simp only [Finset.sum_apply, includeBlock_apply, dite_apply, Pi.zero_apply, Finset.sum_dite_eq',
    Finset.mem_univ, if_true]
  rfl

theorem blockDiagonal'_includeBlock_trace {R k : Type _} [CommSemiring R] [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    (x : ∀ i, Matrix (s i) (s i) R) (j : k) :
    (blockDiagonal' (includeBlock (x j))).trace = (x j).trace :=
  by
  calc
    (blockDiagonal' (includeBlock (x j))).trace
      = ∑ i, (includeBlock (x j) i).trace :=
      by simp_rw [Matrix.trace, Matrix.diag, blockDiagonal'_apply, dif_pos,
      Finset.sum_sigma']; rfl
    _ = ∑ i, ∑ a, includeBlock (x j) i a a := rfl
    _ = ∑ i, ∑ a, dite (j = i) (fun h => by rw [← h]; exact (x j))
      (fun _ => (0 : Matrix (s i) (s i) R)) a a :=
      by simp_rw [includeBlock_apply]; rfl
    _ = ∑ i, ∑ a, dite (j = i) (fun h =>
        (by rw [← h]; exact x j : Matrix (s i) (s i) R) a a)
      (fun _ => (0 : R)) := by congr; ext; congr; ext; aesop
    _ = (x j).trace := by
        simp_rw [Finset.sum_dite_irrel, Finset.sum_const_zero,
          Finset.sum_dite_eq, Finset.mem_univ, if_true]
        rfl

open scoped Matrix

theorem stdBasisMatrix_hMul_trace {R n p : Type _} [Semiring R] [Fintype p] [DecidableEq p]
    [Fintype n] [DecidableEq n] (i : n) (j : p) (x : Matrix p n R) :
    Matrix.trace (stdBasisMatrix i j (1 : R) * x) = x j i := by
  simp_rw [Matrix.trace, Matrix.diag, mul_apply, stdBasisMatrix, boole_mul, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem ext_iff_trace {R n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    [CommSemiring R] (x y : Matrix n p R) : x = y ↔ ∀ a, (x * a).trace = (y * a).trace :=
  by
  refine' ⟨fun h a => by rw [h], fun h => _⟩
  ext i j
  specialize h (stdBasisMatrix j i 1)
  simp_rw [trace_mul_comm _ (stdBasisMatrix _ _ _), Matrix.stdBasisMatrix_hMul_trace j i] at h
  exact h

variable {R : Type _} [CommSemiring R]

theorem IsBlockDiagonal.eq {k : Type _} [DecidableEq k] {s : k → Type _}
    {x : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) :
    blockDiagonal' x.blockDiag' = x :=
  hx

theorem IsBlockDiagonal.add {k : Type _} [DecidableEq k] {s : k → Type _}
    {x y : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) (hy : y.IsBlockDiagonal) :
    (x + y).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal, blockDiag'_add, blockDiagonal'_add, hx.eq, hy.eq]

theorem IsBlockDiagonal.zero {k : Type _} [DecidableEq k] {s : k → Type _} :
    (0 : Matrix (Σ i, s i) (Σ i, s i) R).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal, blockDiag'_zero, blockDiagonal'_zero]

instance IsBlockDiagonal.HAdd {k : Type _} [DecidableEq k] {s : k → Type _} :
    Add ({ x : Matrix (Σ i, s i) (Σ i, s i) R // IsBlockDiagonal x }) where
  add x y := ⟨↑x + ↑y, Matrix.IsBlockDiagonal.add x.property y.property⟩

theorem IsBlockDiagonal.coe_add {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    {x y : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }} :
    ((x + y : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      x + y :=
  rfl

instance IsBlockDiagonal.Zero {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Zero ({ x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) where zero := ⟨0, IsBlockDiagonal.zero⟩

theorem IsBlockDiagonal.coe_zero {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    ((0 : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      0 :=
  rfl

instance addCommMonoidBlockDiagonal {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    AddCommMonoid { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where
  add_assoc x y z := by
    ext
    simp only [IsBlockDiagonal.coe_add, add_assoc]
  zero_add a := by
    ext
    simp only [IsBlockDiagonal.coe_add, IsBlockDiagonal.coe_zero, zero_add]
  add_zero a := by
    ext
    simp only [IsBlockDiagonal.coe_zero, IsBlockDiagonal.coe_add, add_zero]
  add_comm a b := by
    ext
    simp only [IsBlockDiagonal.coe_add, add_comm]
  nsmul n x := by


private theorem is_blockDiagonal.coe_sum_aux {k : Type _} [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {n : ℕ}
    {x : Fin n → { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }} :
    ((∑ i, x i : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      ∑ i, x i :=
  by
  induction' n with d hd
  · simp only [Fintype.univ_ofIsEmpty, Finset.sum_empty]; rfl
  · simp only [Fin.sum_univ_succ, Matrix.IsBlockDiagonal.coe_add, hd]

theorem IsBlockDiagonal.coe_sum {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {n : Type _} [Fintype n]
    {x : n → { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }} :
    ((∑ i, x i : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      ∑ i, x i :=
  by
  let σ : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  have : ∑ i : n, x i = ∑ i : Fin (Fintype.card n), x (σ i) :=
    by
    apply Fintype.sum_equiv σ.symm
    intro i
    simp only [Equiv.apply_symm_apply]
  rw [this]
  have : ∑ i : n, (x i : Matrix (Σ i, s i) (Σ i, s i) R) = ∑ i : Fin (Fintype.card n), x (σ i) :=
    by
    apply Fintype.sum_equiv σ.symm
    intro i
    simp only [Equiv.apply_symm_apply]
  rw [this]
  exact is_blockDiagonal.coe_sum_aux

theorem IsBlockDiagonal.smul {k : Type _} [DecidableEq k] {s : k → Type _}
    {x : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) (α : R) :
    (α • x).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal, blockDiag'_smul, blockDiagonal'_smul, hx.eq]

instance hasSmulBlockDiagonal {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    SMul R { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where smul a x :=
    ⟨a • (x : Matrix (Σ i, s i) (Σ i, s i) R), Matrix.IsBlockDiagonal.smul (Subtype.mem x) a⟩

theorem IsBlockDiagonal.coe_smul {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (a : R)
    (x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
    ((a • x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      a • ↑x :=
  rfl

instance mulActionBlockDiagonal {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    MulAction R { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where
  one_smul x := by simp only [← Subtype.val_inj, Subtype.val, one_smul]; rfl
  hMul_smul a b x := by simp only [← smul_smul, ← Subtype.val_inj, Subtype.val]; rfl

instance distribMulActionBlockDiagonal {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    DistribMulAction R { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where
  smul_zero x := by
    simp only [Subtype.ext_iff_val, Subtype.val, Matrix.IsBlockDiagonal.coe_zero, smul_zero]
  smul_add a x y := by
    simp only [Subtype.ext_iff_val, Subtype.val, Matrix.IsBlockDiagonal.coe_add,
      Matrix.IsBlockDiagonal.coe_smul, smul_add]

instance moduleBlockDiagonal {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Module R { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where
  add_smul x y a := by
    simp only [Subtype.ext_iff_val, Subtype.val, add_smul, Matrix.IsBlockDiagonal.coe_smul]
  zero_smul a :=
    by
    simp only [Subtype.ext_iff, Matrix.IsBlockDiagonal.coe_smul, zero_smul]
    rfl

theorem IsBlockDiagonal.blockDiagonal' {k : Type _} [DecidableEq k] {s : k → Type _}
    (x : ∀ i, Matrix (s i) (s i) R) : (blockDiagonal' x).IsBlockDiagonal := by
  rw [Matrix.IsBlockDiagonal, blockDiag'_blockDiagonal']

theorem isBlockDiagonal_iff {k : Type _} [DecidableEq k] {s : k → Type _}
    (x : Matrix (Σ i, s i) (Σ i, s i) R) :
    x.IsBlockDiagonal ↔ ∃ y : ∀ i, Matrix (s i) (s i) R, x = blockDiagonal' y :=
  ⟨fun h => ⟨x.blockDiag', h.symm⟩, by
    rintro ⟨y, rfl⟩ <;> exact Matrix.IsBlockDiagonal.blockDiagonal' y⟩

def stdBasisMatrixBlockDiagonal {k : Type _} [DecidableEq k] {s : k → Type _}
    [∀ i, DecidableEq (s i)] (i : k) (j l : s i) (α : R) :
    { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal } :=
  ⟨stdBasisMatrix ⟨i, j⟩ ⟨i, l⟩ α,
    by
    simp only [Matrix.IsBlockDiagonal, blockDiag'_apply, blockDiagonal'_apply,
      Matrix.blockDiagonal'_ext, dite_eq_iff', cast_hEq]
    intro a b c d
    constructor
    · intro h
      congr
      exact h
      simp only [cast_hEq]
    · intro h
      symm
      apply stdBasisMatrix.apply_of_ne
      simp only
      rintro ⟨⟨rfl, h2⟩, ⟨rfl, h4⟩⟩
      contradiction⟩

theorem includeBlock_conjTranspose {R k : Type _} [CommSemiring R] [StarRing R] [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {i : k}
    {x : Matrix (s i) (s i) R} : star x.includeBlock = xᴴ.includeBlock :=
  by
  ext
  simp only [Pi.star_apply, includeBlock_apply, star_apply, dite_apply, Pi.zero_apply, star_dite,
    star_zero, conj_transpose_apply]
  split_ifs <;> finish

theorem includeBlock_inj {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {i : k} {x y : Matrix (s i) (s i) R} :
    x.includeBlock = y.includeBlock ↔ x = y :=
  by
  simp only [includeBlock_apply]
  refine' ⟨fun h => _, fun h => by rw [h]⟩
  simp_rw [Function.funext_iff, dite_apply, Pi.zero_apply, dite_eq_iff'] at h
  ext1 j k
  specialize h i j k
  cases' h with h1 h2
  specialize h1 rfl
  simp only [eq_self_iff_true, dif_pos] at h1
  finish

theorem blockDiagonal'_includeBlock_isHermitian_iff {R k : Type _} [CommSemiring R] [StarRing R]
    [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    {i : k} (x : Matrix (s i) (s i) R) :
    (blockDiagonal' x.includeBlock).IsHermitian ↔ x.IsHermitian := by
  calc
    (blockDiagonal' x.includeBlock).IsHermitian ↔
        (blockDiagonal' x.includeBlock)ᴴ = blockDiagonal' x.includeBlock :=
      by simp only [is_hermitian]
    _ ↔ blockDiagonal' (star x.includeBlock) = blockDiagonal' x.includeBlock := by
      simp only [blockDiagonal'_conj_transpose] <;> rfl
    _ ↔ star x.includeBlock = x.includeBlock := blockDiagonal'_inj
    _ ↔ xᴴ.includeBlock = x.includeBlock := by simp only [includeBlock_conj_transpose]
    _ ↔ xᴴ = x := includeBlock_inj
    _ ↔ x.is_hermitian := by simp only [is_hermitian]

theorem matrix_eq_sum_includeBlock {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (x : ∀ i, Matrix (s i) (s i) R) :
    x = ∑ i, includeBlock (x i) :=
  (sum_includeBlock _).symm

theorem includeBlock_apply_same {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {i : k}
    (x : Matrix (s i) (s i) R) : includeBlock x i = x := by rw [includeBlock_apply] <;> finish

theorem includeBlock_apply_ne_same {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {i j : k}
    (x : Matrix (s i) (s i) R) (h : i ≠ j) : includeBlock x j = 0 := by
  simp only [includeBlock_apply, h, dif_neg, not_false_iff]

theorem includeBlock_apply_stdBasisMatrix {R k : Type _} [CommSemiring R] [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {i : k}
    (a b : s i) :
    includeBlock (stdBasisMatrix a b (1 : R)) =
      (stdBasisMatrix (⟨i, a⟩ : Σ j, s j) (⟨i, b⟩ : Σ j, s j) (1 : R)).blockDiag' :=
  by
  ext1 c
  ext1 d e
  simp_rw [includeBlock_apply, dite_apply, Pi.zero_apply, blockDiag'_apply, dite_eq_iff']
  constructor
  · rintro rfl
    simp only [eq_mp_eq_cast, cast_eq, stdBasisMatrix]
    congr <;> · simp only [eq_self_iff_true, heq_iff_eq, true_and_iff]
  · intro h
    symm
    apply stdBasisMatrix.apply_of_ne
    simp only [h, false_and_iff, not_false_iff]

theorem includeBlock_hMul_includeBlock {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {i j : k}
    (x : Matrix (s i) (s i) R) (y : Matrix (s j) (s j) R) :
    includeBlock x * includeBlock y =
      dite (j = i) (fun h => includeBlock (x * by rw [← h]; exact y)) fun h => 0 :=
  by
  ext1
  simp [includeBlock_apply, dite_hMul, hMul_dite, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
    dite_apply, Pi.zero_apply]
  split_ifs <;> finish

theorem IsBlockDiagonal.hMul {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] {x y : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal)
    (hy : y.IsBlockDiagonal) : (x ⬝ y).IsBlockDiagonal :=
  by
  simp only [Matrix.IsBlockDiagonal]
  rw [← hx.eq, ← hy.eq, ← blockDiagonal'_mul, blockDiag'_blockDiagonal']

@[instance]
def IsBlockDiagonal.hasMul {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Mul { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where mul x y := ⟨↑x ⬝ ↑y, IsBlockDiagonal.hMul x.2 y.2⟩

theorem IsBlockDiagonal.coe_hMul {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    {x y : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }} :
    ((x * y : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      x * y :=
  rfl

theorem IsBlockDiagonal.one {k : Type _} [DecidableEq k] {s : k → Type _} [∀ i, DecidableEq (s i)] :
    (1 : Matrix (Σ i, s i) (Σ i, s i) R).IsBlockDiagonal := by
  simp only [Matrix.IsBlockDiagonal, blockDiag'_one, blockDiagonal'_one]

@[instance]
def IsBlockDiagonal.hasOne {k : Type _} [DecidableEq k] {s : k → Type _} [∀ i, DecidableEq (s i)] :
    One { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where one := ⟨(1 : Matrix (Σ i, s i) (Σ i, s i) R), IsBlockDiagonal.one⟩

theorem IsBlockDiagonal.coe_one {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    ((1 : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      1 :=
  rfl

theorem IsBlockDiagonal.coe_nsmul {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (n : ℕ)
    (x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
    ((n • x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      n • ↑x :=
  by simp_rw [nsmul_eq_smul_cast R n, ← is_blockDiagonal.coe_smul]

theorem IsBlockDiagonal.npow {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (n : ℕ) {x : Matrix (Σ i, s i) (Σ i, s i) R}
    (hx : x.IsBlockDiagonal) : (x ^ n).IsBlockDiagonal :=
  by
  induction' n with d hd
  · simp only [pow_zero]; exact is_blockDiagonal.one
  · simp only [pow_succ, is_blockDiagonal.mul, hd]
    exact is_blockDiagonal.mul hx hd

@[instance]
def IsBlockDiagonal.hasNpow {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Pow { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal } ℕ
    where pow x n := ⟨(x : Matrix (Σ i, s i) (Σ i, s i) R) ^ n, IsBlockDiagonal.npow n x.2⟩

theorem IsBlockDiagonal.coe_npow {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (n : ℕ)
    (x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
    ((x ^ n : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      x ^ n :=
  rfl

@[instance]
def IsBlockDiagonal.semiring {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Semiring { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where
  add := (· + ·)
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  nsmul := (· • ·)
  nsmul_zero x := by simp only [zero_nsmul] <;> rfl
  nsmul_succ n x := by
    ext
    simp only [is_blockDiagonal.coe_nsmul, is_blockDiagonal.coe_add, Nat.succ_eq_add_one,
      add_smul, one_smul, add_comm]
  add_comm := add_comm
  mul := (· * ·)
  left_distrib x y z := by ext;
    simp only [is_blockDiagonal.coe_mul, is_blockDiagonal.coe_add, mul_add]
  right_distrib x y z := by ext;
    simp only [is_blockDiagonal.coe_mul, is_blockDiagonal.coe_add, add_mul]
  zero_mul x := by ext;
    simp only [is_blockDiagonal.coe_mul, is_blockDiagonal.coe_zero, MulZeroClass.zero_mul]
  mul_zero x := by ext;
    simp only [is_blockDiagonal.coe_mul, is_blockDiagonal.coe_zero, MulZeroClass.mul_zero]
  mul_assoc x y z := by ext; simp only [is_blockDiagonal.coe_mul, mul_assoc]
  one := 1
  one_mul x := by ext; simp only [is_blockDiagonal.coe_mul, is_blockDiagonal.coe_one, one_mul]
  mul_one x := by ext; simp only [is_blockDiagonal.coe_mul, is_blockDiagonal.coe_one, mul_one]
  natCast n := n • 1
  natCast_zero := by ext;
    simp only [is_blockDiagonal.coe_nsmul, is_blockDiagonal.coe_zero, zero_smul]
  natCast_succ a := by ext;
    simp only [is_blockDiagonal.coe_nsmul, is_blockDiagonal.coe_one, is_blockDiagonal.coe_add,
      Nat.succ_eq_add_one, add_smul, one_smul, add_comm]
  npow n x := IsBlockDiagonal.hasNpow.pow x n
  npow_zero x := by ext; simp only [is_blockDiagonal.coe_npow, is_blockDiagonal.coe_one, pow_zero]
  npow_succ n x := by ext;
    simp_rw [is_blockDiagonal.coe_npow, Nat.succ_eq_one_add, pow_add, is_blockDiagonal.coe_mul,
      pow_one, is_blockDiagonal.coe_npow]

@[instance]
def IsBlockDiagonal.algebra {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Algebra R { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where
  toFun r := r • 1
  map_one' := by ext; simp only [is_blockDiagonal.coe_nsmul, is_blockDiagonal.coe_one, one_smul]
  map_zero' := by ext;
    simp only [is_blockDiagonal.coe_nsmul, is_blockDiagonal.coe_zero, zero_smul]
  map_add' x y := by ext;
    simp only [is_blockDiagonal.coe_nsmul, is_blockDiagonal.coe_add, add_smul, add_comm]
  map_mul' x y := by
    ext; simp only [is_blockDiagonal.coe_smul, is_blockDiagonal.coe_mul, smul_mul_assoc]
    simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, mul_eq_mul, mul_smul,
      is_blockDiagonal.coe_one, Matrix.one_mul, mul_assoc]
  commutes' r x := by ext;
    simp only [is_blockDiagonal.coe_smul, is_blockDiagonal.coe_mul, smul_eq_mul, mul_smul_comm,
      smul_mul_assoc, is_blockDiagonal.coe_one, one_mul, mul_one]
  smul_def' r x := by ext;
    simp only [is_blockDiagonal.coe_smul, is_blockDiagonal.coe_mul, is_blockDiagonal.coe_one,
      smul_mul_assoc, one_mul]

theorem IsBlockDiagonal.coe_blockDiagonal'_blockDiag' {k : Type _} [DecidableEq k] {s : k → Type _}
    (x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
    blockDiagonal' (blockDiag' (x : Matrix (Σ i, s i) (Σ i, s i) R)) = x :=
  x.2

@[simps]
def isBlockDiagonalPiAlgEquiv {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal } ≃ₐ[R] ∀ i, Matrix (s i) (s i) R
    where
  toFun x := blockDiag' (x : Matrix (Σ i, s i) (Σ i, s i) R)
  invFun x := ⟨blockDiagonal' x, Matrix.IsBlockDiagonal.blockDiagonal' x⟩
  left_inv x := by ext;
    simp only [is_blockDiagonal.coe_blockDiagonal'_blockDiag', blockDiag'_blockDiagonal',
      Subtype.coe_mk]
  right_inv x := by ext;
    simp only [is_blockDiagonal.coe_blockDiagonal'_blockDiag', blockDiag'_blockDiagonal',
      Subtype.coe_mk]
  map_add' x y := by ext; simp only [is_blockDiagonal.coe_add, Pi.add_apply, blockDiag'_add]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, is_blockDiagonal.coe_smul,
      is_blockDiagonal.coe_one, blockDiag'_smul, blockDiag'_one]
  map_mul' x y := by
    rw [← blockDiagonal'_inj]
    simp_rw [Pi.mul_def, mul_eq_mul, blockDiagonal'_mul,
      is_blockDiagonal.coe_blockDiagonal'_blockDiag' x,
      is_blockDiagonal.coe_blockDiagonal'_blockDiag' y,
      is_blockDiagonal.coe_blockDiagonal'_blockDiag' (x * y), is_blockDiagonal.coe_mul,
      mul_eq_mul]

theorem IsBlockDiagonal.star {R : Type _} [CommSemiring R] [StarAddMonoid R] {k : Type _}
    [DecidableEq k] {s : k → Type _} {x : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) :
    xᴴ.IsBlockDiagonal := by
  rw [is_blockDiagonal]
  nth_rw 2 [← hx.eq]
  simp_rw [blockDiagonal'_conj_transpose, ← blockDiag'_conj_transpose]

@[instance]
def IsBlockDiagonal.hasStar {R : Type _} [CommSemiring R] [StarAddMonoid R] {k : Type _} [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    Star { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }
    where unit x := ⟨x.1ᴴ, IsBlockDiagonal.star x.2⟩

theorem IsBlockDiagonal.coe_star {R : Type _} [CommSemiring R] [StarAddMonoid R] {k : Type _}
    [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    (x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
    ((star x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
        Matrix (Σ i, s i) (Σ i, s i) R) =
      xᴴ :=
  rfl

theorem isBlockDiagonalPiAlgEquiv.map_star {R : Type _} [CommSemiring R] [StarAddMonoid R]
    {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] (x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) :
    isBlockDiagonalPiAlgEquiv (star x) = star (isBlockDiagonalPiAlgEquiv x) :=
  by
  ext1
  simp_rw [Pi.star_apply, is_blockDiagonal_pi_alg_equiv_apply, is_blockDiagonal.coe_star,
    blockDiag'_conj_transpose]
  rfl

theorem isBlockDiagonalPiAlgEquiv.symm_map_star {R : Type _} [CommSemiring R] [StarAddMonoid R]
    {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] (x : ∀ i, Matrix (s i) (s i) R) :
    isBlockDiagonalPiAlgEquiv.symm (star x) = star (isBlockDiagonalPiAlgEquiv.symm x) :=
  by
  ext1
  simp_rw [is_blockDiagonal.coe_star, is_blockDiagonal_pi_alg_equiv_symm_apply_coe,
    blockDiagonal'_conj_transpose]
  rfl

@[simps]
def Equiv.sigmaProdDistrib' {ι : Type _} (β : Type _) (α : ι → Type _) :
    (β × Σ i : ι, α i) ≃ Σ i : ι, β × α i :=
  by
  let this.1 : (Σ i : ι, β × α i) ≃ Σ i : ι, α i × β :=
    by
    apply Equiv.sigmaCongrRight
    intro i
    exact Equiv.prodComm _ _
  exact ((Equiv.prodComm _ _).trans (Equiv.sigmaProdDistrib _ _)).trans this.symm

@[simps]
def sigmaProdSigma {α β : Type _} {ζ : α → Type _} {℘ : β → Type _} :
    ((Σ i, ζ i) × Σ i, ℘ i) ≃ Σ i j, ζ i × ℘ j
    where
  toFun x := by
    refine' ⟨(Equiv.sigmaProdDistrib _ _ x).1, (equiv.sigma_prod_distrib' _ _ x).1, (x.1.2, x.2.2)⟩
  invFun x := (⟨x.1, x.2.2.1⟩, ⟨x.2.1, x.2.2.2⟩)
  left_inv x :=
    by
    ext <;>
      simp only [equiv.sigma_prod_distrib'_apply_fst, equiv.sigma_prod_distrib'_apply_snd,
        Equiv.sigmaProdDistrib, Equiv.coe_fn_mk]
    rfl
  right_inv x :=
    by
    ext <;>
      simp only [equiv.sigma_prod_distrib'_apply_fst, equiv.sigma_prod_distrib'_apply_snd,
        Equiv.coe_fn_mk, Equiv.sigmaProdDistrib, Equiv.coe_fn_mk]
    simp only [Prod.mk.eta, heq_iff_eq]
    ext <;> simp only [equiv.sigma_prod_distrib'_apply_fst, Equiv.sigmaProdDistrib, Equiv.coe_fn_mk]
    rfl

theorem IsBlockDiagonal.apply_of_ne {R : Type _} [CommSemiring R] {k : Type _} [DecidableEq k]
    {s : k → Type _} {x : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) (i j : Σ i, s i)
    (h : i.1 ≠ j.1) : x i j = 0 := by
  rw [← hx.eq]
  simp_rw [blockDiagonal'_apply, blockDiag'_apply, dif_neg h]

theorem IsBlockDiagonal.apply_of_ne_coe {R : Type _} [CommSemiring R] {k : Type _} [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    (x : { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal }) (i j : Σ i, s i)
    (h : i.fst ≠ j.fst) : (x : Matrix (Σ i, s i) (Σ i, s i) R) i j = 0 :=
  IsBlockDiagonal.apply_of_ne x.2 i j h

open scoped Kronecker

theorem IsBlockDiagonal.kronecker_hMul {R : Type _} [CommSemiring R] {k : Type _} [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    {x y : Matrix (Σ i, s i) (Σ i, s i) R} (hx : x.IsBlockDiagonal) :
    IsBlockDiagonal fun i j => (x ⊗ₖ y) (sigmaProdSigma.symm i) (sigmaProdSigma.symm j) :=
  by
  rw [Matrix.IsBlockDiagonal, blockDiagonal'_ext]
  intro a b c d
  simp only [blockDiagonal'_apply', blockDiag'_apply, kronecker_map_apply,
    sigma_prod_sigma_symm_apply, dite_hMul, MulZeroClass.zero_mul, hMul_dite, MulZeroClass.mul_zero]
  split_ifs
  · dsimp [h]
    congr <;> simp [h]
  · dsimp only
    rw [hx.apply_of_ne, MulZeroClass.zero_mul]
    exact h

@[simps]
def directSumLinearMapAlgEquivIsBlockDiagonalLinearMap {R : Type _} [CommSemiring R] {k : Type _}
    [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] :
    ((∀ i, Matrix (s i) (s i) R) →ₗ[R] ∀ i, Matrix (s i) (s i) R) ≃ₐ[R]
      { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal } →ₗ[R]
        { x : Matrix (Σ i, s i) (Σ i, s i) R // x.IsBlockDiagonal } :=
  isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv.innerConj

end Matrix

variable {R k : Type _} [CommSemiring R] [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "ℍ₂" => ∀ i, Matrix (s i) (s i) R

local notation "ℍ_ " i => Matrix (s i) (s i) R

open Matrix

theorem TensorProduct.assoc_includeBlock {k : Type _} [DecidableEq k] {s : k → Type _} {i j : k} :
    (↑(TensorProduct.assoc R (∀ a, Matrix (s a) (s a) R) (∀ a, Matrix (s a) (s a) R)
              (∀ a, Matrix (s a) (s a) R)).symm ∘ₗ
        (includeBlock : Matrix (s i) (s i) R →ₗ[R] ∀ a, Matrix (s a) (s a) R) ⊗ₘ
          (includeBlock : Matrix (s j) (s j) R →ₗ[R] ∀ a, Matrix (s a) (s a) R) ⊗ₘ
            (includeBlock : Matrix (s j) (s j) R →ₗ[R] ∀ a, Matrix (s a) (s a) R)) =
      (((includeBlock : Matrix (s i) (s i) R →ₗ[R] ∀ a, Matrix (s a) (s a) R) ⊗ₘ
            (includeBlock : Matrix (s j) (s j) R →ₗ[R] ∀ a, Matrix (s a) (s a) R)) ⊗ₘ
          (includeBlock : Matrix (s j) (s j) R →ₗ[R] ∀ a, Matrix (s a) (s a) R)) ∘ₗ
        ↑(TensorProduct.assoc R (Matrix (s i) (s i) R) (Matrix (s j) (s j) R)
              (Matrix (s j) (s j) R)).symm :=
  by
  apply TensorProduct.ext_threefold'
  intro x y z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
    TensorProduct.map_tmul]
