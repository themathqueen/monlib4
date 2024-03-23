/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.MyMatrix.PosDefRpow
import Monlib.LinearAlgebra.PiStarOrderedRing
import Monlib.LinearAlgebra.MyIps.Functional
import Monlib.LinearAlgebra.MyIps.QuantumSet
import Momnlib.LinearAlgebra.PiDirectSum
import Monlib.LinearAlgebra.KroneckerToTensor

#align_import linear_algebra.my_matrix.star_ordered_ring

/-!
# Matrix algebras are star ordered rings

This file contains the instance of `star_ordered_ring` for `matrix n n ℂ`.

## Main definitions

* `matrix.partial_order`: The partial order on `matrix n n ℂ` induced by the positive semidefinite
  matrices.
* `matrix.pos_semidef.add_submonoid`: The additive submonoid of positive semidefinite matrices.
* `matrix.star_ordered_ring`: The instance of `star_ordered_ring` for `matrix n n ℂ`.

You need to `open_locale matrix_order` to use these instances.

-/


#print Matrix.PosSemidef.zero /-
theorem Matrix.PosSemidef.zero {n : Type _} [Fintype n] : (0 : Matrix n n ℂ).PosSemidef := by
  simp_rw [Matrix.PosSemidef, Matrix.isHermitian_zero, true_and_iff, Matrix.zero_mulVec,
    Matrix.dotProduct_zero, map_zero, le_refl, imp_true_iff]
-/

theorem Matrix.PosSemidef.add {n : Type _} [Fintype n] {x y : Matrix n n ℂ} (hx : x.PosSemidef)
    (hy : y.PosSemidef) : (x + y).PosSemidef :=
  by
  simp_rw [Matrix.PosSemidef, Matrix.IsHermitian.add hx.1 hy.1, true_and_iff, Matrix.add_mulVec,
    Matrix.dotProduct_add, map_add]
  exact fun a => add_nonneg (hx.2 a) (hy.2 a)

open scoped Matrix

theorem Matrix.eq_zero_iff {n : Type _} [Fintype n] [DecidableEq n] {x : Matrix n n ℂ} :
    x = 0 ↔ ∀ a : n → ℂ, star a ⬝ᵥ x.mulVec a = 0 := by
  calc
    x = 0 ↔ x.to_euclidean_lin = 0 := by simp only [LinearEquiv.map_eq_zero_iff]
    _ ↔ ∀ a : EuclideanSpace ℂ n, ⟪a, x.to_euclidean_lin a⟫_ℂ = 0 := by
      simp_rw [← inner_map_self_eq_zero, inner_eq_zero_symm]
    _ ↔ ∀ a : EuclideanSpace ℂ n, (star (a : n → ℂ) : n → ℂ) ⬝ᵥ x.mul_vec a = 0 := by rfl
    _ ↔ ∀ a : n → ℂ, star a ⬝ᵥ x.mul_vec a = 0 := by rfl

theorem Matrix.toEuclideanLin_apply {n : Type _} [Fintype n] [DecidableEq n] (x : Matrix n n ℂ)
    (a : n → ℂ) : x.toEuclideanLin a = x.mulVec a :=
  rfl

open scoped ComplexOrder

def Matrix.partialOrder {n : Type _} [Fintype n] [DecidableEq n] : PartialOrder (Matrix n n ℂ)
    where
  le x y := (y - x).PosSemidef
  le_refl x := by simp only [sub_self, Matrix.PosSemidef.zero]
  le_trans x y z hx hy := by
    have := Matrix.PosSemidef.add hx hy
    simp only [sub_add_sub_cancel'] at this
    exact this
  le_antisymm x y hx hy := by
    rw [← sub_eq_zero, Matrix.eq_zero_iff]
    intro a
    have := hx.2 a
    rw [← neg_sub, Matrix.neg_mulVec, Matrix.dotProduct_neg, map_neg, ← Complex.zero_le_real,
      Complex.ofReal_neg, le_neg, neg_zero] at this
    ext
    exact le_antisymm this (complex.zero_le_real.mpr (hy.2 a))
    simp_rw [Complex.zero_im, ← Complex.conj_eq_iff_im, ← EuclideanSpace.inner_eq, ←
      Matrix.toEuclideanLin_apply, inner_conj_symm, ← LinearMap.adjoint_inner_left, ←
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hy.1.Eq]

scoped[-- lt := λ x y, (y - x).pos_def,
-- lt_iff_le_not_le := λ x y, by {  } }
MatrixOrder] attribute [instance] Matrix.partialOrder

theorem Matrix.le_iff {n : Type _} [Fintype n] [DecidableEq n] {x y : Matrix n n ℂ} :
    x ≤ y ↔ (y - x).PosSemidef :=
  Iff.rfl

-- def matrix.pos_semidef.add_submonoid (n : Type*) [fintype n] [decidable_eq n] :
--   add_submonoid (matrix n n ℂ) :=
-- { carrier := {x : matrix n n ℂ | x.pos_semidef},
--   zero_mem' := matrix.pos_semidef.zero,
--   add_mem' := λ x y hx hy, matrix.pos_semidef.add hx hy }
-- lemma matrix.pos_semidef.mem_add_submonoid {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
--   x ∈ (matrix.pos_semidef.add_submonoid n : add_submonoid (matrix n n ℂ)) ↔ x.pos_semidef :=
-- iff.rfl
-- lemma matrix.pos_semidef.star_mul_self_mem_add_submonoid {n : Type*} [fintype n] [decidable_eq n]
--   (x : matrix n n ℂ) :
--   xᴴ ⬝ x ∈ matrix.pos_semidef.add_submonoid n :=
-- begin
--   simp_rw [matrix.pos_semidef.mem_add_submonoid, matrix.pos_semidef.star_mul_self],
-- end
noncomputable def Matrix.starOrderedRing {n : Type _} [Fintype n] [DecidableEq n] :
    StarOrderedRing (Matrix n n ℂ) :=
  by
  apply StarOrderedRing.ofLEIff
  · intro a b hab c
    simp_rw [Matrix.le_iff, add_sub_add_left_eq_sub]
    exact hab
  · intro x y
    simp_rw [Matrix.le_iff, Matrix.posSemidef_iff, sub_eq_iff_eq_add', Matrix.star_eq_conjTranspose,
      Matrix.hMul_eq_hMul]

scoped[MatrixOrder] attribute [instance] Matrix.starOrderedRing

open scoped MatrixOrder

theorem Matrix.Pi.le_iff_sub_nonneg {ι : Type _} [Fintype ι] [DecidableEq ι] {n : ι → Type _}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] (x y : ∀ i, Matrix (n i) (n i) ℂ) :
    x ≤ y ↔ ∃ z : ∀ i, Matrix (n i) (n i) ℂ, y = x + star z * z :=
  by
  simp_rw [@Function.funext_iff _ _ _ (_ + star _ * _), Pi.add_apply, Pi.mul_apply, Pi.star_apply,
    Pi.le_def, Matrix.le_iff, Matrix.posSemidef_iff, sub_eq_iff_eq_add',
    Matrix.star_eq_conjTranspose, Matrix.hMul_eq_hMul]
  exact
    ⟨fun hx => ⟨fun i => (hx i).some, fun i => (hx i).choose_spec⟩, fun ⟨y, hy⟩ i => ⟨y i, hy i⟩⟩

noncomputable def Matrix.Pi.starOrderedRing {ι : Type _} [Fintype ι] [DecidableEq ι]
    {n : ι → Type _} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] :
    StarOrderedRing (∀ i, Matrix (n i) (n i) ℂ) :=
  by
  refine'
    StarOrderedRing.ofLEIff
      (fun a b hab c i => by
        simp_rw [Pi.add_apply]
        exact add_le_add_left (hab _) _)
      _
  intro a b
  simp_rw [Pi.le_def, Matrix.le_iff]
  rw [← Matrix.Pi.le_iff_sub_nonneg]
  rfl

scoped[MatrixOrder] attribute [instance] Matrix.Pi.starOrderedRing

def Matrix.NegSemidef {n : Type _} [Fintype n] [DecidableEq n] (x : Matrix n n ℂ) : Prop :=
  x.IsHermitian ∧ ∀ a : n → ℂ, IsROrC.re (Matrix.dotProduct (Star.star a) (x.mulVec a)) ≤ 0

theorem Matrix.IsHermitian.neg_iff {n : Type _} [Fintype n] [DecidableEq n] (x : Matrix n n ℂ) :
    (-x).IsHermitian ↔ x.IsHermitian := by
  constructor
  · intro h
    rw [← neg_neg x]
    exact Matrix.IsHermitian.neg h
  · exact Matrix.IsHermitian.neg

theorem Matrix.negSemidef_iff_neg_posSemidef {n : Type _} [Fintype n] [DecidableEq n]
    (x : Matrix n n ℂ) : x.NegSemidef ↔ (-x).PosSemidef := by
  simp_rw [Matrix.NegSemidef, Matrix.PosSemidef, Matrix.IsHermitian.neg_iff, Matrix.neg_mulVec,
    Matrix.dotProduct_neg, map_neg, @le_neg _ _ _ _ _ (0 : ℝ), neg_zero]

theorem Matrix.negSemidef_iff_nonpos {n : Type _} [Fintype n] [DecidableEq n] (x : Matrix n n ℂ) :
    x.NegSemidef ↔ x ≤ 0 := by rw [Matrix.negSemidef_iff_neg_posSemidef, Matrix.le_iff, zero_sub]

open scoped ComplexOrder

theorem Matrix.posSemidef_and_negSemidef_iff_eq_zero {n : Type _} [Fintype n] [DecidableEq n]
    {x : Matrix n n ℂ} : x.PosSemidef ∧ x.NegSemidef ↔ x = 0 := by
  simp_rw [Matrix.negSemidef_iff_neg_posSemidef, Matrix.eq_zero_iff, PosSemidef.complex,
    Matrix.neg_mulVec, Matrix.dotProduct_neg, neg_nonneg, le_antisymm_iff, forall_and, and_comm']

-- lemma matrix.pos_semidef_and_not_neg_semidef_iff_pos_def
--   {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
--   (x.pos_semidef ∧ ¬ x.neg_semidef) ↔ x.pos_def :=
-- begin
--   nth_rewrite 0 ← sub_zero x,
--   rw [← matrix.le_iff, matrix.neg_semidef_iff_nonpos, ← lt_iff_le_not_le,
--     lt_iff_le_and_ne, ne.def, eq_comm],
--   split,
--   { rintro ⟨⟨hx1, hx2⟩, h⟩,
--     rw ← sub_zero x,
--     refine ⟨hx1, _⟩,
--     intros a ha,
--     specialize hx2 a,
--     apply lt_of_le_not_le hx2,
--     intro hi,
--     simp_rw [sub_zero] at hi hx2,
--   }
-- end
-- def matrix.pos_def.has_pow {n : Type*} [fintype n] [decidable_eq n] :
--   has_pow ({x : matrix n n ℂ // 0 < x}) ℝ :=
-- { pow := λ x r, @matrix.pos_def.rpow x _ r, }
-- open_locale functional
-- noncomputable def module.dual.is_faithful_pos_map.normed_add_comm_group_of_ring
--   {n : Type*} [fintype n] [decidable_eq n] (f : module.dual ℂ (matrix n n ℂ))
--   [hf : fact f.is_faithful_pos_map] :
--   normed_add_comm_group_of_ring (matrix n n ℂ) :=
-- { to_has_norm := normed_add_comm_group.to_has_norm,
--   ..matrix.ring }
-- local attribute [instance] algebra.of_is_scalar_tower_smul_comm_class
-- def matrix_is_quantum_set {n : Type*} [fintype n] [decidable_eq n]
--   {f : module.dual ℂ (matrix n n ℂ)} [hf : fact f.is_faithful_pos_map] :
--   quantum_set (matrix n n ℂ) :=
-- begin
--   refine { to_normed_add_comm_group_of_ring := module.dual.is_faithful_pos_map.normed_add_comm_group_of_ring f,
--   to_inner_product_space := @module.dual.is_faithful_pos_map.inner_product_space _ _ _ _ hf,
--   to_partial_order := @matrix.partial_order n _ _,
--   to_star_ordered_ring := @matrix.star_ordered_ring n _ _,
--   to_has_smul_comm_class := by { apply_instance },
--   to_is_scalar_tower := by { apply_instance },
--   to_finite_dimensional := by { apply_instance },
--   to_has_inv := by { apply_instance },
--   φ := f,
--   hφ := hf.elim,
--   inner_eq := λ x y, rfl,
--   functional_adjoint_eq := module.dual.is_faithful_pos_map.adjoint_eq,
--   ..},
-- end
