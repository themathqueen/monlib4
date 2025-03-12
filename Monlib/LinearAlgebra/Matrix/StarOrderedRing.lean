/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.PiStarOrderedRing
-- import Monlib.LinearAlgebra.Ips.Functional
-- import Monlib.LinearAlgebra.MyIps.QuantumSet
import Monlib.LinearAlgebra.PiDirectSum
import Monlib.LinearAlgebra.InnerAut
import Monlib.LinearAlgebra.Matrix.PosEqLinearMapIsPositive
import Monlib.LinearAlgebra.KroneckerToTensor
import Monlib.Preq.Complex
import Monlib.LinearAlgebra.Matrix.PiMat
import Mathlib.Analysis.InnerProductSpace.Basic

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

namespace Matrix

open scoped ComplexOrder

-- theorem PosSemidef.add {n : Type _} [Fintype n] {x y : Matrix n n ℂ} (hx : PosSemidef x)
--     (hy : PosSemidef y) : PosSemidef (x + y) :=
--   by
--   simp_rw [PosSemidef, Matrix.IsHermitian.add hx.1 hy.1, true_and_iff, Matrix.add_mulVec,
--     Matrix.dotProduct_add]
--   exact fun a => add_nonneg (hx.2 a) (hy.2 a)

open scoped Matrix

theorem eq_zero_iff {n : Type _} [Fintype n] [DecidableEq n] {x : Matrix n n ℂ} :
    x = 0 ↔ ∀ a : n → ℂ, star a ⬝ᵥ x.mulVec a = 0 := by
  calc
    x = 0 ↔ toEuclideanLin x = 0 := by simp only [LinearEquiv.map_eq_zero_iff]
    _ ↔ ∀ a : EuclideanSpace ℂ n, (inner a (toEuclideanLin x a) :
    ℂ) = 0 := by
      simp_rw [← inner_map_self_eq_zero, inner_eq_zero_symm]
    _ ↔ ∀ a : EuclideanSpace ℂ n, (star (a : n → ℂ) : n → ℂ) ⬝ᵥ x *ᵥ a = 0 := by rfl
    _ ↔ ∀ a : n → ℂ, star a ⬝ᵥ x *ᵥ a = 0 := by rfl

@[reducible]
protected def LE {n : Type _} [Fintype n] [DecidableEq n] :
  LE (Matrix n n ℂ) :=
⟨fun x y => (y - x).PosSemidef⟩

def NegSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] (x : Matrix n n 𝕜) : Prop :=
  x.IsHermitian ∧ ∀ a : n → 𝕜, dotProduct (Star.star a) (x *ᵥ a) ≤ 0

def NegDef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] (x : Matrix n n 𝕜) : Prop :=
x.IsHermitian ∧ ∀ a : n → 𝕜, a ≠ 0 → (star a) ⬝ᵥ (x *ᵥ a) < 0

theorem IsHermitian.neg_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] (x : Matrix n n 𝕜) :
    (-x).IsHermitian ↔ x.IsHermitian := by
  constructor
  · intro h
    rw [← neg_neg x]
    exact Matrix.IsHermitian.neg h
  · exact Matrix.IsHermitian.neg

theorem negSemidef_iff_neg_posSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    (x : Matrix n n 𝕜) : x.NegSemidef ↔ (-x).PosSemidef := by
  simp_rw [Matrix.NegSemidef, Matrix.PosSemidef, Matrix.IsHermitian.neg_iff, Matrix.neg_mulVec,
    dotProduct_neg, le_neg, neg_zero]
theorem negDef_iff_neg_posDef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] (x : Matrix n n 𝕜) :
    x.NegDef ↔ (-x).PosDef := by
  simp_rw [Matrix.NegDef, Matrix.PosDef, Matrix.IsHermitian.neg_iff, Matrix.neg_mulVec,
    dotProduct_neg, lt_neg, neg_zero]

open scoped ComplexOrder

theorem NegDef.re_dotProduct_neg {n 𝕜 : Type _}
  [RCLike 𝕜] [Fintype n]
  {M : Matrix n n 𝕜} (hM : M.NegDef) {x : n → 𝕜} (hx : x ≠ 0) :
    RCLike.re (dotProduct (star x) (M *ᵥ x)) < 0 :=
  RCLike.neg_iff.mp (hM.2 _ hx) |>.1

theorem NegSemidef.nonpos_eigenvalues {𝕜 n : Type _}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
  (hx : x.NegSemidef) (i : n) :
  hx.1.eigenvalues i ≤ 0 := by
    rw [hx.1.eigenvalues_eq']
    exact (RCLike.nonpos_def.mp (hx.2 _)).1

theorem NegDef.neg_eigenvalues {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.NegDef) (i : n) : hx.1.eigenvalues i < 0 := by
  rw [hx.1.eigenvalues_eq']
  exact hx.re_dotProduct_neg <| hx.1.eigenvectorBasis.orthonormal.ne_zero i

theorem IsHermitian.eigenvalues_eq_zero_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {x : Matrix n n 𝕜} (hx : x.IsHermitian) :
  RCLike.ofReal ∘ hx.eigenvalues = (0 : n → 𝕜) ↔ x = 0 :=
  by
  constructor
  · intro h
    rw [Matrix.IsHermitian.spectral_theorem hx, h,
      Pi.zero_def, diagonal_zero, mul_zero, zero_mul]
  · rintro rfl
    ext
    simp only [Function.comp_apply, hx.eigenvalues_eq, zero_mulVec, dotProduct_zero, map_zero,
      Pi.zero_apply, RCLike.ofReal_zero]

theorem posSemidef_and_negSemidef_iff_eq_zero {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {x : Matrix n n 𝕜} : x.PosSemidef ∧ x.NegSemidef ↔ x = 0 := by
  constructor
  . rintro ⟨h1, h2⟩
    rw [← IsHermitian.eigenvalues_eq_zero_iff h1.1]
    ext i
    simp_rw [Pi.zero_apply, Function.comp_apply, RCLike.ofReal_eq_zero]
    have := h1.eigenvalues_nonneg i
    have := h2.nonpos_eigenvalues i
    linarith
  . rintro rfl
    simp only [negSemidef_iff_neg_posSemidef, neg_zero, and_self, PosSemidef.zero]

theorem not_posDef_and_negDef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Nonempty n] (x : Matrix n n 𝕜) :
    ¬ (x.PosDef ∧ x.NegDef) := by
  let i : n := Nonempty.some (by infer_instance)
  rintro ⟨h1, h2⟩
  have hh1 := PosDef.pos_eigenvalues h1 i
  have hh2 := NegDef.neg_eigenvalues h2 i
  linarith

open scoped BigOperators
theorem diagonal_posSemidef_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosSemidef ↔ 0 ≤ x := by
  simp_rw [PosSemidef, IsHermitian, diagonal_conjTranspose,
    dotProduct, mulVec, dotProduct, diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.star_apply, mul_rotate',
    mul_comm _ (star _), RCLike.star_def, RCLike.conj_mul,
    diagonal_eq_diagonal_iff, Pi.star_apply]
  constructor
  . rintro ⟨_, h2⟩ i
    specialize h2 (λ j => if j = i then 1 else 0)
    simp only [apply_ite, norm_zero, RCLike.ofReal_zero, ite_pow, zero_pow two_ne_zero,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, norm_one,
      RCLike.ofReal_one, one_pow, mul_one] at h2
    exact h2
  . intro h
    simp_rw [Pi.le_def, Pi.zero_apply, @RCLike.nonneg_def' 𝕜,
      ← RCLike.conj_eq_iff_re] at h
    refine ⟨λ i => (h i).1, λ i => ?_⟩
    apply Finset.sum_nonneg
    intro i _
    simp_rw [RCLike.conj_eq_iff_re] at h
    rw [← (h i).1, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.zero_le_real]
    apply mul_nonneg (h i).2 (sq_nonneg _)

theorem diagonal_negSemidef_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).NegSemidef ↔ x ≤ 0 := by
  simp_rw [negSemidef_iff_neg_posSemidef, diagonal_neg, diagonal_posSemidef_iff,
    Pi.le_def, Pi.zero_apply, Left.nonneg_neg_iff]

theorem diagonal_posDef_iff {𝕜 n : Type _}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosDef ↔ ∀ i, 0 < x i := by
  simp_rw [PosDef, IsHermitian, diagonal_conjTranspose,
    dotProduct, mulVec, dotProduct, diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.star_apply, mul_rotate',
    mul_comm _ (star _), RCLike.star_def, RCLike.conj_mul,
    diagonal_eq_diagonal_iff, Pi.star_apply]
  constructor
  . rintro ⟨_, h2⟩ i
    specialize h2 (λ j => if j = i then 1 else 0)
    simp only [apply_ite, norm_zero, RCLike.ofReal_zero, ite_pow, zero_pow two_ne_zero,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, norm_one,
      RCLike.ofReal_one, one_pow, mul_one] at h2
    apply h2
    simp_rw [ne_eq, funext_iff, not_forall]
    use i
    simp only [↓reduceIte, Pi.zero_apply, one_ne_zero, not_false_eq_true]
  . intro h
    simp_rw [@RCLike.pos_def 𝕜, ← RCLike.conj_eq_iff_im] at h
    refine ⟨λ i => (h i).2, λ x hx => ?_⟩
    apply Finset.sum_pos'
    intro i _
    simp_rw [RCLike.conj_eq_iff_re] at h
    rw [← (h i).2, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.zero_le_real]
    apply mul_nonneg (le_of_lt (h i).1) (sq_nonneg _)
    simp_rw [ne_eq, funext_iff, not_forall, Pi.zero_apply] at hx
    obtain ⟨i, hi⟩ := hx
    use i
    simp only [Finset.mem_univ, true_and, ← RCLike.ofReal_pow]
    simp_rw [RCLike.conj_eq_iff_im, ← RCLike.pos_def] at h
    apply mul_pos (h i)
    simp_rw [RCLike.zero_lt_real]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi)

theorem diagonal_negDef_iff {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).NegDef ↔ ∀ i, x i < 0 := by
  simp_rw [negDef_iff_neg_posDef, diagonal_neg, diagonal_posDef_iff, Left.neg_pos_iff]

theorem posSemidef_iff_of_isHermitian {𝕜 n : Type _}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    x.PosSemidef ↔ 0 ≤ hx.eigenvalues := by
  constructor
  . intro h i
    simp only [Pi.zero_apply, LE.le, sub_zero] at h ⊢
    exact IsHermitian.nonneg_eigenvalues_of_posSemidef h i
  . intro h
    rw [IsHermitian.spectral_theorem'' hx,
      innerAut_posSemidef_iff, diagonal_posSemidef_iff]
    intro i
    rw [Pi.zero_apply, Function.comp_apply, RCLike.zero_le_real]
    exact h i

theorem posSemidef_iff_isHermitian_and_nonneg_spectrum {𝕜 n : Type _}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
  x.PosSemidef ↔ (x.IsHermitian ∧ spectrum 𝕜 (Matrix.toLin' x) ⊆ {x : 𝕜 | 0 ≤ x}) :=
by
  constructor
  . intro h
    refine ⟨h.1, ?_⟩
    simp_rw [h.1.spectrum]
    simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff,
      RCLike.zero_le_real]
    intro i
    exact h.eigenvalues_nonneg i
  . rintro ⟨h1, h2⟩
    rw [posSemidef_iff_of_isHermitian h1]
    rw [h1.spectrum] at h2
    simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff,
      RCLike.zero_le_real] at h2
    exact h2

theorem posDef_iff_of_isHermitian {𝕜 n : Type _}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
  (hx : x.IsHermitian) :
    x.PosDef ↔ ∀ i, 0 < hx.eigenvalues i := by
  constructor
  . intro h i
    simp only [Pi.zero_apply, LE.le, sub_zero] at h ⊢
    exact PosDef.pos_eigenvalues h i
  . intro h
    rw [IsHermitian.spectral_theorem'' hx,
      innerAut_posDef_iff, diagonal_posDef_iff]
    intro i
    rw [Function.comp_apply, RCLike.zero_lt_real]
    exact h i

theorem posDef_iff_isHermitian_and_pos_spectrum {𝕜 n : Type _}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜} :
  x.PosDef ↔ (x.IsHermitian ∧ spectrum 𝕜 (Matrix.toLin' x) ⊆ {x : 𝕜 | 0 < x}) :=
by
  constructor
  . intro h
    refine ⟨h.1, ?_⟩
    simp_rw [h.1.spectrum]
    simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff,
      RCLike.zero_lt_real]
    intro i
    exact h.eigenvalues_pos i
  . rintro ⟨h1, h2⟩
    rw [posDef_iff_of_isHermitian h1]
    rw [h1.spectrum] at h2
    simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff,
      RCLike.zero_lt_real] at h2
    exact h2

theorem posSemidef_iff_commute {𝕜 n : Type _} [RCLike 𝕜]
  [Fintype n] [DecidableEq n] {x y : Matrix n n 𝕜}
  (hx : x.PosSemidef) (hy : y.PosSemidef) :
  Commute x y ↔ (x * y).PosSemidef :=
by
  refine ⟨λ h => ?_, λ h => (Matrix.commute_iff hx.1 hy.1).mpr h.1⟩
  rw [posSemidef_iff_isHermitian_and_nonneg_spectrum]
  refine ⟨(Matrix.commute_iff hx.1 hy.1).mp h, ?_⟩
  obtain ⟨a, rfl⟩ := (posSemidef_iff _).mp hx
  obtain ⟨b, rfl⟩ := (posSemidef_iff _).mp hy
  calc spectrum 𝕜 (toLin' (aᴴ * a * (bᴴ * b)))
      = spectrum 𝕜 ((toLin' a) * toLin' (bᴴ * b) * toLin' aᴴ) :=
      by
        rw [LinearMap.mul_eq_comp, spectrum.comm]
        simp_rw [LinearMap.mul_eq_comp, ← toLin'_mul, mul_assoc]
    _ = spectrum 𝕜 (toLin' ((b * aᴴ)ᴴ * (b * aᴴ))) :=
      by simp_rw [conjTranspose_mul, conjTranspose_conjTranspose, LinearMap.mul_eq_comp,
        ← toLin'_mul, mul_assoc]
  exact (posSemidef_iff_isHermitian_and_nonneg_spectrum.mp (posSemidef_conjTranspose_mul_self _)).2

theorem innerAut_negSemidef_iff {𝕜 n : Type _}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] (U : unitaryGroup n 𝕜) {a : Matrix n n 𝕜} :
  (innerAut U a).NegSemidef ↔ a.NegSemidef :=
by
  simp_rw [negSemidef_iff_neg_posSemidef, ← map_neg, innerAut_posSemidef_iff]

/-- $f_U(x)$ is negative definite if and only if $x$ is negative definite -/
theorem innerAut_negDef_iff {𝕜 n : Type _} [RCLike 𝕜]
  [Fintype n] [DecidableEq n]
  (U : unitaryGroup n 𝕜) {x : Matrix n n 𝕜} :
  (innerAut U x).NegDef ↔ x.NegDef :=
  by
  simp_rw [negDef_iff_neg_posDef, ← map_neg, innerAut_posDef_iff]

theorem negSemidef_iff_of_isHermitian {𝕜 n : Type _}
  [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    x.NegSemidef ↔ hx.eigenvalues ≤ 0 := by
  nth_rw 1 [IsHermitian.spectral_theorem'' hx, innerAut_negSemidef_iff, diagonal_negSemidef_iff]
  simp_rw [Pi.le_def, Function.comp_apply, Pi.zero_apply, ← @RCLike.ofReal_zero 𝕜,
    RCLike.real_le_real]

theorem negDef_iff_of_isHermitian {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    x.NegDef ↔ ∀ i, hx.eigenvalues i < 0 := by
  nth_rw 1 [IsHermitian.spectral_theorem'' hx, innerAut_negDef_iff, diagonal_negDef_iff]
  simp_rw [Function.comp_apply, RCLike.neg_ofReal]

theorem posDef_of_posSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.PosSemidef) :
    x.PosDef ↔ ∀ i, hx.1.eigenvalues i ≠ 0 := by
  rw [posDef_iff_of_isHermitian hx.1]
  simp_rw [lt_iff_le_and_ne, ne_eq, IsHermitian.nonneg_eigenvalues_of_posSemidef hx, true_and, eq_comm]

theorem negDef_of_negSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.NegSemidef) :
    x.NegDef ↔ ∀ i, hx.1.eigenvalues i ≠ 0 := by
  rw [negDef_iff_of_isHermitian hx.1]
  simp_rw [lt_iff_le_and_ne, ne_eq, NegSemidef.nonpos_eigenvalues hx, true_and]

@[reducible]
def partialOrder {n : Type _} [Fintype n] [DecidableEq n] : PartialOrder (Matrix n n ℂ)
    where
  toLE := Matrix.LE
  le_refl x := by simp only [LE.le, sub_self, Matrix.PosSemidef.zero]
  le_trans x y z hx hy := by
    have := Matrix.PosSemidef.add hx hy
    simp only [sub_add_sub_cancel'] at this
    exact this
  le_antisymm x y hx hy := by
    rw [← sub_eq_zero, Matrix.eq_zero_iff]
    intro a
    have := hx.2 a
    rw [← neg_sub, Matrix.neg_mulVec, dotProduct_neg,
      le_neg, neg_zero] at this
    exact le_antisymm this (hy.2 a)

scoped[-- lt := λ x y, (y - x).pos_def,
-- lt_iff_le_not_le := λ x y, by {  } }
MatrixOrder] attribute [instance] Matrix.partialOrder

open scoped MatrixOrder

theorem le_iff {n : Type _} [Fintype n] [DecidableEq n] {x y : Matrix n n ℂ} :
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
@[reducible]
noncomputable def starOrderedRing {n : Type _} [Fintype n] [DecidableEq n] :
    StarOrderedRing (Matrix n n ℂ) :=
StarOrderedRing.of_le_iff (fun a b => by
  constructor
  · intro hab
    simp_rw [Matrix.le_iff] at hab
    simp_rw [← sub_eq_iff_eq_add']
    exact (posSemidef_iff _).mp hab
  · rintro ⟨s, rfl⟩
    simp_rw [Matrix.le_iff, Matrix.posSemidef_iff, sub_eq_iff_eq_add', Matrix.star_eq_conjTranspose]
    exact ⟨_, rfl⟩)

scoped[MatrixOrder] attribute [instance] Matrix.starOrderedRing

open scoped MatrixOrder

theorem Pi.le_iff_sub_nonneg {ι : Type _} [Fintype ι] [DecidableEq ι] {n : ι → Type _}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] (x y : PiMat ℂ ι n) :
    x ≤ y ↔ ∃ z : PiMat ℂ ι n, y = x + star z * z :=
  by
  simp_rw [funext_iff, Pi.add_apply, Pi.mul_apply, Pi.star_apply,
    Pi.le_def, Matrix.le_iff, Matrix.posSemidef_iff, sub_eq_iff_eq_add',
    Matrix.star_eq_conjTranspose]
  exact
    ⟨fun hx => ⟨fun i => (hx i).choose, fun i => (hx i).choose_spec⟩, fun ⟨y, hy⟩ i => ⟨y i, hy i⟩⟩

@[reducible]
noncomputable def PiStarOrderedRing {ι : Type _} [Fintype ι] [DecidableEq ι]
    {n : ι → Type _} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] :
    StarOrderedRing (PiMat ℂ ι n) :=
StarOrderedRing.of_le_iff
  (fun a b => by simp_rw [Pi.le_iff_sub_nonneg])

scoped[MatrixOrder] attribute [instance] Matrix.PiStarOrderedRing

theorem negSemidef_iff_nonpos {n : Type _} [Fintype n] [DecidableEq n] (x : Matrix n n ℂ) :
    x.NegSemidef ↔ x ≤ 0 := by rw [Matrix.negSemidef_iff_neg_posSemidef, Matrix.le_iff, zero_sub]

theorem PosSemidef.conj_by_isHermitian_posSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] {x y : Matrix n n 𝕜}
  (hx : x.PosSemidef) (hy : y.IsHermitian) :
  PosSemidef (y * x * y) :=
by
  nth_rw 1 [← hy.eq]
  exact PosSemidef.conjTranspose_mul_mul_same hx _

theorem IsHermitian.conj_by_isHermitian_posSemidef {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] {x y : Matrix n n 𝕜}
  (hx : x.IsHermitian) (hy : y.PosSemidef) :
  PosSemidef (x * y * x) :=
by
  nth_rw 1 [← hx.eq]
  exact PosSemidef.conjTranspose_mul_mul_same hy _

alias isHermitian_mul_iff := Matrix.commute_iff

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

end Matrix

lemma StarAlgEquiv.map_pow {R A₁ A₂ : Type _} [CommSemiring R]
  [Semiring A₁] [Semiring A₂] [Algebra R A₁] [Algebra R A₂]
  [Star A₁] [Star A₂]
  (e : A₁ ≃⋆ₐ[R] A₂) (x : A₁) (n : ℕ) :
  e (x ^ n) = e x ^ n :=
by induction n with | zero => simp | succ _ ih => rw [pow_succ', map_mul, ih, ← pow_succ']

lemma Matrix.innerAut.map_pow {n : Type _} [Fintype n] [DecidableEq n] {𝕜 : Type _} [RCLike 𝕜]
  (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) (n : ℕ) :
  (innerAut U x) ^ n = innerAut U (x ^ n) :=
by simp_rw [← innerAutStarAlg_apply_eq_innerAut_apply, StarAlgEquiv.map_pow]
