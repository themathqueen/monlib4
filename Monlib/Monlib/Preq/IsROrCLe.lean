/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Data.IsROrC.Basic

#align_import preq.is_R_or_C_le

/-!
 # Strictly ordered field structure on `𝕜`

 This file defines the following structures on `𝕜`.
-/


namespace IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜]

protected def partialOrder : PartialOrder 𝕜
    where
  le z w := re z ≤ re w ∧ im z = im w
  lt z w := re z < re w ∧ im z = im w
  lt_iff_le_not_le z w := by dsimp; rw [lt_iff_le_not_le]; tauto
  le_refl x := ⟨le_rfl, rfl⟩
  le_trans x y z h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm z w h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2

scoped[ComplexOrder] attribute [instance] IsROrC.partialOrder

theorem le_def {z w : 𝕜} : z ≤ w ↔ re z ≤ re w ∧ im z = im w :=
  Iff.rfl

theorem lt_def {z w : 𝕜} : z < w ↔ re z < re w ∧ im z = im w :=
  Iff.rfl

theorem nonneg_def {x : 𝕜} : 0 ≤ x ↔ 0 ≤ re x ∧ im x = 0 := by
  simp only [le_def, map_zero, one_im, one_re, iff_self_iff, eq_comm]

theorem pos_def {x : 𝕜} : 0 < x ↔ 0 < re x ∧ im x = 0 := by
  simp only [lt_def, map_zero, one_im, one_re, iff_self_iff, eq_comm]

theorem nonpos_def {x : 𝕜} : x ≤ 0 ↔ re x ≤ 0 ∧ im x = 0 := by
  simp only [le_def, map_zero, one_im, one_re, iff_self_iff, eq_comm]

theorem neg_def {x : 𝕜} : x < 0 ↔ re x < 0 ∧ im x = 0 := by
  simp only [lt_def, map_zero, one_im, one_re, iff_self_iff, eq_comm]

theorem nonneg_def' {x : 𝕜} : 0 ≤ x ↔ (re x : 𝕜) = x ∧ 0 ≤ re x := by
  simp_rw [nonneg_def, ← conj_eq_iff_re, conj_eq_iff_im, and_comm']

@[simp, norm_cast]
theorem real_le_real {x y : ℝ} : (x : 𝕜) ≤ (y : 𝕜) ↔ x ≤ y := by simp [le_def]

@[simp, norm_cast]
theorem real_lt_real {x y : ℝ} : (x : 𝕜) < (y : 𝕜) ↔ x < y := by simp [lt_def]

@[simp, norm_cast]
theorem zero_le_real {x : ℝ} : 0 ≤ (x : 𝕜) ↔ 0 ≤ x := by
  simp_rw [nonneg_def, of_real_im, eq_self_iff_true, and_true_iff, of_real_re]

@[simp, norm_cast]
theorem zero_lt_real {x : ℝ} : 0 < (x : 𝕜) ↔ 0 < x := by
  simp_rw [pos_def, of_real_im, eq_self_iff_true, and_true_iff, of_real_re]

theorem not_le_iff {z w : 𝕜} : ¬z ≤ w ↔ re w < re z ∨ im z ≠ im w := by
  rw [le_def, not_and_or, not_le]

theorem not_lt_iff {z w : 𝕜} : ¬z < w ↔ re w ≤ re z ∨ im z ≠ im w := by
  rw [lt_def, not_and_or, not_lt]

theorem not_le_zero_iff {z : 𝕜} : ¬z ≤ 0 ↔ 0 < re z ∨ im z ≠ 0 := by
  simp only [not_le_iff, map_zero]

theorem not_lt_zero_iff {z : 𝕜} : ¬z < 0 ↔ 0 ≤ re z ∨ im z ≠ 0 := by
  simp only [not_lt_iff, map_zero]

theorem eq_re_of_real_le {r : ℝ} {z : 𝕜} (hz : (r : 𝕜) ≤ z) : z = re z :=
  by
  rw [IsROrC.ext_iff]
  exact
    ⟨by simp only [of_real_re], by simp only [← (IsROrC.le_def.1 hz).2, map_zero, IsROrC.ofReal_im]⟩

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `𝕜` is a strictly ordered ring.
-/
protected def strictOrderedCommRing : StrictOrderedCommRing 𝕜 :=
  { IsROrC.partialOrder, Field.toCommRing 𝕜,
    IsDomain.to_nontrivial
      𝕜 with
    zero_le_one := by rw [nonneg_def];
      simp only [one_re, zero_le_one, one_im, eq_self_iff_true, and_self_iff]
    add_le_add_left := fun w z h y => by
      simp only [le_def, map_add]
      exact ⟨add_le_add_left h.1 _, congr_arg₂ _ rfl (le_def.mp h).2⟩
    mul_pos := fun z w hz hw => by
      simp [lt_def, mul_re, mul_im, ← hz.2, ← hw.2, mul_pos (pos_def.mp hz).1 (pos_def.mp hw).1] }

scoped[ComplexOrder] attribute [instance] IsROrC.strictOrderedCommRing

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `𝕜` is a star ordered ring.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)
-/
protected def starOrderedRing : StarOrderedRing 𝕜 :=
  StarOrderedRing.ofNonnegIff' (fun _ _ => add_le_add_left) fun r =>
    by
    refine' ⟨fun hr => ⟨Real.sqrt (re r), _⟩, fun h => _⟩
    · have h₁ : 0 ≤ re r := by rw [nonneg_def] at hr; exact hr.1
      have h₂ : im r = 0 := by rw [nonneg_def] at hr; exact hr.2
      rw [ext_iff]
      constructor
      ·
        simp only [of_real_im, star_def, of_real_re, sub_zero, conj_re, mul_re,
          MulZeroClass.mul_zero, ← Real.sqrt_mul h₁ (re r), Real.sqrt_mul_self h₁]
      ·
        simp only [h₂, add_zero, of_real_im, star_def, MulZeroClass.zero_mul, conj_im, mul_im,
          MulZeroClass.mul_zero, neg_zero]
    · obtain ⟨s, rfl⟩ := h
      simp only [conj_mul, norm_sq_nonneg, zero_le_real, star_def]

scoped[ComplexOrder] attribute [instance] IsROrC.starOrderedRing

end IsROrC

