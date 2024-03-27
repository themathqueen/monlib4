/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.IsROrC.Basic

#align_import preq.is_R_or_C_le

/-!
 # Extra lemmas on IsROrC

 This file contains extra lemmas on `IsROrC`.
-/

namespace IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜]

open scoped ComplexOrder

alias le_def := le_iff_re_im
alias lt_def := lt_iff_re_im
alias nonneg_def := nonneg_iff
alias pos_def := pos_iff
alias nonpos_def := nonpos_iff
alias neg_def := neg_iff

theorem nonneg_def' {x : 𝕜} : 0 ≤ x ↔ (re x : 𝕜) = x ∧ 0 ≤ re x :=
  by
  rw [nonneg_def, ← conj_eq_iff_re, conj_eq_iff_im, and_comm]

@[simp, norm_cast]
theorem real_le_real {x y : ℝ} : (x : 𝕜) ≤ (y : 𝕜) ↔ x ≤ y := by rw [le_def]; simp_rw [ofReal_re, ofReal_im, and_true]

@[simp, norm_cast]
theorem real_lt_real {x y : ℝ} : (x : 𝕜) < (y : 𝕜) ↔ x < y := by simp [@lt_def 𝕜]

@[simp, norm_cast]
theorem zero_le_real {x : ℝ} : 0 ≤ (x : 𝕜) ↔ 0 ≤ x := by
  simp_rw [@nonneg_def 𝕜, ofReal_im, and_true_iff, ofReal_re]

@[simp, norm_cast]
theorem zero_lt_real {x : ℝ} : 0 < (x : 𝕜) ↔ 0 < x := by
  simp_rw [@pos_def 𝕜, ofReal_im, and_true_iff, ofReal_re]

theorem not_le_iff {z w : 𝕜} : ¬z ≤ w ↔ re w < re z ∨ im z ≠ im w := by
  rw [le_def, not_and_or, not_le]

theorem not_lt_iff {z w : 𝕜} : ¬z < w ↔ re w ≤ re z ∨ im z ≠ im w := by
  rw [lt_def, not_and_or, not_lt]

theorem not_le_zero_iff {z : 𝕜} : ¬z ≤ 0 ↔ 0 < re z ∨ im z ≠ 0 := by
  simp only [not_le_iff, map_zero]

theorem not_lt_zero_iff {z : 𝕜} : ¬z < 0 ↔ 0 ≤ re z ∨ im z ≠ 0 := by
  simp only [not_lt_iff, map_zero]

theorem eq_re_ofReal_le {r : ℝ} {z : 𝕜} (hz : (r : 𝕜) ≤ z) : z = re z :=
  by
  rw [IsROrC.ext_iff]
  exact
    ⟨by simp only [ofReal_re], by simp only [← (IsROrC.le_def.1 hz).2, map_zero, IsROrC.ofReal_im]⟩

end IsROrC
