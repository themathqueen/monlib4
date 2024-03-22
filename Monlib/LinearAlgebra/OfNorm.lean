import LinearAlgebra.MyIps.Basic
import LinearAlgebra.MyIps.Ips
import LinearAlgebra.MyIps.RankOne
import Preq.IsROrCLe

#align_import linear_algebra.of_norm

open scoped ComplexOrder

section Ex4

variable {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem cs_aux {x y : E} (hy : y ≠ 0) :
    ‖x - ((inner y x : 𝕜) * (‖y‖ ^ 2)⁻¹) • y‖ ^ 2 = ‖x‖ ^ 2 - ‖(inner x y : 𝕜)‖ ^ 2 * (‖y‖ ^ 2)⁻¹ :=
  by
  have : ((‖y‖ ^ 2 : ℝ) : 𝕜) ≠ 0 :=
    by
    rw [Ne.def, IsROrC.ofReal_eq_zero, sq_eq_zero_iff, norm_eq_zero]
    exact hy
  rw [← @inner_self_eq_norm_sq 𝕜]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, _root_.map_mul, inner_conj_symm,
    ← IsROrC.ofReal_pow]
  simp_rw [inner_self_eq_norm_sq_to_K, starRingEnd_apply, star_inv', IsROrC.star_def,
    IsROrC.conj_ofReal, mul_assoc, ← IsROrC.ofReal_pow, inv_mul_cancel this, mul_one]
  letI : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
  calc
    IsROrC.re
          (((‖x‖ ^ 2 : ℝ) : 𝕜) - (inner y x : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner x y : 𝕜)) -
              (inner x y : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner y x : 𝕜)) +
            (inner y x : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner x y : 𝕜))) =
        IsROrC.re (((‖x‖ ^ 2 : ℝ) : 𝕜) - (inner x y : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * inner y x)) :=
      _
    _ = IsROrC.re (↑(‖x‖ ^ 2) - ‖(inner x y : 𝕜)‖ ^ 2 * (↑(‖y‖ ^ 2))⁻¹) := _
    _ = ‖x‖ ^ 2 - ‖(inner x y : 𝕜)‖ ^ 2 * (‖y‖ ^ 2)⁻¹ := _
  · congr
    ring_nf
  · rw [mul_rotate', ← inner_conj_symm, IsROrC.conj_mul, mul_comm, IsROrC.normSq_eq_def']
    simp_rw [_root_.map_sub, IsROrC.re_ofReal_mul]
    norm_cast
  · norm_cast

-- already exists in `mathlib`... but different proof... just for fun
example {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(inner x y : 𝕜)‖ = ‖x‖ * ‖y‖ ↔ ∃ α : 𝕜ˣ, x = (α : 𝕜) • y :=
  by
  constructor
  · intro h
    have : (inner y x : 𝕜) ≠ 0 := by
      intro h'
      rw [inner_eq_zero_symm] at h'
      rw [h', norm_zero, eq_comm, mul_eq_zero] at h
      simp_rw [norm_eq_zero, hx, hy, false_or_iff] at h
      exact h
    have hy' : ‖y‖ ^ 2 ≠ 0 := by
      rw [Ne.def, sq_eq_zero_iff, norm_eq_zero]
      exact hy
    rw [← sq_eq_sq (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow, eq_comm, ←
      eq_mul_inv_iff_mul_eq₀ hy', ← sub_eq_zero, ← cs_aux hy, sq_eq_zero_iff, norm_eq_zero,
      sub_eq_zero] at h
    exact
      ⟨Units.mk0 ((inner y x : 𝕜) * ((‖y‖ : 𝕜) ^ 2)⁻¹)
          (mul_ne_zero this
            (by
              rw [Ne.def, inv_eq_zero, sq_eq_zero_iff, IsROrC.ofReal_eq_zero, norm_eq_zero]
              exact hy)),
        h⟩
  · rintro ⟨α, rfl⟩
    simp_rw [inner_smul_left, norm_mul, norm_smul, ← inner_self_re_eq_norm,
      inner_self_eq_norm_mul_norm, mul_assoc, IsROrC.norm_conj]

end Ex4

open IsROrC

open scoped ComplexConjugate

variable {𝕜 X : Type _} [IsROrC 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

noncomputable def OfNorm.innerDef (x y : X) : 𝕜 :=
  4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 + i * ‖(i : 𝕜) • x + y‖ ^ 2 - i * ‖(i : 𝕜) • x - y‖ ^ 2)

namespace OfNorm

theorem re_innerDef (x y : X) : re (innerDef x y : 𝕜) = 4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) := by
  calc
    re (inner_def x y : 𝕜) =
        re
          (4⁻¹ *
              (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 + I * ‖(I : 𝕜) • x + y‖ ^ 2 - I * ‖(I : 𝕜) • x - y‖ ^ 2) :
            𝕜) :=
      rfl
    _ =
        (4⁻¹ : ℝ) *
          re
            (((‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 : ℝ) : 𝕜) +
              I * ((‖(I : 𝕜) • x + y‖ ^ 2 - ‖(I : 𝕜) • x - y‖ ^ 2 : ℝ) : 𝕜)) :=
      by
      rw [mul_re]
      have : im (4 : 𝕜)⁻¹ = 0 := by simp
      simp only [this, MulZeroClass.zero_mul, sub_zero, mul_sub, of_real_sub, of_real_pow]
      simp only [sub_eq_add_neg, add_assoc]
      congr
      ·
        calc
          re (4 : 𝕜)⁻¹ = re ((4 : ℝ) : 𝕜)⁻¹ := by
            congr
            norm_cast
          _ = (re ((4 : ℝ) : 𝕜))⁻¹ :=
            by
            simp_rw [inv_re, norm_sq_eq_def', norm_of_real]
            norm_num
          _ = (4 : ℝ)⁻¹ := by simp only [of_real_re]
    _ = 4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) := by
      rw [_root_.map_add, I_mul_re, of_real_im, neg_zero, add_zero, of_real_re]

theorem im_eq_re_neg_i (x : 𝕜) : im x = re (-(i : 𝕜) * x) := by
  simp only [neg_mul, map_neg, I_mul_re, neg_neg]

theorem innerDef_zero_left (x : X) : (innerDef 0 x : 𝕜) = 0 := by
  simp only [inner_def, smul_zero, zero_add, zero_sub, norm_neg, sub_self, MulZeroClass.mul_zero]

theorem innerDef_i_smul_left (x y : X) : (innerDef ((i : 𝕜) • x) y : 𝕜) = (-i : 𝕜) * innerDef x y :=
  by
  by_cases hI : (I : 𝕜) = 0
  · simp_rw [hI, zero_smul, inner_def_zero_left, neg_zero, MulZeroClass.zero_mul]
  have hI' : (-I : 𝕜) * I = 1 := by rw [← inv_I, inv_mul_cancel hI]
  simp only [inner_def, smul_eq_mul, ← mul_assoc, mul_comm (-I : 𝕜) 4⁻¹]
  simp only [mul_assoc]
  congr 1
  rw [smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, neg_sub_left, norm_neg]
  simp only [mul_add, mul_sub]
  simp_rw [← mul_assoc, hI', one_mul, neg_mul]
  rw [sub_neg_eq_add]
  have : ‖x - y‖ = ‖-x + y‖ := by rw [← norm_neg, neg_sub', sub_eq_add_neg, neg_neg]
  rw [this, add_comm x y]
  ring_nf

theorem im_innerDef_aux (x y : X) : im (innerDef x y : 𝕜) = re (innerDef ((i : 𝕜) • x) y : 𝕜) := by
  rw [im_eq_re_neg_I, ← inner_def_I_smul_left]

theorem re_innerDef_symm (x y : X) : re (innerDef x y : 𝕜) = re (innerDef y x : 𝕜) :=
  by
  simp_rw [re_inner_def]
  rw [add_comm]
  congr 2
  simp only [sq_eq_sq, norm_nonneg, norm_sub_rev]

theorem im_innerDef_symm (x y : X) : im (innerDef x y : 𝕜) = -im (innerDef y x : 𝕜) :=
  by
  simp_rw [im_inner_def_aux]
  rw [re_inner_def_symm]
  by_cases (I : 𝕜) = 0
  ·
    simp only [re_inner_def, h, zero_smul, zero_add, add_zero, zero_sub, sub_zero, sub_self,
      norm_neg, MulZeroClass.mul_zero, neg_zero]
  · have := norm_I_of_ne_zero h
    simp only [re_inner_def, ← neg_mul, neg_mul_comm]
    congr 1
    simp only [neg_sub]
    have h₁ : ∀ a : X, ‖a‖ = ‖(I : 𝕜) • a‖ := fun a => by
      rw [norm_smul, norm_I_of_ne_zero h, one_mul]
    rw [h₁ (y + (I : 𝕜) • x), h₁ (y - (I : 𝕜) • x)]
    simp only [smul_add, smul_sub, smul_smul, I_mul_I_of_nonzero h, neg_one_smul]
    simp_rw [sub_eq_add_neg, neg_neg]

theorem innerDef_conj (x y : X) : conj (innerDef x y : 𝕜) = innerDef y x :=
  by
  rw [← @re_add_im 𝕜 _ (inner_def x y)]
  simp_rw [map_add, map_mul, conj_of_real, conj_I]
  calc
    ↑(re (inner_def x y : 𝕜)) + ↑(im (inner_def x y : 𝕜)) * -(I : 𝕜) =
        ↑(re (inner_def y x : 𝕜)) + ↑(-im (inner_def x y : 𝕜)) * (I : 𝕜) :=
      by
      rw [re_inner_def_symm]
      congr 1
      simp
    _ = ↑(re (inner_def y x : 𝕜)) + ↑(im (inner_def y x : 𝕜)) * (I : 𝕜) := by
      rw [← im_inner_def_symm]
    _ = inner_def y x := re_add_im _

section FromMathlib4

/-!
  In this section we show the addition property and scalar-multiplication property by mimicking (and copying) the `Mathlib4` code on `InnerProductSpace.ofNorm`.
-/


private theorem add_left_aux1
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
    (x y z : X) :
    ‖x + y + z‖ * ‖x + y + z‖ =
      (‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖) / 2 - ‖x - z‖ * ‖x - z‖ :=
  by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  convert h (x + y + z) (x - z) using 4
  all_goals rw [two_smul]; abel

private theorem add_left_aux2
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
    (x y z : X) :
    ‖x + y - z‖ * ‖x + y - z‖ =
      (‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 - ‖x + z‖ * ‖x + z‖ :=
  by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  have h₀ := h (x + y - z) (x + z)
  convert h₀ using 4
  all_goals rw [two_smul]; abel

private theorem add_left_aux2'
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
    (x y z : X) :
    ‖x + y + z‖ * ‖x + y + z‖ - ‖x + y - z‖ * ‖x + y - z‖ =
      ‖x + z‖ * ‖x + z‖ - ‖x - z‖ * ‖x - z‖ +
        (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 :=
  by rw [add_left_aux1 h, add_left_aux2 h] <;> ring

private theorem add_left_aux3
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
    ‖2 • z + y‖ * ‖2 • z + y‖ = 2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ :=
  by
  apply eq_sub_of_add_eq
  convert h (y + z) z using 4
  all_goals try rw [two_smul]; abel

private theorem add_left_aux4
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
    ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ :=
  by
  apply eq_sub_of_add_eq'
  have h₀ := h (y - z) z
  convert h₀ using 4
  all_goals try rw [two_smul]; abel

private theorem add_left_aux4'
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
    (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 =
      ‖y + z‖ * ‖y + z‖ - ‖y - z‖ * ‖y - z‖ :=
  by rw [add_left_aux3 h, add_left_aux4 h] <;> ring

private theorem add_left_aux5
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
    (x y z : X) :
    ‖(i : 𝕜) • (x + y) + z‖ * ‖(i : 𝕜) • (x + y) + z‖ =
      (‖(i : 𝕜) • (2 • x + y)‖ * ‖(i : 𝕜) • (2 • x + y)‖ +
            ‖(i : 𝕜) • y + 2 • z‖ * ‖(i : 𝕜) • y + 2 • z‖) /
          2 -
        ‖(i : 𝕜) • x - z‖ * ‖(i : 𝕜) • x - z‖ :=
  by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  have h₀ := h ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z)
  convert h₀ using 4
  all_goals try simp only [two_smul, smul_add]; abel

private theorem add_left_aux6
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
    (x y z : X) :
    ‖(i : 𝕜) • (x + y) - z‖ * ‖(i : 𝕜) • (x + y) - z‖ =
      (‖(i : 𝕜) • (2 • x + y)‖ * ‖(i : 𝕜) • (2 • x + y)‖ +
            ‖(i : 𝕜) • y - 2 • z‖ * ‖(i : 𝕜) • y - 2 • z‖) /
          2 -
        ‖(i : 𝕜) • x + z‖ * ‖(i : 𝕜) • x + z‖ :=
  by
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm]
  have h₀ := h ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z)
  convert h₀ using 4
  all_goals try simp only [two_smul, smul_add]; abel

private theorem add_left_aux7
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
    ‖(i : 𝕜) • y + 2 • z‖ * ‖(i : 𝕜) • y + 2 • z‖ =
      2 * (‖(i : 𝕜) • y + z‖ * ‖(i : 𝕜) • y + z‖ + ‖z‖ * ‖z‖) - ‖(i : 𝕜) • y‖ * ‖(i : 𝕜) • y‖ :=
  by
  apply eq_sub_of_add_eq
  have h₀ := h ((I : 𝕜) • y + z) z
  convert h₀ using 4
  all_goals try simp only [two_smul, smul_add]; abel

private theorem add_left_aux8
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (y z : X) :
    ‖(i : 𝕜) • y - 2 • z‖ * ‖(i : 𝕜) • y - 2 • z‖ =
      2 * (‖(i : 𝕜) • y - z‖ * ‖(i : 𝕜) • y - z‖ + ‖z‖ * ‖z‖) - ‖(i : 𝕜) • y‖ * ‖(i : 𝕜) • y‖ :=
  by
  apply eq_sub_of_add_eq'
  have h₀ := h ((I : 𝕜) • y - z) z
  convert h₀ using 4
  all_goals try simp only [two_smul, smul_add]; abel

theorem innerDef_add_left
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
    (x y z : X) : (innerDef (x + y) z : 𝕜) = innerDef x z + innerDef y z :=
  by
  simp only [inner_def, ← mul_add]
  congr
  simp only [mul_assoc, ← map_mul, add_sub_assoc, ← mul_sub, ← map_sub]
  rw [add_add_add_comm]
  simp only [← map_add, ← mul_add, pow_two, ← of_real_mul, ← of_real_sub, ← of_real_add]
  congr
  · rw [← add_sub_assoc, add_left_aux2' h x y z, add_left_aux4' h]
  · rw [add_sub]
    by_cases h₀ : (I : 𝕜) = 0
    · simp only [h₀, zero_smul, zero_add, zero_sub, sub_self, norm_neg]
    · have h₀₀ := I_mul_I_of_nonzero h₀
      have h₀₁ := norm_I_of_ne_zero h₀
      rw [add_left_aux5 h, add_left_aux6 h, add_left_aux7 h, add_left_aux8 h]
      simp only [map_sub, map_mul, map_add, div_eq_mul_inv]
      ring_nf

theorem innerDef_nsmul_left
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (n : ℕ)
    (x y : X) : innerDef ((n : 𝕜) • x) y = (n : 𝕜) * innerDef x y :=
  by
  induction' n with n hd
  ·
    simp only [inner_def, zero_sub, Nat.cast_zero, MulZeroClass.zero_mul, eq_self_iff_true,
      zero_smul, zero_add, MulZeroClass.mul_zero, sub_self, norm_neg, smul_zero]
  · simp only [Nat.cast_succ, add_smul, one_smul, add_mul, one_mul]
    rw [← hd, ← inner_def_add_left h]

theorem innerDef_neg_one_smul_left (x y : X) :
    (innerDef (((-1 : ℤ) : 𝕜) • x) y : 𝕜) = -innerDef x y :=
  by
  simp only [inner_def, neg_mul_eq_neg_mul, one_mul, Int.cast_one, one_smul, RingHom.map_one,
    map_neg, Int.cast_neg, neg_smul, neg_one_mul]
  rw [neg_mul_comm]
  congr 1
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  have h₃ : ‖(I : 𝕜) • -x + y‖ = ‖(I : 𝕜) • x - y‖ := by
    rw [← neg_sub, norm_neg, sub_eq_neg_add, ← smul_neg]
  have h₄ : ‖(I : 𝕜) • -x - y‖ = ‖(I : 𝕜) • x + y‖ := by rw [smul_neg, ← neg_add', norm_neg]
  rw [h₁, h₂, h₃, h₄]
  ring

private theorem inner_def_zsmul_left
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (n : ℤ)
    (x y : X) : innerDef ((n : 𝕜) • x) y = (n : 𝕜) * innerDef x y :=
  by
  rw [← n.sign_mul_nat_abs]
  simp only [Int.cast_ofNat, map_natCast, map_intCast, Int.cast_mul, map_mul, mul_smul]
  obtain hn | rfl | hn := lt_trichotomy n 0
  · rw [Int.sign_eq_neg_one_of_neg hn, inner_def_neg_one_smul_left, Int.cast_ofNat,
      inner_def_nsmul_left h n.nat_abs]
    simp only [Int.cast_one, Int.cast_neg, neg_one_mul, neg_mul, one_mul]
  · simp [inner_def_zero_left]
  · rw [Int.sign_eq_one_of_pos hn]
    simp only [Int.cast_one, one_smul, one_mul, Int.cast_ofNat, inner_def_nsmul_left h]

private theorem inner_def_rat_smul_left
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (r : ℚ)
    (x y : X) : (innerDef ((r : 𝕜) • x) y : 𝕜) = (r : 𝕜) • innerDef x y :=
  by
  have : (r.denom : 𝕜) ≠ 0 :=
    by
    haveI : CharZero 𝕜 := IsROrC.charZero_isROrC
    norm_cast
    exact r.pos.ne'
  rw [← r.num_div_denom, ← mul_right_inj' this, Rat.cast_div]
  simp only [map_natCast, Rat.cast_coe_nat, map_intCast, Rat.cast_coe_int, map_div₀]
  simp_rw [div_eq_mul_inv, ← smul_smul, inner_def_zsmul_left h]
  rw [← mul_assoc, mul_comm ↑r.denom _, mul_assoc, ← inner_def_nsmul_left h]
  simp [smul_smul, ← mul_assoc]
  rw [mul_rotate ↑r.denom]
  simp only [mul_assoc]
  congr 1
  simp only [← mul_assoc, inv_mul_cancel this, mul_inv_cancel this, one_smul, one_mul]

theorem Continuous.innerDef {f g : ℝ → X} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x : ℝ => (innerDef (f x) (g x) : 𝕜) :=
  by
  unfold inner_def
  continuity

private theorem inner_def_rsmul_left
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (r : ℝ)
    (x y : X) : innerDef ((r : 𝕜) • x) y = (r : 𝕜) * innerDef x y :=
  by
  revert r
  rw [← Function.funext_iff]
  refine' rat.dense_embedding_coe_real.dense.equalizer _ _ (funext fun _ => _)
  · exact (continuous_of_real.smul continuous_const).innerDef continuous_const
  · continuity
  · simp only [Function.comp_apply, IsROrC.ofReal_ratCast, inner_def_rat_smul_left h]
    rfl

theorem innerDef_smul_left
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) (r : 𝕜)
    (x y : X) : innerDef (r • x) y = conj r * innerDef x y :=
  by
  rw [← re_add_im r, add_smul, inner_def_add_left h, inner_def_rsmul_left h, ← smul_smul,
    inner_def_rsmul_left h, inner_def_I_smul_left, map_add, map_mul, conj_of_real, conj_of_real,
    conj_I]
  ring

/-!
 End of section from `Mathlib4`.
-/


end FromMathlib4

noncomputable def InnerProductSpacce.ofNorm
    (h : ∀ x y : X, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    InnerProductSpace 𝕜 X where
  inner x y := innerDef x y
  norm_sq_eq_inner x := by
    simp only [inner, re_inner_def, pow_two]
    specialize h x x
    simp only [sub_self, norm_zero, MulZeroClass.zero_mul, sub_zero, add_zero] at h ⊢
    simp only [h, ← two_mul, ← mul_assoc]
    norm_num
  conj_symm x y := innerDef_conj y x
  add_left x y z := innerDef_add_left h _ _ _
  smul_left r x y := innerDef_smul_left h _ _ _

end OfNorm

open scoped ComplexConjugate

def IsContinuousLinearMap (𝕜 : Type _) [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E → F) : Prop :=
  IsLinearMap 𝕜 f ∧ Continuous f

def IsContinuousLinearMap.mk' {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}
    (h : IsContinuousLinearMap 𝕜 f) : E →L[𝕜] F :=
  ⟨h.1.mk' f, h.2⟩

theorem IsContinuousLinearMap.coe_mk' {𝕜 : Type _} [NormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} (h : IsContinuousLinearMap 𝕜 f) : f = h.mk' :=
  rfl

theorem isBoundedLinearMap_iff_isContinuousLinearMap {𝕜 E : Type _} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) : IsBoundedLinearMap 𝕜 f ↔ IsContinuousLinearMap 𝕜 f :=
  by
  refine'
    ⟨fun h => ⟨IsBoundedLinearMap.to_isLinearMap h, IsBoundedLinearMap.continuous h⟩, fun h => _⟩
  let f' : E →L[𝕜] F := ⟨h.1.mk' f, h.2⟩
  exact f'.is_bounded_linear_map

private theorem linear_map.is_bounded_linear_map_iff_is_continuous {𝕜 E : Type _}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →ₗ[𝕜] F) :
    IsBoundedLinearMap 𝕜 f ↔ Continuous f :=
  by
  rw [isBoundedLinearMap_iff_isContinuousLinearMap, IsContinuousLinearMap]
  simp only [and_iff_right_iff_imp, f.is_linear, imp_true_iff]

def WithBound {E : Type _} [NormedAddCommGroup E] {F : Type _} [NormedAddCommGroup F] (f : E → F) :
    Prop :=
  ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖

theorem IsBoundedLinearMap.def {𝕜 E : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} :
    IsBoundedLinearMap 𝕜 f ↔ IsLinearMap 𝕜 f ∧ WithBound f :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem LinearMap.withBound_iff_is_continuous {𝕜 E : Type _} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →ₗ[𝕜] F} : WithBound f ↔ Continuous f :=
  by
  have := @isBoundedLinearMap_iff_isContinuousLinearMap 𝕜 _ _ _ _ _ _ _ f
  simp only [IsBoundedLinearMap.def, IsContinuousLinearMap, and_congr_right_iff, f.is_linear,
    true_imp_iff] at this
  exact this

theorem LinearMap.ker_coe_def {R E F : Type _} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R E] [Module R F] {f : E →ₗ[R] F} : (f.ker : Set E) = {x : E | f x = 0} :=
  rfl

theorem exists_dual_vector_of_ne {X : Type _} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {x y : X}
    (h : x ≠ y) : ∃ f : NormedSpace.Dual 𝕜 X, f x ≠ f y :=
  by
  rw [Ne.def, ← sub_eq_zero] at h
  obtain ⟨f, ⟨hf, hxy⟩⟩ := @exists_dual_vector 𝕜 _ X _ _ _ h
  rw [map_sub] at hxy
  use f
  intro H
  rw [H, sub_self, eq_comm, IsROrC.ofReal_eq_zero, norm_eq_zero] at hxy
  contradiction

theorem isLinearMap_zero (R : Type _) {E F : Type _} [CommSemiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] : IsLinearMap R (0 : E → F) := by
  fconstructor <;> simp only [Pi.zero_apply, smul_zero, add_zero] <;> intros <;> trivial

theorem isContinuousLinearMapZero {𝕜 E : Type _} [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    IsContinuousLinearMap 𝕜 (0 : E → F) :=
  ⟨isLinearMap_zero 𝕜, continuous_zero⟩

open scoped Classical Topology BigOperators NNReal

theorem IsContinuousLinearMap.ofInnerSymmetricFun {X : Type _} [NormedAddCommGroup X]
    [InnerProductSpace 𝕜 X] [CompleteSpace X] {f : X → X}
    (h : ∀ a b : X, (inner (f a) b : 𝕜) = inner a (f b)) : IsContinuousLinearMap 𝕜 f :=
  by
  have : IsLinearMap 𝕜 f :=
    { map_add := fun x y => by
        apply @ext_inner_right 𝕜
        intro z
        simp_rw [h, inner_add_left, h]
      map_smul := fun r x => by
        apply @ext_inner_right 𝕜
        intro z
        simp_rw [h, inner_smul_left, h] }
  let f' : X →ₗ[𝕜] X := IsLinearMap.mk' _ this
  have : f = f' := rfl
  simp only [this] at *
  clear this
  exact ⟨f'.is_linear, LinearMap.IsSymmetric.continuous h⟩

structure IsBilinearMap (𝕜 : Type _) [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (f : E × F → G) : Prop where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
  smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
  smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)

def IsLeftLinearMap (𝕜 : Type _) [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (f : E × F → G) : Prop :=
  ∀ b : F, IsLinearMap 𝕜 fun a => f (a, b)

theorem isLeftLinearMap_iff {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} : IsLeftLinearMap 𝕜 f ↔ ∀ b : F, IsLinearMap 𝕜 fun a => f (a, b) :=
  Iff.rfl

def IsRightLinearMap (𝕜 : Type _) [NormedField 𝕜] {E : Type _} {F : Type _} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G] (f : E × F → G) :
    Prop :=
  ∀ a : E, IsLinearMap 𝕜 fun b => f (a, b)

theorem isRightLinearMap_iff {𝕜 : Type _} [NormedField 𝕜] {E : Type _} {F : Type _}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} : IsRightLinearMap 𝕜 f ↔ ∀ a : E, IsLinearMap 𝕜 fun b => f (a, b) :=
  Iff.rfl

theorem isBilinearMap_iff_is_linear_map_left_right {𝕜 : Type _} [NormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E × F → G} :
    IsBilinearMap 𝕜 f ↔ IsLeftLinearMap 𝕜 f ∧ IsRightLinearMap 𝕜 f :=
  by
  constructor
  · intro hf
    constructor
    · intro x
      exact ⟨fun y z => hf.add_left y z x, fun r a => hf.smul_left r a x⟩
    · intro x
      exact ⟨fun y z => hf.add_right x y z, fun r a => hf.smul_right r x a⟩
  · rintro ⟨h1, h2⟩
    fconstructor
    · intro x₁ x₂ y
      exact (h1 y).map_add _ _
    · intro r x y
      exact (h1 y).map_smul _ _
    · intro y x₁ x₂
      exact (h2 y).map_add _ _
    · intro r x y
      exact (h2 x).map_smul _ _

def IsBilinearMap.toLmLm {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E × F → G} (hf : IsBilinearMap 𝕜 f) :
    E →ₗ[𝕜] F →ₗ[𝕜] G
    where
  toFun x :=
    { toFun := fun y => f (x, y)
      map_add' := fun y z => hf.add_right x _ _
      map_smul' := fun r y => hf.smul_right r x y }
  map_add' y z := by
    ext
    simp only [LinearMap.add_apply]
    exact hf.add_left y z x
  map_smul' r z := by
    ext
    simp only [LinearMap.smul_apply]
    exact hf.smul_left r z x

def IsLmLeftIsClmRight.toLmClm {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E × F → G}
    (hf₁ : ∀ y, IsLinearMap 𝕜 fun a => f (a, y))
    (hf₂ : ∀ x, IsContinuousLinearMap 𝕜 fun a => f (x, a)) : E →ₗ[𝕜] F →L[𝕜] G
    where
  toFun x := (hf₂ x).mk'
  map_add' y z := by
    ext
    simp only [ContinuousLinearMap.add_apply]
    exact (hf₁ x).map_add _ _
  map_smul' r z := by
    ext
    exact (hf₁ x).map_smul _ _

theorem IsBilinearMap.zero_left {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E × F → G} (h : IsBilinearMap 𝕜 f) (y : F) :
    f (0, y) = 0 := by
  simp only [isBilinearMap_iff_is_linear_map_left_right] at h
  exact (h.1 y).map_zero

theorem IsBilinearMap.zero_right {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E × F → G} (h : IsBilinearMap 𝕜 f) (x : E) :
    f (x, 0) = 0 := by
  simp only [isBilinearMap_iff_is_linear_map_left_right] at h
  exact (h.2 x).map_zero

theorem IsBilinearMap.eq_zero_add_self {𝕜 : Type _} [NormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E × F → G} (h : IsBilinearMap 𝕜 f)
    (xy : E × F) : f xy = f (xy.1, 0) + f xy := by simp_rw [h.zero_right, zero_add]

open scoped ComplexOrder

theorem IsContinuousLinearMap.to_is_lm {𝕜 X Y : Type _} [NormedField 𝕜] [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] {β : X → Y}
    (hf : IsContinuousLinearMap 𝕜 β) : IsLinearMap 𝕜 β :=
  hf.1

#print ContinuousLinearMap.op_norm_le_iff /-
theorem ContinuousLinearMap.op_norm_le_iff {𝕜 X Y : Type _} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) {r : ℝ} (hr : 0 ≤ r) : ‖f‖ ≤ r ↔ ∀ x, ‖f x‖ ≤ r * ‖x‖ :=
  by
  constructor
  · intro hf x
    exact f.le_of_op_norm_le hf _
  · intro h
    exact f.op_norm_le_bound hr h
-/

example
    --is_continuous_bilinear_map_norm_of_clm
    {𝕜 X Y Z : Type _}
    [IsROrC 𝕜] [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z] [CompleteSpace X] [CompleteSpace Y]
    [CompleteSpace Z] (β : X →L[𝕜] Y →L[𝕜] Z) : ∃ M : ℝ, ∀ x y, ‖β x y‖ ≤ M * ‖x‖ * ‖y‖ :=
  by
  use‖β‖
  intro x y
  apply ContinuousLinearMap.le_of_opNorm_le
  exact ContinuousLinearMap.le_opNorm _ _

