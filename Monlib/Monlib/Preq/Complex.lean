/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Data.Complex.Basic
import Algebra.BigOperators.Fin

#align_import preq.complex

/-!

# Some stuff about complex numbers

This file contains some basic lemmas about complex numbers.

-/


open scoped ComplexConjugate BigOperators

open Complex

/--
$\left|\sum_i\alpha_i^2\right|=\sum_i|\alpha_i|^2$ if and only if $\forall{i,j}\in[n]:\Re(\alpha_i)\Im(\alpha_j)=\Re(\alpha_j)\Im(\alpha_i)$ -/
theorem abs_of_sum_sq_eq_sum_abs_sq_iff {n : Type _} [Fintype n] (α : n → ℂ) :
    abs (∑ i : n, α i ^ 2) = ∑ i : n, abs (α i) ^ 2 ↔
      ∀ i j : n, (α i).re * (α j).im = (α j).re * (α i).im :=
  by
  have complex.abs_sq : ∀ x : ℂ, abs x ^ 2 = norm_sq x :=
    by
    intros
    simp_rw [abs_apply, Real.sq_sqrt (norm_sq_nonneg _)]
  simp_rw [complex.abs_sq, abs_apply]
  rw [Real.sqrt_eq_iff_sq_eq (norm_sq_nonneg _), pow_two, Finset.sum_mul_sum]
  simp_rw [← norm_sq_mul, norm_sq_apply, re_sum, im_sum, Finset.sum_mul_sum, ←
    Finset.sum_add_distrib, pow_two, mul_re, mul_im, sub_mul, mul_sub, mul_add, add_mul]
  rw [← sub_eq_zero]
  have aux_for_ex :
    ∀ x : n × n,
      (α x.fst).re * (α x.snd).re * ((α x.fst).re * (α x.snd).re) -
                (α x.fst).re * (α x.snd).re * ((α x.fst).im * (α x.snd).im) -
              ((α x.fst).im * (α x.snd).im * ((α x.fst).re * (α x.snd).re) -
                (α x.fst).im * (α x.snd).im * ((α x.fst).im * (α x.snd).im)) +
            ((α x.fst).re * (α x.snd).im * ((α x.fst).re * (α x.snd).im) +
                (α x.fst).im * (α x.snd).re * ((α x.fst).re * (α x.snd).im) +
              ((α x.fst).re * (α x.snd).im * ((α x.fst).im * (α x.snd).re) +
                (α x.fst).im * (α x.snd).re * ((α x.fst).im * (α x.snd).re))) -
          ((α x.fst).re * (α x.fst).re * ((α x.snd).re * (α x.snd).re) -
                (α x.fst).re * (α x.fst).re * ((α x.snd).im * (α x.snd).im) -
              ((α x.fst).im * (α x.fst).im * ((α x.snd).re * (α x.snd).re) -
                (α x.fst).im * (α x.fst).im * ((α x.snd).im * (α x.snd).im)) +
            ((α x.fst).re * (α x.fst).im * ((α x.snd).re * (α x.snd).im) +
                (α x.fst).im * (α x.fst).re * ((α x.snd).re * (α x.snd).im) +
              ((α x.fst).re * (α x.fst).im * ((α x.snd).im * (α x.snd).re) +
                (α x.fst).im * (α x.fst).re * ((α x.snd).im * (α x.snd).re)))) =
        2 *
          (((α x.snd).im * (α x.fst).re) ^ 2 -
              2 * ((α x.snd).im * (α x.fst).re) * ((α x.fst).im * (α x.snd).re) +
            ((α x.fst).im * (α x.snd).re) ^ 2) :=
    by
    intros
    simp_rw [← pow_two, sub_sub, mul_comm, ← two_mul]
    ring_nf
  simp_rw [← Finset.sum_sub_distrib, Finset.univ_product_univ, aux_for_ex, ← sub_sq, ←
    Finset.mul_sum, mul_eq_zero, two_ne_zero, false_or_iff]
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  simp_rw [Finset.mem_univ, true_imp_iff, Prod.forall, sq_eq_zero_iff, sub_eq_zero, mul_comm]
  · simp_rw [Finset.mem_univ, true_imp_iff, sq_nonneg, forall_true_iff]
  · apply Finset.sum_nonneg
    intros
    exact norm_sq_nonneg _

theorem abs_of_sq_add_sq_eq_abs_sq_add_abs_sq_iff (α₁ α₂ : ℂ) :
    abs (α₁ ^ 2 + α₂ ^ 2) = abs α₁ ^ 2 + abs α₂ ^ 2 ↔ α₁.re * α₂.im = α₂.re * α₁.im :=
  by
  let α := ![α₁, α₂]
  have h₀ : α 0 = α₁ := rfl
  have h₁ : α 1 = α₂ := rfl
  have hy :
    abs (∑ i : Fin 2, α i ^ 2) = abs (α 0 ^ 2 + α 1 ^ 2) ∧
      ∑ i : Fin 2, abs (α i) ^ 2 = abs (α 0) ^ 2 + abs (α 1) ^ 2 :=
    by
    constructor <;>
      · rw [Finset.sum_eq_add_sum_diff_singleton]
        congr
        ·
          simp only [Finset.sum_sdiff_eq_sub, Finset.subset_univ, Fin.sum_univ_two,
            Finset.sum_singleton, add_sub_cancel']
        · exact Finset.mem_univ _
  simp_rw [← h₀, ← h₁, ← hy.1, ← hy.2, abs_of_sum_sq_eq_sum_abs_sq_iff, Fin.forall_fin_two, h₀, h₁,
    eq_self_iff_true, true_and_iff, and_true_iff, eq_comm, and_self_iff]

theorem abs_of_sq_add_sq_abs_sq_add_abs_sq_iff' (α₁ α₂ : ℂ) :
    abs (α₁ ^ 2 + α₂ ^ 2) = abs α₁ ^ 2 + abs α₂ ^ 2 ↔ α₁ * conj α₂ = conj α₁ * α₂ :=
  by
  rw [abs_of_sq_add_sq_eq_abs_sq_add_abs_sq_iff, ← re_add_im α₁, ← re_add_im α₂]
  simp_rw [add_re, add_im, map_add, conj_of_real, mul_I_im, mul_I_re, starRingEnd_apply, star_mul',
    ← starRingEnd_apply, conj_I, conj_of_real, mul_add, add_mul]
  simp only [of_real_re, of_real_im, MulZeroClass.mul_zero, neg_zero, add_zero,
    MulZeroClass.zero_mul, zero_add, mul_neg, neg_mul, mul_comm _ I, mul_mul_mul_comm, I_mul_I,
    neg_neg, one_mul]
  simp_rw [add_assoc, add_right_inj, ← add_assoc, add_left_inj, mul_comm _ (I * _), add_comm (-_) _,
    Tactic.Ring.add_neg_eq_sub, mul_assoc, ← mul_sub, mul_right_inj' I_ne_zero, ← of_real_mul, ←
    of_real_sub]
  norm_cast
  simp_rw [sub_eq_sub_iff_add_eq_add, ← two_mul, mul_right_inj' two_ne_zero,
    mul_comm _ (Complex.re _), eq_comm]

/--
$\left|\sum_i\alpha_i^2\right|=\sum_i|\alpha_i|^2$ is also equivalent to saying that for any $i,j$ we get $\alpha_i\overline{\alpha_j}=\overline{\alpha_i}\alpha_j$ -/
theorem abs_of_sum_sq_eq_sum_abs_sq_iff' {n : Type _} [Fintype n] (α : n → ℂ) :
    abs (∑ i : n, α i ^ 2) = ∑ i : n, abs (α i) ^ 2 ↔
      ∀ i j : n, α i * conj (α j) = conj (α i) * α j :=
  by
  have := abs_of_sq_add_sq_abs_sq_add_abs_sq_iff'
  simp_rw [abs_of_sq_add_sq_eq_abs_sq_add_abs_sq_iff] at this
  simp_rw [abs_of_sum_sq_eq_sum_abs_sq_iff, this]

theorem abs_of_sq_add_sq_abs_sq_add_abs_sq_iff'' (α₁ α₂ : ℂ) :
    abs (α₁ ^ 2 + α₂ ^ 2) = abs α₁ ^ 2 + abs α₂ ^ 2 ↔
      ∃ (γ : ℂ) (β₁ β₂ : ℝ), α₁ = γ * β₁ ∧ α₂ = γ * β₂ :=
  by
  rw [abs_of_sq_add_sq_eq_abs_sq_add_abs_sq_iff]
  constructor
  · intro h
    rw [← re_add_im α₂, ← re_add_im α₁]
    by_cases h1 : α₂.im = 0
    · by_cases h2 : α₂.re = 0
      · rw [h1, h2, of_real_zero, zero_add, MulZeroClass.zero_mul]
        use α₁
        use 1
        use 0
        simp_rw [re_add_im, of_real_zero, MulZeroClass.mul_zero, of_real_one, mul_one,
          eq_self_iff_true, true_and_iff]
      have : α₂.re = 0 ∨ α₁.im = 0 := by rw [← mul_eq_zero, ← h, h1, MulZeroClass.mul_zero]
      cases this
      · contradiction
      · use 1
        use α₁.re
        use α₂.re
        simp_rw [h1, this, of_real_zero, MulZeroClass.zero_mul, add_zero, one_mul, eq_self_iff_true,
          and_self_iff]
    by_cases h2 : α₂.re = 0
    · have : α₁.re = 0 ∨ α₂.im = 0 := by rw [← mul_eq_zero, h, h2, MulZeroClass.zero_mul]
      cases this
      · use I
        use α₁.im
        use α₂.im
        simp_rw [h2, this, of_real_zero, zero_add, mul_comm, eq_self_iff_true, and_self_iff]
      · contradiction
    use 1 / α₂.im + I * (1 / α₂.re)
    use α₁.re * α₂.im
    use α₂.im * α₂.re
    simp_rw [add_mul, one_div, ← of_real_inv, ← of_real_mul, mul_comm, ← mul_assoc,
      inv_mul_cancel h1, one_mul, mul_rotate, mul_assoc, ← of_real_mul, mul_comm α₂.im _, h, ←
      mul_assoc, inv_mul_cancel h2, one_mul, eq_self_iff_true, and_self_iff]
  · rintro ⟨γ, β₁, β₂, ⟨rfl, rfl⟩⟩
    simp_rw [mul_comm γ _, of_real_mul_re, of_real_mul_im, mul_mul_mul_comm, mul_comm]

/--
$\left|\sum_i\alpha_i^2\right|=\sum_i|\alpha_i|^2$ is equivalent to saying that there exists some $\gamma\in\mathbb{C}$ such that for any $i\in[n]$ we get there exists some $\beta\in\mathbb{R}$ such that $\alpha_i=\gamma\beta$ -/
theorem abs_of_sum_sq_eq_sum_abs_sq_iff'' {n : Type _} [Fintype n] (α : n → ℂ) :
    abs (∑ i : n, α i ^ 2) = ∑ i : n, abs (α i) ^ 2 ↔ ∃ γ : ℂ, ∀ i : n, ∃ β : ℝ, α i = γ * β :=
  by
  have := abs_of_sq_add_sq_abs_sq_add_abs_sq_iff''
  simp_rw [abs_of_sq_add_sq_eq_abs_sq_add_abs_sq_iff] at this
  simp_rw [abs_of_sum_sq_eq_sum_abs_sq_iff, this]
  constructor
  · intro h
    by_cases H : α = 0
    · use 0
      intros
      use 0
      simp_rw [H, Pi.zero_apply, MulZeroClass.zero_mul]
    · have : ∃ i : n, α i ≠ 0 := by simp_rw [Ne.def, ← Classical.not_forall, ← Function.funext_iff];
        exact H
      have := this
      cases' this with i hi
      cases' this with j hj
      obtain ⟨γ, β₁, β₂, ⟨hβ₁, hβ₂⟩⟩ := h i j
      use γ
      intro k
      obtain ⟨γ₂, β₃, β₄, ⟨hβ₃, hβ₄⟩⟩ := h i k
      by_cases h' : β₃ = 0
      · simp_rw [h', of_real_zero, MulZeroClass.mul_zero] at hβ₃
        contradiction
      · use β₁ * (β₄ / β₃)
        simp_rw [of_real_mul, ← mul_assoc, ← hβ₁, hβ₃, mul_assoc, ← of_real_mul,
          mul_div_cancel' _ h', hβ₄]
  · rintro ⟨γ, hγ⟩ i j
    obtain ⟨β₁, hβ₁⟩ := hγ i
    obtain ⟨β₂, hβ₂⟩ := hγ j
    exact ⟨γ, β₁, β₂, ⟨hβ₁, hβ₂⟩⟩

