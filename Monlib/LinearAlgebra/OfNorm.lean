import Monlib.LinearAlgebra.MyIps.Basic
import Monlib.LinearAlgebra.MyIps.Ips
import Monlib.LinearAlgebra.MyIps.RankOne
import Monlib.Preq.RCLikeLe
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Extreme

#align_import linear_algebra.of_norm

open scoped ComplexOrder

section Ex4

variable {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem cs_aux {x y : E} (hy : y ≠ 0) :
    ‖x - ((inner y x : 𝕜) * (‖y‖ ^ 2 : ℝ)⁻¹) • y‖ ^ 2 = ‖x‖ ^ 2 - ‖(inner x y : 𝕜)‖ ^ 2 * (‖y‖ ^ 2)⁻¹ :=
  by
  have : ((‖y‖ ^ 2 : ℝ) : 𝕜) ≠ 0 :=
    by
    rw [Ne.def, RCLike.ofReal_eq_zero, sq_eq_zero_iff, norm_eq_zero]
    exact hy
  rw [← @inner_self_eq_norm_sq 𝕜]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, _root_.map_mul, inner_conj_symm,
    ← RCLike.ofReal_pow]
  simp_rw [inner_self_eq_norm_sq_to_K, starRingEnd_apply,
    RCLike.ofReal_inv, star_inv', RCLike.star_def,
    RCLike.conj_ofReal, mul_assoc, ← RCLike.ofReal_pow, inv_mul_cancel this, mul_one]
  letI : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
  calc
    RCLike.re
          (((‖x‖ ^ 2 : ℝ) : 𝕜) - (inner y x : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner x y : 𝕜)) -
              (inner x y : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner y x : 𝕜)) +
            (inner y x : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * (inner x y : 𝕜))) =
        RCLike.re (((‖x‖ ^ 2 : ℝ) : 𝕜) - (inner x y : 𝕜) * (((‖y‖ ^ 2 : ℝ) : 𝕜)⁻¹ * inner y x)) :=
      ?_
    _ = RCLike.re (↑(‖x‖ ^ 2) - ‖(inner x y : 𝕜)‖ ^ 2 * (↑(‖y‖ ^ 2))⁻¹) := ?_
    _ = ‖x‖ ^ 2 - ‖(inner x y : 𝕜)‖ ^ 2 * (‖y‖ ^ 2)⁻¹ := ?_
  · congr
    ring_nf
  · rw [mul_rotate', ← inner_conj_symm, RCLike.conj_mul, mul_comm,
      ← RCLike.normSq_eq_def', RCLike.normSq_eq_def']
    simp_rw [_root_.map_sub, ← RCLike.ofReal_inv,
      ← RCLike.ofReal_pow, ← RCLike.ofReal_mul]
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
    have hy' : ‖y‖ ^ 2 ≠ 0 := by
      rw [Ne.def, sq_eq_zero_iff, norm_eq_zero]
      exact hy
    rw [← sq_eq_sq (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow, eq_comm, ←
      eq_mul_inv_iff_mul_eq₀ hy', ← sub_eq_zero, ← cs_aux hy, sq_eq_zero_iff, norm_eq_zero,
      sub_eq_zero] at h
    use Units.mk0 ((inner y x : 𝕜) * ((‖y‖ : 𝕜) ^ 2)⁻¹)
          (mul_ne_zero this
            (by
              rw [Ne.def, inv_eq_zero, sq_eq_zero_iff, RCLike.ofReal_eq_zero, norm_eq_zero]
              exact hy))
    norm_cast at h ⊢
  · rintro ⟨α, rfl⟩
    simp_rw [inner_smul_left, norm_mul, norm_smul, ← inner_self_re_eq_norm,
      inner_self_eq_norm_mul_norm, mul_assoc, RCLike.norm_conj]

end Ex4

open RCLike

open scoped ComplexConjugate

variable {𝕜 X : Type _} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

noncomputable def OfNorm.innerDef (x y : X) : 𝕜 :=
  4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 + I * ‖(I : 𝕜) • x + y‖ ^ 2 - I * ‖(I : 𝕜) • x - y‖ ^ 2)

namespace OfNorm

theorem re_innerDef (x y : X) : re (innerDef x y : 𝕜) = 4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) := by
  calc
    re (innerDef x y : 𝕜) =
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
      simp only [this, MulZeroClass.zero_mul, sub_zero, mul_sub, ofReal_sub, ofReal_pow]
      simp only [sub_eq_add_neg, add_assoc]
      congr
      ·
        calc
          re (4 : 𝕜)⁻¹ = re ((4 : ℝ) : 𝕜)⁻¹ := by
            congr
            norm_cast
          _ = (re ((4 : ℝ) : 𝕜))⁻¹ :=
            by
            simp_rw [inv_re, normSq_eq_def', norm_ofReal]
            norm_num
          _ = (4 : ℝ)⁻¹ := by simp only [ofReal_re]
    _ = 4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) := by
      rw [_root_.map_add, I_mul_re, ofReal_im, neg_zero, add_zero, ofReal_re]

theorem im_eq_re_neg_i (x : 𝕜) : im x = re (-(I : 𝕜) * x) := by
  simp only [neg_mul, map_neg, I_mul_re, neg_neg]

theorem innerDef_zero_left (x : X) : (innerDef 0 x : 𝕜) = 0 := by
  simp only [innerDef, smul_zero, zero_add, zero_sub, norm_neg, sub_self, MulZeroClass.mul_zero]

theorem innerDef_i_smul_left (x y : X) : (innerDef ((I : 𝕜) • x) y : 𝕜) = (-I : 𝕜) * innerDef x y :=
  by
  by_cases hI : (I : 𝕜) = 0
  · simp_rw [hI, zero_smul, innerDef_zero_left, neg_zero, MulZeroClass.zero_mul]
  have hI' : (-I : 𝕜) * I = 1 := by rw [← inv_I, inv_mul_cancel hI]
  simp only [innerDef, smul_eq_mul, ← mul_assoc, mul_comm (-I : 𝕜) 4⁻¹]
  simp only [mul_assoc]
  congr 1
  rw [smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, neg_sub_left, norm_neg]
  simp only [mul_add, mul_sub]
  simp_rw [← mul_assoc, hI', one_mul, neg_mul]
  rw [sub_neg_eq_add]
  have : ‖x - y‖ = ‖-x + y‖ := by rw [← norm_neg, neg_sub', sub_eq_add_neg, neg_neg]
  rw [this, add_comm x y]
  ring_nf

theorem im_innerDef_aux (x y : X) : im (innerDef x y : 𝕜) = re (innerDef ((I : 𝕜) • x) y : 𝕜) := by
  rw [im_eq_re_neg_i, ← innerDef_i_smul_left]

theorem re_innerDef_symm (x y : X) : re (innerDef x y : 𝕜) = re (innerDef y x : 𝕜) :=
  by
  simp_rw [re_innerDef]
  rw [add_comm]
  congr 2
  simp only [sq_eq_sq, norm_nonneg, norm_sub_rev]

theorem im_innerDef_symm (x y : X) : im (innerDef x y : 𝕜) = -im (innerDef y x : 𝕜) :=
  by
  simp_rw [im_innerDef_aux]
  rw [re_innerDef_symm]
  by_cases h : (I : 𝕜) = 0
  · simp only [re_innerDef, h, zero_smul, zero_add, add_zero, zero_sub, sub_zero, sub_self,
      norm_neg, MulZeroClass.mul_zero, neg_zero]
  · have := norm_I_of_ne_zero h
    simp only [re_innerDef, ← neg_mul, neg_mul_comm]
    congr 1
    simp only [neg_sub]
    have h₁ : ∀ a : X, ‖a‖ = ‖(I : 𝕜) • a‖ := fun a => by
      rw [norm_smul, norm_I_of_ne_zero h, one_mul]
    rw [h₁ (y + (I : 𝕜) • x), h₁ (y - (I : 𝕜) • x)]
    simp only [smul_add, smul_sub, smul_smul, I_mul_I_of_nonzero h, neg_one_smul]
    simp_rw [sub_eq_add_neg, neg_neg]

theorem innerDef_conj (x y : X) : conj (innerDef x y : 𝕜) = innerDef y x :=
  by
  rw [← @re_add_im 𝕜 _ (innerDef x y)]
  simp_rw [map_add, map_mul, conj_ofReal, conj_I]
  calc
    ↑(re (innerDef x y : 𝕜)) + ↑(im (innerDef x y : 𝕜)) * -(I : 𝕜) =
        ↑(re (innerDef y x : 𝕜)) + ↑(-im (innerDef x y : 𝕜)) * (I : 𝕜) :=
      by
      rw [re_innerDef_symm]
      congr 1
      simp
    _ = ↑(re (innerDef y x : 𝕜)) + ↑(im (innerDef y x : 𝕜)) * (I : 𝕜) := by
      rw [← im_innerDef_symm]
    _ = innerDef y x := re_add_im _

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
    ⟨fun h => ⟨IsBoundedLinearMap.toIsLinearMap h, IsBoundedLinearMap.continuous h⟩, fun h => _⟩
  let f' : E →L[𝕜] F := ⟨h.1.mk' f, h.2⟩
  exact f'.isBoundedLinearMap

private theorem linear_map.is_bounded_linear_map_iff_is_continuous {𝕜 E : Type _}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →ₗ[𝕜] F) :
    IsBoundedLinearMap 𝕜 f ↔ Continuous f :=
  by
  rw [isBoundedLinearMap_iff_isContinuousLinearMap, IsContinuousLinearMap]
  simp only [and_iff_right_iff_imp, f.isLinear, imp_true_iff]

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
  simp only [IsBoundedLinearMap.def, IsContinuousLinearMap, and_congr_right_iff, f.isLinear,
    true_imp_iff] at this
  exact this

theorem LinearMap.ker_coe_def {R E F : Type _} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R E] [Module R F] {f : E →ₗ[R] F} : (ker f : Set E) = {x : E | f x = 0} :=
  rfl

theorem exists_dual_vector_of_ne {X : Type _} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {x y : X}
    (h : x ≠ y) : ∃ f : NormedSpace.Dual 𝕜 X, f x ≠ f y :=
  by
  rw [Ne.def, ← sub_eq_zero] at h
  obtain ⟨f, ⟨_, hxy⟩⟩ := @exists_dual_vector 𝕜 _ X _ _ _ h
  rw [map_sub] at hxy
  use f
  intro H
  rw [H, sub_self, eq_comm, RCLike.ofReal_eq_zero, norm_eq_zero] at hxy
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
  exact ⟨f'.isLinear, LinearMap.IsSymmetric.continuous h⟩

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
    ext x
    simp only [LinearMap.add_apply]
    exact hf.add_left y z x
  map_smul' r z := by
    ext x
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
    ext x
    simp only [ContinuousLinearMap.add_apply]
    exact (hf₁ x).map_add _ _
  map_smul' r z := by
    ext x
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

example
    --is_continuous_bilinear_map_norm_of_clm
    {𝕜 X Y Z : Type _}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z] [CompleteSpace X] [CompleteSpace Y]
    [CompleteSpace Z] (β : X →L[𝕜] Y →L[𝕜] Z) : ∃ M : ℝ, ∀ x y, ‖β x y‖ ≤ M * ‖x‖ * ‖y‖ :=
  by
  use ‖β‖
  intro x y
  apply ContinuousLinearMap.le_of_opNorm_le
  exact ContinuousLinearMap.le_opNorm _ _

open scoped ComplexOrder
open RCLike
lemma Metric.mem_extremePoints_of_closedUnitBall_iff
  {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H] (x : H) :
  x ∈ Set.extremePoints 𝕜 (closedBall 0 1) ↔
  (‖x‖ ≤ 1 ∧
    ∀ (x₁ : H), ‖x₁‖ ≤ 1 → ∀ (x₂ : H), ‖x₂‖ ≤ 1 →
      (∃ a : 𝕜, 0 < a ∧ a < 1 ∧ a • x₁ + (1 - a) • x₂ = x) → x₁ = x ∧ x₂ = x) := by
{ simp only [mem_extremePoints, mem_closedBall, openSegment, Set.mem_setOf]
  simp only [exists_and_left, forall_exists_index, and_imp, dist_zero_right, and_congr_right_iff]
  intro h
  constructor
  { rintro h2 y hy z hz r hr hrr rfl
    exact h2 y hy z hz r hr (1 - r) (sub_pos.mpr hrr) (add_sub_cancel _ _) rfl }
  { rintro h2 y hy z hz r hr s hs hrs rfl
    have hs' := calc 0 < s ↔ 0 < 1 - r := by rw [← hrs, add_sub_cancel_left]
      _ ↔ r < 1 := by rw [sub_pos]
    apply h2 y hy z hz r hr (hs'.mp hs)
    simp only [add_right_inj, ← hrs, add_sub_cancel_left] } }
lemma Metric.mem_extremePoints_of_unitBall_iff
  {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H] (x : H) :
  x ∈ Set.extremePoints 𝕜 (ball 0 1) ↔
  (‖x‖ < 1 ∧
    ∀ (x₁ : H), ‖x₁‖ < 1 → ∀ (x₂ : H), ‖x₂‖ < 1 →
      (∃ a : 𝕜, 0 < a ∧ a < 1 ∧ a • x₁ + (1 - a) • x₂ = x) → x₁ = x ∧ x₂ = x) := by
{ simp only [mem_extremePoints, mem_ball, openSegment, Set.mem_setOf]
  simp only [exists_and_left, forall_exists_index, and_imp, dist_zero_right, and_congr_right_iff]
  intro h
  constructor
  { rintro h2 y hy z hz r hr hrr rfl
    exact h2 y hy z hz r hr (1 - r) (sub_pos.mpr hrr) (add_sub_cancel _ _) rfl }
  { rintro h2 y hy z hz r hr s hs hrs rfl
    have hs' := calc 0 < s ↔ 0 < 1 - r := by rw [← hrs, add_sub_cancel_left]
      _ ↔ r < 1 := by rw [sub_pos]
    apply h2 y hy z hz r hr (hs'.mp hs)
    simp only [add_right_inj, ← hrs, add_sub_cancel_left] } }

lemma Metric.exists_mem_closedUnitBall_of_norm_one (𝕜 H : Type _) [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [Nontrivial H] :
  ∃ x : H, ‖x‖ = 1 ∧ x ∈ closedBall (0 : H) 1 := by
obtain ⟨x, hx⟩ : ∃ x : H, x ≠ 0 := exists_ne 0
use (1 / ‖x‖ : 𝕜) • x
simp only [one_div, mem_closedBall, dist_zero_right, norm_smul, norm_inv]
simp only [norm_ofReal, abs_norm]
rw [inv_mul_cancel (norm_ne_zero_iff.mpr hx)]
exact ⟨rfl, le_rfl⟩

lemma Metric.exists_mem_unitBall_of_norm_one (𝕜 H : Type _) [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [Nontrivial H] :
  ∃ (x : H) (ε : ℝ), ‖x‖ = ε ∧ 0 < ε ∧ ε < 1 ∧ x ∈ ball (0 : H) 1 := by
obtain ⟨x, hx⟩ : ∃ x : H, x ≠ 0 := exists_ne 0
obtain ⟨ε, hε⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 := ⟨1 / 2, by norm_num⟩
use ((ε / ‖x‖ : ℝ) : 𝕜) • x, ε
simp only [div_eq_inv_mul, mem_ball, dist_zero_right, norm_smul, norm_inv]
simp only [norm_ofReal, abs_norm, abs_mul, abs_inv, abs_of_pos hε.1]
rw [mul_comm, ← mul_assoc, mul_inv_cancel (norm_ne_zero_iff.mpr hx), one_mul]
exact ⟨rfl, hε.1, hε.2, hε.2⟩

theorem inner_lt_one_iff_of_norm_one {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
  ⟪x, y⟫_𝕜 < 1 ↔ x ≠ y ∧ (re ⟪x, y⟫_𝕜 : 𝕜) = ⟪x, y⟫_𝕜 :=
by
  simp_rw [lt_iff_le_and_ne, ne_eq, inner_eq_one_iff_of_norm_one hx hy]
  -- rw [← @inner_eq_one_iff_of_norm_one 𝕜 _ _ _ _ _ _ hx hy]
  refine ⟨λ ⟨h1, h2⟩ => ⟨h2, ?_⟩, λ h => ⟨?_, h.1⟩⟩
  rw [@le_def 𝕜, one_re, one_im, ← conj_eq_iff_im, conj_eq_iff_re] at h1
  exact h1.2
  rw [← h.2, ← @RCLike.ofReal_one 𝕜, real_le_real]
  calc re ⟪x, y⟫_𝕜 ≤ ‖x‖ * ‖y‖ := re_inner_le_norm _ _
    _ = 1 := by rw [hx, hy, mul_one]

theorem re_inner_lt_one_iff_of_norm_one {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
  re ⟪x, y⟫_𝕜 < 1 ↔ x ≠ y :=
by
  rw [← real_inner_eq_re_inner]
  exact @inner_lt_one_iff_real_of_norm_one H _ (InnerProductSpace.rclikeToReal 𝕜 H) _ _ hx hy

theorem mem_extremePoints_of_closedBall_iff_norm_eq_one
  {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Nontrivial H] (x : H) :
  x ∈ Set.extremePoints 𝕜 (Metric.closedBall (0 : H) 1) ↔ ‖x‖ = 1 := by
  simp_rw [Metric.mem_extremePoints_of_closedUnitBall_iff]
  constructor
  .
    rintro ⟨h1, h⟩
    by_cases hx : x = 0
    . simp_rw [hx] at h1 h ⊢
      obtain ⟨y, hy, h₂⟩ := Metric.exists_mem_closedUnitBall_of_norm_one 𝕜 H
      simp_rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h₂
      specialize h y h₂ (- y) (by rw [norm_neg]; exact h₂)
        (⟨(1/2 : ℝ), by simp_rw [RCLike.zero_lt_real, one_half_pos],
          by simp_rw [← @RCLike.ofReal_one 𝕜, RCLike.real_lt_real]; norm_num,
          by simp only [one_div, ofReal_inv, ofReal_ofNat, smul_neg, sub_smul, neg_sub,
            ← add_sub_assoc, ← add_smul]; norm_num⟩)
      rw [h.1] at hy
      exact hy
    by_cases hx' : ‖x‖ ≠ 1
    . specialize h ((1 / ‖x‖ : 𝕜) • x)
        (by simp_rw [norm_smul, one_div, norm_inv, norm_ofReal, abs_norm, inv_mul_cancel (norm_ne_zero_iff.mpr hx), le_rfl])
        0 (by simp_rw [norm_zero, zero_le_one])
        (⟨‖x‖, by simp_rw [RCLike.zero_lt_real]; exact norm_pos_iff.mpr hx,
          by simp_rw [← @RCLike.ofReal_one 𝕜, real_lt_real, lt_iff_le_and_ne]; exact ⟨h1, hx'⟩,
          by simp only [one_div, smul_zero, add_zero, smul_smul, ← ofReal_inv, ← ofReal_mul,
            mul_inv_cancel (norm_ne_zero_iff.mpr hx), ofReal_one, one_smul]⟩)
      exfalso
      exact hx h.2.symm
    rw [not_ne_iff] at hx'
    exact hx'
  . rintro hx
    refine ⟨by simp_rw [hx, le_rfl], λ y hy z hz ⟨α, hα₁, hα₂, hαx⟩ => ?_⟩
    let β : ℝ := re α
    have : (β : 𝕜) = α :=
    by
      simp_rw [@lt_def 𝕜, map_zero] at hα₁
      rw [← re_add_im α, ← hα₁.2, ofReal_zero, zero_mul, add_zero]
    simp_rw [← this, ← @ofReal_zero 𝕜, ← @ofReal_one 𝕜, real_lt_real, ← ofReal_sub] at hα₁ hα₂ hαx
    have :=
      calc 1 = ‖x‖ ^ 2 := by rw [hx, one_pow]
          _ = ‖(β : 𝕜) • y + ((1 - β : ℝ) : 𝕜) • z‖ ^ 2 := by rw [hαx]
          _ = (‖(β : 𝕜) • y‖ ^ 2 + 2 * re (⟪(β : 𝕜) • y, ((1 - β : ℝ) : 𝕜) • z⟫_𝕜)
                + ‖((1 - β : ℝ) : 𝕜) • z‖ ^ 2 : ℝ) := by rw [← norm_add_pow_two]
          _ = β ^ 2 * ‖y‖ ^ 2 + (2 * β * (1 - β)) * re (⟪y, z⟫_𝕜) + (1 - β) ^ 2 * ‖z‖ ^ 2 :=
            by
              simp_rw [norm_smul, inner_smul_left, inner_smul_right, conj_ofReal,
                ← mul_assoc, ← ofReal_mul, re_ofReal_mul, mul_pow, ← norm_pow, ← ofReal_pow]
              simp only [norm_ofReal, abs_sq]
              simp only [mul_assoc]
    by_cases hyz : y = z
    . rw [hyz, ← add_smul, ← ofReal_add, add_sub_cancel, ofReal_one, one_smul] at hαx
      rw [hyz, and_self, hαx]
    . by_cases hyzyz : ‖y‖ = 1 ∧ ‖z‖ = 1
      . simp_rw [hyzyz, one_pow, mul_one] at this
        have this' : re ⟪y, z⟫_𝕜 < 1 := (re_inner_lt_one_iff_of_norm_one hyzyz.1 hyzyz.2).mpr hyz
        have := calc 1 = β ^ 2 + 2 * β * (1 - β) * re ⟪y, z⟫_𝕜 + (1 - β) ^ 2 := this
          _ < β ^ 2 + 2 * β * (1 - β) * 1 + (1 - β) ^ 2 := by
            simp only [add_lt_add_iff_right, add_lt_add_iff_left]
            apply mul_lt_mul_of_pos_left this'
            apply mul_pos (mul_pos two_pos hα₁)
            simp only [sub_pos, hα₂]
          _ = 1 := by ring_nf
        simp only [lt_irrefl] at this
      . rw [not_and_or] at hyzyz
        rcases hyzyz with (Hy | Hy)
        on_goal 1 => have Hyy : ‖y‖ < 1 := lt_of_le_of_ne hy Hy
        on_goal 2 => have Hyy : ‖z‖ < 1 := lt_of_le_of_ne hz Hy
        all_goals
          have :=
            calc 1 = ‖x‖ := hx.symm
              _ = ‖(β : 𝕜) • y + ((1 - β : ℝ) : 𝕜) • z‖ := by rw [hαx]
              _ ≤ ‖(β : 𝕜) • y‖ + ‖((1 - β : ℝ) : 𝕜) • z‖ := norm_add_le _ _
              _ ≤ β * ‖y‖ + (1 - β) * ‖z‖ :=
                by
                  simp_rw [norm_smul, norm_ofReal, abs_of_pos hα₁]
                  rw [abs_of_pos]; simp_rw [sub_pos, hα₂]
              _ < β * 1 + (1 - β) * 1 :=
                by
                  try
                  { apply add_lt_add_of_lt_of_le
                    apply mul_lt_mul' le_rfl Hyy (norm_nonneg _) hα₁
                    apply mul_le_mul_of_nonneg_left hz
                    simp_rw [sub_nonneg, le_of_lt hα₂] }
                  try
                  { apply add_lt_add_of_le_of_lt
                    exact mul_le_mul le_rfl hy (norm_nonneg y) (le_of_lt hα₁)
                    apply mul_lt_mul' le_rfl Hyy (norm_nonneg _)
                    simp only [sub_pos, hα₂] }
              _ = 1 := by ring_nf
          simp only [lt_irrefl] at this
