/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Monlib.LinearAlgebra.Ips.Basic
import Monlib.LinearAlgebra.IsProj'

#align_import linear_algebra.my_ips.rank_one

/-!

# rank one operators

This defines the rank one operator $| x \rangle\langle y |$ for continuous linear maps
  (see `rank_one`) and linear maps (see `rank_one_lm`).

-/


section rankOne

/-- we define the rank one operator $| x \rangle\langle y |$ by
  $x \mapsto \langle y,z\rangle x$ -/
@[simps]
def rankOne (𝕜 : Type*) {E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] :
    E₁ →ₗ[𝕜] (E₂ →ₗ⋆[𝕜] (E₂ →L[𝕜] E₁)) where
  toFun x :=
  { toFun := λ y =>
    { toFun := λ z => ⟪y,z⟫_𝕜 • x
      map_add' := λ _ _ => by simp_rw [inner_add_right, add_smul]
      map_smul' := λ _ _ => by simp_rw [inner_smul_right, RingHom.id_apply, smul_smul]
      cont := Continuous.smul (Continuous.inner continuous_const continuous_id') (continuous_const) }
    map_add' := λ a b => by simp only [inner_add_left, add_smul]; rfl
    map_smul' := λ r x => by simp only [inner_smul_left, RingHom.id_apply, ← smul_smul]; rfl }
  map_add' a b := by simp only [smul_add]; rfl
  map_smul' r a := by
    simp only [smul_smul, RingHom.id_apply, mul_comm _ r]
    simp only [← smul_smul]; rfl

variable {𝕜 E₁ E₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]

@[simp]
theorem rankOne_apply {x : E₁} {y : E₂} (z : E₂) : rankOne 𝕜 x y z = ⟪y,z⟫_𝕜 • x :=
rfl

open ContinuousLinearMap

@[simp]
theorem rankOne.smul_real_apply {x : E₁} {y : E₂} {α : ℝ} :
    rankOne 𝕜 x ((α : 𝕜) • y) = (α : 𝕜) • rankOne 𝕜 x y := by
  simp only [LinearMap.map_smulₛₗ, RCLike.conj_ofReal]

/--
$| x \rangle\langle y | | z \rangle\langle w | = \langle y, z \rangle \cdot  | x \rangle\langle w |$ -/
@[simp]
theorem rankOne.apply_rankOne {E₃ : Type*} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  (x : E₁) (y z : E₂) (w : E₃) :
    (rankOne 𝕜 x y) ∘L rankOne 𝕜 z w = ⟪y,z⟫_𝕜 • rankOne 𝕜 x w :=
  by
  ext r
  simp_rw [ContinuousLinearMap.smul_apply, comp_apply, rankOne_apply,
    inner_smul_right, mul_comm, smul_smul]

/-- $u \circ | x \rangle\langle y | = | u(x) \rangle\langle y |$ -/
theorem ContinuousLinearMap.comp_rankOne {E₃ : Type*} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  (x : E₁) (y : E₂) (u : E₁ →L[𝕜] E₃) :
    u ∘L rankOne 𝕜 x y = rankOne 𝕜 (u x) y :=
  by
  ext r
  simp_rw [comp_apply, rankOne_apply, map_smul]

/-- $| x \rangle\langle y | \circ u  = | x \rangle\langle u^*(y) |$ -/
theorem ContinuousLinearMap.rankOne_comp {E₃ : Type*} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  [CompleteSpace E₂] [CompleteSpace E₃] (x : E₁) (y : E₂) (u : E₃ →L[𝕜] E₂) :
    rankOne 𝕜 x y ∘L u = rankOne 𝕜 x (adjoint u y) :=
  by
  ext r
  simp_rw [comp_apply, rankOne_apply, adjoint_inner_left]

/-- rank one operators given by norm one vectors are automatically idempotent -/
@[simp]
theorem rankOne_self_isIdempotentElem_of_normOne {x : E₁} (h : ‖x‖ = 1) :
  IsIdempotentElem (rankOne 𝕜 x x) := by
simp_rw [IsIdempotentElem, ContinuousLinearMap.ext_iff, mul_def, rankOne.apply_rankOne,
  inner_self_eq_norm_sq_to_K, h, RCLike.ofReal_one, one_pow, one_smul,
  forall_const]

theorem rankOne_self_isSymmetric {x : E₁} :
  LinearMap.IsSymmetric ((rankOne 𝕜 x x) : E₁ →ₗ[𝕜] E₁) := by
simp_rw [LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
  inner_smul_right, inner_conj_symm, mul_comm, forall₂_true_iff]

/-- rank one operators are automatically self-adjoint -/
@[simp]
theorem rankOne_self_isSelfAdjoint [CompleteSpace E₁] {x : E₁} :
  IsSelfAdjoint (rankOne 𝕜 x x) :=
isSelfAdjoint_iff_isSymmetric.mpr rankOne_self_isSymmetric

/-- $| x \rangle\langle y |^* = | y \rangle\langle x |$ -/
theorem rankOne_adjoint [CompleteSpace E₁] [CompleteSpace E₂] (x : E₁) (y : E₂) :
  adjoint (rankOne 𝕜 x y) = rankOne 𝕜 y x :=
by
  ext a
  apply @ext_inner_right 𝕜
  intro b
  simp_rw [adjoint_inner_left, rankOne_apply, inner_smul_left, inner_smul_right, inner_conj_symm,
    mul_comm]

theorem rankOne_inner_left (x w : E₁) (y z : E₂) :
  ⟪rankOne 𝕜 x y z,w⟫_𝕜 = ⟪z,y⟫_𝕜 * ⟪x,w⟫_𝕜 := by
rw [rankOne_apply, inner_smul_left, inner_conj_symm]

theorem rankOne_inner_right (x y : E₁) (z w : E₂) :
  ⟪x, rankOne 𝕜 y z w⟫_𝕜 = ⟪z,w⟫_𝕜 * ⟪x,y⟫_𝕜 := by
rw [rankOne_apply, inner_smul_right]

theorem ContinuousLinearMap.commutes_with_all_iff [CompleteSpace E₁] {T : E₁ →L[𝕜] E₁} :
    (∀ S, Commute S T) ↔ ∃ α : 𝕜, T = α • 1 :=
  by
  constructor
  · intro h
    have h' : ∀ x y : E₁, rankOne 𝕜 x y ∘L T = T ∘L rankOne 𝕜 x y := fun x y => h _
    simp_rw [ContinuousLinearMap.rankOne_comp, ContinuousLinearMap.comp_rankOne] at h'
    have h'' : ∀ x y : E₁, rankOne 𝕜 (adjoint T y) x = rankOne 𝕜 y (T x) :=
      by
      intro x y
      nth_rw 1 [← rankOne_adjoint]
      rw [h', rankOne_adjoint]
    simp_rw [ext_iff, rankOne_apply] at h' h''
    by_cases H : ∀ x : E₁, x = 0
    · use 0
      simp_rw [ext_iff]
      intro x
      rw [H x, zero_smul, map_zero, zero_apply]
    push_neg at H
    obtain ⟨x, hx⟩ := H
    use (⟪x,x⟫_𝕜)⁻¹ * ⟪adjoint T x, x⟫_𝕜
    simp_rw [ext_iff, ContinuousLinearMap.smul_apply, one_apply, mul_smul, h', smul_smul]
    rw [inv_mul_cancel]
    simp_rw [one_smul, forall_true_iff]
    · rw [inner_self_ne_zero]
      exact hx
  · rintro ⟨α, hα⟩ S
    simp_rw [Commute, SemiconjBy, mul_def, hα, comp_smul, smul_comp, one_def, comp_id, id_comp]

theorem ContinuousLinearMap.centralizer [CompleteSpace E₁] :
    (@Set.univ (E₁ →L[𝕜] E₁)).centralizer = { x : E₁ →L[𝕜] E₁ | ∃ α : 𝕜, x = α • 1 } :=
  by
  simp_rw [Set.centralizer, Set.mem_univ, true_imp_iff, ← ContinuousLinearMap.commutes_with_all_iff]
  rfl

theorem ContinuousLinearMap.scalar_centralizer :
    {x : E₁ →L[𝕜] E₁ | ∃ α : 𝕜, x = α • 1}.centralizer = @Set.univ (E₁ →L[𝕜] E₁) :=
  by
  simp_rw [Set.centralizer, Set.ext_iff, Set.mem_setOf, Set.mem_univ, iff_true_iff]
  rintro x y ⟨α, rfl⟩
  simp only [Algebra.smul_mul_assoc, one_mul, Algebra.mul_smul_comm, mul_one]

theorem ContinuousLinearMap.centralizer_centralizer [CompleteSpace E₁] :
    (@Set.univ (E₁ →L[𝕜] E₁)).centralizer.centralizer = Set.univ := by
  rw [ContinuousLinearMap.centralizer, ContinuousLinearMap.scalar_centralizer]

theorem colinear_of_rankOne_self_eq_rankOne_self
  (x y : E₁) (h : rankOne 𝕜 x x = rankOne 𝕜 y y) :
      ∃ α : 𝕜ˣ, x = (α : 𝕜) • y :=
by
  have : x = 0 ↔ y = 0 :=
    by
    constructor <;> intro hh <;>
      simp only [hh, ContinuousLinearMap.ext_iff, map_zero, ContinuousLinearMap.zero_apply,
        @eq_comm _ (0 : E₁ →L[𝕜] E₁), rankOne_apply, smul_eq_zero] at h
    on_goal 1 => specialize h y
    on_goal 2 => specialize h x
    all_goals
      simp_rw [inner_self_eq_zero, or_self_iff] at h
      exact h
  simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply] at h
  by_cases Hx : x = 0
  · use 1
    simp_rw [Hx, Units.val_one, one_smul, eq_comm, ← this, Hx]
  · have ugh : inner y x ≠ (0 : 𝕜) := by
      intro hy
      specialize h x
      rw [hy, zero_smul, smul_eq_zero, inner_self_eq_zero, or_self_iff] at h
      contradiction
    use Units.mk0 (inner y x / inner x x)
        (div_ne_zero ugh ((@inner_self_ne_zero 𝕜 _ _ _ _ _).mpr Hx))
    simp_rw [div_eq_inv_mul, Units.val_mk0, mul_smul, ← h, smul_smul,
      inv_mul_cancel ((@inner_self_ne_zero 𝕜 _ _ _ _ _).mpr Hx), one_smul]

theorem ContinuousLinearMap.ext_inner_map {F : Type _} [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] (T S : E₁ →L[𝕜] F) :
      T = S ↔ ∀ x y, ⟪T x,y⟫_𝕜 = ⟪S x,y⟫_𝕜 :=
by
  simp only [ContinuousLinearMap.ext_iff]
  constructor
  · intro h x y
    rw [h]
  · intro h x
    apply @ext_inner_right 𝕜
    exact h x
theorem LinearMap.ext_inner_map {F : Type _} [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] (T S : E₁ →ₗ[𝕜] F) :
      T = S ↔ ∀ x y, ⟪T x,y⟫_𝕜 = ⟪S x,y⟫_𝕜 :=
by
  simp only [LinearMap.ext_iff]
  constructor
  · intro h x y
    rw [h]
  · intro h x
    apply @ext_inner_right 𝕜
    exact h x

open scoped BigOperators

theorem ContinuousLinearMap.exists_sum_rankOne
  [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] (T : E₁ →L[𝕜] E₂) :
    ∃ (x : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₂)
      (y : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₁),
      T = ∑ i, rankOne 𝕜 (x i) (y i) :=
  by
  letI := FiniteDimensional.complete 𝕜 E₁
  letI := FiniteDimensional.complete 𝕜 E₂
  let e₁ := stdOrthonormalBasis 𝕜 E₁
  let e₂ := stdOrthonormalBasis 𝕜 E₂
  let b : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₁ := fun ij =>
    e₁ ij.1
  let a : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₂ := fun ij =>
    e₂.repr (T (e₁ ij.1)) ij.2 • e₂ ij.2
  refine' ⟨a, b, _⟩
  simp only [a, b]
  simp only [ContinuousLinearMap.ext_inner_map, sum_apply, sum_inner, rankOne_inner_left,
    inner_smul_left, OrthonormalBasis.repr_apply_apply, inner_conj_symm]
  intro u v
  symm
  calc
    ∑ x : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂),
          ⟪u,e₁ x.fst⟫_𝕜 * (⟪T (e₁ x.fst),e₂ x.snd⟫_𝕜 * ⟪e₂ x.snd,v⟫_𝕜) =
        ∑ x_1, ∑ x_2,
          ⟪u,e₁ x_1⟫_𝕜 * (⟪T (e₁ x_1),e₂ x_2⟫_𝕜 * ⟪e₂ x_2,v⟫_𝕜) :=
      by simp_rw [← Finset.sum_product', Finset.univ_product_univ]
    _ = ∑ x_1, ⟪u,e₁ x_1⟫_𝕜 * ⟪T (e₁ x_1),v⟫_𝕜 := by
      simp_rw [← Finset.mul_sum, OrthonormalBasis.sum_inner_mul_inner]
    _ = ⟪T u,v⟫_𝕜 := by simp_rw [← adjoint_inner_right T, OrthonormalBasis.sum_inner_mul_inner]

example [FiniteDimensional 𝕜 E₁] (T : E₁ →L[𝕜] E₁) :
    ∃ x y : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₁) → E₁,
      T = ∑ i, rankOne 𝕜 (x i) (y i) :=
ContinuousLinearMap.exists_sum_rankOne T

theorem LinearMap.exists_sum_rankOne [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] (T : E₁ →ₗ[𝕜] E₂) :
    ∃ (x : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₂)
      (y : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₁),
      T = ∑ i, ↑(rankOne 𝕜 (x i) (y i)) :=
by
  obtain ⟨a, b, h⟩ := ContinuousLinearMap.exists_sum_rankOne (toContinuousLinearMap T)
  refine' ⟨a, b, _⟩
  simp_rw [← coe_sum, ← h]
  rfl

theorem rankOne.sum_orthonormalBasis_eq_id {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type _} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, rankOne 𝕜 (b i) (b i) = 1 :=
by
  rw [ContinuousLinearMap.ext_iff]
  intros
  apply @ext_inner_left 𝕜 _
  intro v
  simp_rw [ContinuousLinearMap.sum_apply, rankOne_apply, ← OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.sum_repr, ContinuousLinearMap.one_apply]

end rankOne

section rankOneLm


-- /-- same as `rank_one`, but as a linear map -/
-- @[reducible, simps!]
-- abbrev rankOneLm {𝕜 E₁ E₂ : Type*}
--   (x : E₁) (y : E₂) : E₂ →ₗ[𝕜] E₁ :=
--   (rankOne 𝕜 x y).toLinearMap

variable {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- theorem rankOneLm_comp_rankOneLm (x : E₁) (y z : E₂) (w : E) :
--     (rankOne x y) ∘ₗ rankOneLm z w = ⟪y,z⟫_𝕜 • rankOneLm x w := by
--   simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, rankOneLm_apply, LinearMap.smul_apply,
--     inner_smul_right, mul_smul, rankOneLm_apply, smul_smul, mul_comm,
--     forall_true_iff]

-- theorem rankOneLm_apply_rank_one (x : E₁) (y z : E₂) (w v : E) :
--     (rankOneLm x y : _ →ₗ[𝕜] _) ((rankOneLm z w : _ →ₗ[𝕜] _) v) = (⟪y,z⟫_𝕜 * ⟪w,v⟫_𝕜) • x := by
--   rw [← LinearMap.comp_apply, rankOneLm_comp_rankOneLm, LinearMap.smul_apply, rankOneLm_apply,
--     smul_smul]

-- theorem rankOneLm_adjoint [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] (x : E₁) (y : E₂) :
--     LinearMap.adjoint (rankOneLm x y : _ →ₗ[𝕜] _) = rankOneLm y x :=
--   by
--   simp_rw [rankOneLm, LinearMap.adjoint_eq_toCLM_adjoint,
--     ContinuousLinearMap.coe_inj, ← @rankOne.adjoint 𝕜 _ _ _ _ _ _ _
--       (FiniteDimensional.complete 𝕜 E₁) (FiniteDimensional.complete 𝕜 E₂) x y]
--   rfl

open scoped BigOperators


theorem ContinuousLinearMap.ext_of_rankOne {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜]
    [NormedAddCommGroup H'] [Module 𝕜 H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →L[𝕜] H₂) →L[𝕜] H'}
    (h : ∀ a b, x (rankOne 𝕜 a b) = y (rankOne 𝕜 a b)) : x = y :=
by
  ext a
  obtain ⟨α, β, rfl⟩ := ContinuousLinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]

theorem LinearMap.ext_of_rankOne {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜] [AddCommMonoid H'] [Module 𝕜 H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →L[𝕜] H₂) →ₗ[𝕜] H'}
    (h : ∀ a b, x (rankOne 𝕜 a b) = y (rankOne 𝕜 a b)) : x = y :=
by
  ext a
  obtain ⟨α, β, rfl⟩ := ContinuousLinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]

theorem LinearMap.ext_of_rank_one' {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜] [AddCommMonoid H'] [Module 𝕜 H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →ₗ[𝕜] H₂) →ₗ[𝕜] H'}
    (h : ∀ a b, x (rankOne 𝕜 a b).toLinearMap = y (rankOne 𝕜 a b).toLinearMap) : x = y :=
by
  ext a
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]

open scoped BigOperators

theorem rankOne.sum_orthonormalBasis_eq_id_lm {𝕜 : Type _} {E : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type _} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, (rankOne 𝕜 (b i) (b i) : E →L[𝕜] E).toLinearMap = 1 :=
by
  simp only [← ContinuousLinearMap.coe_sum, rankOne.sum_orthonormalBasis_eq_id b]
  rfl

theorem ContinuousLinearMap.coe_eq_zero {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂] (f : E₁ →L[𝕜] E₂) :
    (f : E₁ →ₗ[𝕜] E₂) = 0 ↔ f = 0 := by norm_cast

theorem rankOne.eq_zero_iff {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) :
    rankOne 𝕜 x y = 0 ↔ x = 0 ∨ y = 0 := by
  simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply, ContinuousLinearMap.zero_apply, smul_eq_zero,
    forall_or_right, forall_inner_eq_zero_iff, or_comm]

theorem LinearMap.rankOne_comp {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
  [InnerProductSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₂] [FiniteDimensional 𝕜 E₃] (x : E₁) (y : E₂) (u : E₃ →ₗ[𝕜] E₂) :
    (rankOne 𝕜 x y).toLinearMap ∘ₗ u = (rankOne 𝕜 x (adjoint u y)) :=
by
  ext
  simp_rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    LinearMap.adjoint_inner_left]

theorem LinearMap.rankOne_comp'  {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
  [InnerProductSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₂] [FiniteDimensional 𝕜 E₃] (x : E₁) (y : E₂) (u : E₂ →ₗ[𝕜] E₃) :
    (rankOne 𝕜 x y).toLinearMap ∘ₗ adjoint u = (rankOne 𝕜 x (u y)) :=
by rw [LinearMap.rankOne_comp, LinearMap.adjoint_adjoint]

theorem OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne {ι 𝕜 : Type _} [RCLike 𝕜] {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] {U : Submodule 𝕜 E}
    [CompleteSpace U] (b : OrthonormalBasis ι 𝕜 ↥U) :
    orthogonalProjection' U = ∑ i : ι, rankOne 𝕜 (b i : E) (b i : E) :=
by
  ext
  simp_rw [orthogonalProjection'_apply, b.orthogonalProjection_eq_sum,
    ContinuousLinearMap.sum_apply, rankOne_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]

theorem LinearMap.comp_rankOne  {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
  [InnerProductSpace 𝕜 E₃] (x : E₁) (y : E₂) (u : E₁ →ₗ[𝕜] E₃) :
    u ∘ₗ (rankOne 𝕜 x y).toLinearMap = rankOne 𝕜 (u x) y :=
by
  ext
  simp_rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply, _root_.map_smul]


theorem _root_.rankOne_smul_smul {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) (r₁ r₂ : 𝕜) :
    rankOne 𝕜 (r₁ • x) (star r₂ • y) = (r₁ * r₂) • rankOne 𝕜 x y := by
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_smul, starRingEnd_apply, star_star, mul_comm,
    RingHom.id_apply]

theorem _root_.rankOne_lm_smul_smul {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) (r₁ r₂ : 𝕜) :
    (rankOne 𝕜 (r₁ • x) (star r₂ • y)).toLinearMap =
      (r₁ * r₂) • ((rankOne 𝕜 x y : _ →L[𝕜] _).toLinearMap) :=
  by rw [rankOne_smul_smul, ContinuousLinearMap.coe_smul]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem _root_.rankOne_lm_sum_sum {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    {ι₁ ι₂ : Type _} {k : Finset ι₁} {k₂ : Finset ι₂} (f : ι₁ → E₁) (g : ι₂ → E₂) :
    (rankOne 𝕜 (∑ i in k, f i) (∑ i in k₂, g i)).toLinearMap =
      ∑ i in k, ∑ j in k₂, (rankOne 𝕜 (f i) (g j)).toLinearMap :=
by
  simp_rw [map_sum, LinearMap.sum_apply, ContinuousLinearMap.coe_sum]
  rw [Finset.sum_comm]

theorem ContinuousLinearMap.linearMap_adjoint {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] (x : B →L[𝕜] C) :
    LinearMap.adjoint (x : B →ₗ[𝕜] C) =
      @ContinuousLinearMap.adjoint 𝕜 _ _ _ _ _ _ _ (FiniteDimensional.complete 𝕜 B)
        (FiniteDimensional.complete 𝕜 C) x :=
  rfl

set_option synthInstance.checkSynthOrder false in
scoped[FiniteDimensional] attribute [instance] FiniteDimensional.complete
open scoped FiniteDimensional
theorem LinearMap.toContinuousLinearMap_adjoint {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] {x : B →ₗ[𝕜] C} :
  ContinuousLinearMap.adjoint (toContinuousLinearMap x) =
    toContinuousLinearMap (LinearMap.adjoint x) :=
rfl
theorem LinearMap.toContinuousLinearMap_adjoint' {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] {x : B →ₗ[𝕜] C} :
  ContinuousLinearMap.toLinearMap (ContinuousLinearMap.adjoint (toContinuousLinearMap x)) =
    LinearMap.adjoint x :=
rfl
