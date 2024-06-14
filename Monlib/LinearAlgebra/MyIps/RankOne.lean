/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Monlib.LinearAlgebra.MyIps.Basic
import Monlib.LinearAlgebra.IsProj'

#align_import linear_algebra.my_ips.rank_one

/-!

# rank one operators

This defines the rank one operator $| x \rangle\!\langle y |$ for continuous linear maps
  (see `rank_one`) and linear maps (see `rank_one_lm`).

-/


section rankOne

variable {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]

-- local notation "L(" x ")" => x →L[ℂ] x

local notation "⟪" x "," y "⟫_𝕜" => @inner 𝕜 _ _ x y

/-- we define the rank one operator $| x \rangle\!\langle y |$ by
  $x \mapsto \langle y,  z \rangle \cdot  x$ -/
def rankOne : E₁ →ₗ[𝕜] (E₂ →+ (E₂ →L[𝕜] E₁)) where
  toFun x :=
  { toFun := λ y =>
    { toFun := λ z => ⟪y,z⟫_𝕜 • x
      map_add' := λ _ _ => by simp_rw [inner_add_right, add_smul]
      map_smul' := λ _ _ => by simp_rw [inner_smul_right, RingHom.id_apply, smul_smul]
      cont := Continuous.smul (Continuous.inner continuous_const continuous_id') (continuous_const) }
    map_add' := λ a b => by simp only [inner_add_left, add_smul]; rfl
    map_zero' := by simp only [inner_zero_left, zero_smul]; rfl }
  map_add' a b := by simp only [smul_add]; rfl
  map_smul' r a := by
    simp only [smul_smul, RingHom.id_apply, mul_comm _ r]
    simp only [← smul_smul]; rfl

-- local notation "|" x "⟩⟨" y "|" => rankOne x y

@[simp]
theorem rankOne_apply {x : E₁} {y : E₂} (z : E₂) : (rankOne x y : E₂ →L[𝕜] E₁) z = ⟪y,z⟫_𝕜 • x :=
  rfl

open ContinuousLinearMap

/-- $| x \rangle\!\langle \alpha\cdot y | = \bar{\alpha} \cdot | x \rangle\!\langle y |$ -/
@[simp]
theorem rankOne.smul_apply {x : E₁} {y : E₂} {α : 𝕜} :
    rankOne x (α • y) = (starRingEnd 𝕜) α • (rankOne x y : E₂ →L[𝕜] E₁) :=
  by
  ext
  simp_rw [ContinuousLinearMap.smul_apply, rankOne_apply, inner_smul_left, smul_smul]

/-- $| \alpha \cdot x \rangle\!\langle y | = \alpha \cdot | x \rangle\!\langle y |$ -/
@[simp]
theorem rankOne.apply_smul {x : E₁} {y : E₂} {α : 𝕜} : rankOne (α • x) y = α • (rankOne x y : E₂ →L[𝕜] E₁) :=
  by
  simp only [LinearMapClass.map_smul, AddMonoidHom.coe_smul, Pi.smul_apply]

@[simp]
theorem rankOne.smul_real_apply {x : E₁} {y : E₂} {α : ℝ} :
    rankOne x ((α : 𝕜) • y) = (α : 𝕜) • (rankOne x y : E₂ →L[𝕜] E₁) := by
  simp_rw [rankOne.smul_apply, RCLike.conj_ofReal]

/--
$| x \rangle\!\langle y | | z \rangle\!\langle w | = \langle y, z \rangle \cdot  | x \rangle\!\langle w |$ -/
@[simp]
theorem rankOne.apply_rankOne {E₃ : Type*} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  (x : E₁) (y z : E₂) (w : E₃) :
    (rankOne x y : E₂ →L[𝕜] E₁) ∘L (rankOne z w : _) = ⟪y,z⟫_𝕜 • (rankOne x w : _) :=
  by
  ext r
  simp_rw [ContinuousLinearMap.smul_apply, comp_apply, rankOne_apply, inner_smul_right, mul_comm, smul_smul]

/-- $u \circ | x \rangle\!\langle y | = | u(x) \rangle\!\langle y |$ -/
theorem ContinuousLinearMap.comp_rankOne {E₃ : Type*} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  (x : E₁) (y : E₂) (u : E₁ →L[𝕜] E₃) : u ∘L rankOne x y = rankOne (u x) y :=
  by
  ext r
  simp_rw [comp_apply, rankOne_apply, map_smul]

/-- $| x \rangle\!\langle y | \circ u  = | x \rangle\!\langle u^*(y) |$ -/
theorem ContinuousLinearMap.rankOne_comp {E₃ : Type*} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  [CompleteSpace E₂] [CompleteSpace E₃] (x : E₁) (y : E₂) (u : E₃ →L[𝕜] E₂) :
    rankOne x y ∘L (u : E₃ →L[𝕜] E₂) = rankOne x (adjoint u y) :=
  by
  ext r
  simp_rw [comp_apply, rankOne_apply, adjoint_inner_left]

/-- rank one operators given by norm one vectors are automatically idempotent -/
@[simp]
theorem rankOne.isIdempotentElem (x : E₁) (h : ‖x‖ = 1) : IsIdempotentElem (rankOne x x : E₁ →L[𝕜] E₁) := by
  simp_rw [IsIdempotentElem, ContinuousLinearMap.ext_iff, mul_def, rankOne.apply_rankOne,
    inner_self_eq_norm_sq_to_K, h, RCLike.ofReal_one, one_pow, one_smul,
    forall_const]

theorem rankOne.isSymmetric (x : E₁) : LinearMap.IsSymmetric ((rankOne x x : E₁ →L[𝕜] E₁) : E₁ →ₗ[𝕜] E₁) := by
  simp_rw [LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
    inner_smul_right, inner_conj_symm, mul_comm, forall₂_true_iff]

/-- rank one operators are automatically self-adjoint -/
@[simp]
theorem rankOne.isSelfAdjoint [CompleteSpace E₁] (x : E₁) : IsSelfAdjoint (rankOne x x : E₁ →L[𝕜] E₁) :=
  isSelfAdjoint_iff_isSymmetric.mpr (rankOne.isSymmetric x)

/-- $| x \rangle\!\langle y |^* = | y \rangle\!\langle x |$ -/
theorem rankOne.adjoint [CompleteSpace E₁] [CompleteSpace E₂] (x : E₁) (y : E₂) : adjoint (rankOne x y) = (rankOne y x : E₁ →L[𝕜] E₂) :=
  by
  ext a
  apply @ext_inner_right 𝕜
  intro b
  simp_rw [adjoint_inner_left, rankOne_apply, inner_smul_left, inner_smul_right, inner_conj_symm,
    mul_comm]

theorem rankOne_inner_left (x w : E₁) (y z : E₂) : ⟪(rankOne x y : E₂ →L[𝕜] E₁) z,w⟫_𝕜 = ⟪z,y⟫_𝕜 * ⟪x,w⟫_𝕜 := by
  rw [rankOne_apply, inner_smul_left, inner_conj_symm]

theorem rankOne_inner_right (x y : E₁) (z w : E₂) : ⟪x,(rankOne y z : _ →L[𝕜] _) w⟫_𝕜 = ⟪z,w⟫_𝕜 * ⟪x,y⟫_𝕜 := by
  rw [rankOne_apply, inner_smul_right]

theorem ContinuousLinearMap.commutes_with_all_iff [CompleteSpace E₁] (T : E₁ →L[𝕜] E₁) :
    (∀ S, Commute S T) ↔ ∃ α : 𝕜, T = α • 1 :=
  by
  constructor
  · intro h
    have h' : ∀ x y : E₁, rankOne x y ∘L T = T ∘L rankOne x y := fun x y => h _
    simp_rw [ContinuousLinearMap.rankOne_comp, ContinuousLinearMap.comp_rankOne] at h'
    have h'' : ∀ x y : E₁, (rankOne (adjoint T y) x : _ →L[𝕜] _) = rankOne y (T x) :=
      by
      intro x y
      nth_rw 1 [← rankOne.adjoint]
      rw [h', rankOne.adjoint]
    simp_rw [ext_iff, rankOne_apply] at h' h''
    by_cases H : ∀ x : E₁, x = 0
    · use 0
      simp_rw [ext_iff]
      intro x
      rw [H x, zero_smul, map_zero, zero_apply]
    push_neg at H
    obtain ⟨x, hx⟩ := H
    use⟪x,x⟫_𝕜⁻¹ * ⟪adjoint T x,x⟫_𝕜
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

theorem rankOne.zero_left
    (x : E₂) : (rankOne 0 x : E₂ →L[𝕜] E₁) = 0 := by
  ext1
  simp_rw [rankOne_apply, smul_zero, ContinuousLinearMap.zero_apply]

theorem rankOne.zero_right
    (x : E₁) : (rankOne x 0 : E₂ →L[𝕜] E₁) = 0 := by
  ext1
  simp_rw [rankOne_apply, inner_zero_left, zero_smul, ContinuousLinearMap.zero_apply]

theorem rankOne.ext_iff
    (x y : E₁) (h : (rankOne x x : E₁ →L[𝕜] E₁) = rankOne y y) : ∃ α : 𝕜ˣ, x = (α : 𝕜) • y :=
  by
  have : x = 0 ↔ y = 0 :=
    by
    constructor <;> intro hh <;>
      simp only [hh, ContinuousLinearMap.ext_iff, rankOne.zero_left, ContinuousLinearMap.zero_apply,
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
    [InnerProductSpace 𝕜 F] (T S : E₁ →L[𝕜] F) : T = S ↔ ∀ x y, ⟪T x,y⟫_𝕜 = ⟪S x,y⟫_𝕜 :=
  by
  simp only [ContinuousLinearMap.ext_iff]
  constructor
  · intro h x y
    rw [h]
  · intro h x
    apply @ext_inner_right 𝕜
    exact h x

open scoped BigOperators

local notation "|" x "⟩⟨" y "|" => rankOne x y

theorem ContinuousLinearMap.exists_sum_rankOne [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] (T : E₁ →L[𝕜] E₂) :
    ∃ (x : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₂)
      (y : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₁),
      T = ∑ i, |x i⟩⟨y i| :=
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

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_1 x_2) -/
example [FiniteDimensional 𝕜 E₁] (T : E₁ →L[𝕜] E₁) :
    ∃ x y : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₁) → E₁,
      T = ∑ i, |x i⟩⟨y i| :=
ContinuousLinearMap.exists_sum_rankOne T

theorem LinearMap.exists_sum_rankOne [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] (T : E₁ →ₗ[𝕜] E₂) :
    ∃ (x : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₂)
      (y : Fin (FiniteDimensional.finrank 𝕜 E₁) × Fin (FiniteDimensional.finrank 𝕜 E₂) → E₁),
      T = ∑ i, ↑(|x i⟩⟨y i| : _ →L[𝕜] _) :=
  by
  obtain ⟨a, b, h⟩ := ContinuousLinearMap.exists_sum_rankOne (toContinuousLinearMap T)
  refine' ⟨a, b, _⟩
  simp_rw [← coe_sum, ← h]
  rfl

theorem rankOne.sum_orthonormalBasis_eq_id {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type _} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, (rankOne (b i) (b i) : E →L[𝕜] E) = 1 :=
  by
  rw [ContinuousLinearMap.ext_iff]
  intros
  apply @ext_inner_left 𝕜 _
  intro v
  simp_rw [ContinuousLinearMap.sum_apply, rankOne_apply, ← OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.sum_repr, ContinuousLinearMap.one_apply]

end rankOne

section rankOneLm

variable {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x "," y "⟫_𝕜" => @inner 𝕜 _ _ x y

/-- same as `rank_one`, but as a linear map -/
@[reducible, simps!]
def rankOneLm (x : E₁) (y : E₂) : E₂ →ₗ[𝕜] E₁ :=
  (rankOne x y).toLinearMap

-- @[simp]
-- theorem rankOneLm_apply (x y z : E) : (rankOneLm x y : E →ₗ[𝕜] E) z = ⟪y,z⟫_𝕜 • x :=
--   rfl

theorem rankOneLm_comp_rankOneLm (x : E₁) (y z : E₂) (w : E) :
    (rankOneLm x y : _ →ₗ[𝕜] _) ∘ₗ rankOneLm z w = ⟪y,z⟫_𝕜 • rankOneLm x w := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, rankOneLm_apply, LinearMap.smul_apply,
    inner_smul_right, mul_smul, rankOneLm_apply, smul_smul, mul_comm,
    forall_true_iff]

theorem rankOneLm_apply_rank_one (x : E₁) (y z : E₂) (w v : E) :
    (rankOneLm x y : _ →ₗ[𝕜] _) ((rankOneLm z w : _ →ₗ[𝕜] _) v) = (⟪y,z⟫_𝕜 * ⟪w,v⟫_𝕜) • x := by
  rw [← LinearMap.comp_apply, rankOneLm_comp_rankOneLm, LinearMap.smul_apply, rankOneLm_apply,
    smul_smul]

theorem rankOneLm_adjoint [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] (x : E₁) (y : E₂) :
    LinearMap.adjoint (rankOneLm x y : _ →ₗ[𝕜] _) = rankOneLm y x :=
  by
  simp_rw [rankOneLm, LinearMap.adjoint_eq_toCLM_adjoint,
    ContinuousLinearMap.coe_inj, ← @rankOne.adjoint 𝕜 _ _ _ _ _ _ _
      (FiniteDimensional.complete 𝕜 E₁) (FiniteDimensional.complete 𝕜 E₂) x y]
  rfl

open scoped BigOperators

theorem sum_rankOne {n : Type _} {s : Finset n} (x : n → E₁) (y : E₂) :
    (rankOne (∑ i in s, x i) y : E₂ →L[𝕜] E₁) = ∑ i in s, rankOne (x i) y :=
  by
  simp only [map_sum, AddMonoidHom.finset_sum_apply]

theorem rankOne_sum {n : Type _} {s : Finset n} (x : E₁) (y : n → E₂) :
    (rankOne x (∑ i in s, y i) : _ →L[𝕜] _) = ∑ i in s, rankOne x (y i) :=
  by
  simp only [map_sum]

theorem sum_rankOneLm {n : Type _} {s : Finset n} (x : n → E₁) (y : E₂) :
    (rankOneLm (∑ i in s, x i) y : _ →ₗ[𝕜] _) = ∑ i in s, rankOneLm (x i) y :=
by simp [rankOneLm, sum_rankOne]

theorem rankOneLm_sum {n : Type _} {s : Finset n} (x : E₁) (y : n → E₂) :
    (rankOneLm x (∑ i in s, y i) : _ →ₗ[𝕜] _) = ∑ i in s, rankOneLm x (y i) :=
by simp [rankOneLm, rankOne_sum]

end rankOneLm

theorem LinearMap.ext_of_rankOne {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜] [AddCommMonoid H'] [Module 𝕜 H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →L[𝕜] H₂) →ₗ[𝕜] H'} (h : ∀ a b, x (rankOne a b) = y (rankOne a b)) : x = y :=
  by
  ext a
  obtain ⟨α, β, rfl⟩ := ContinuousLinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]

theorem LinearMap.ext_of_rank_one' {𝕜 H₁ H₂ H' : Type _} [RCLike 𝕜] [AddCommMonoid H'] [Module 𝕜 H']
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    [FiniteDimensional 𝕜 H₁] [FiniteDimensional 𝕜 H₂]
    {x y : (H₁ →ₗ[𝕜] H₂) →ₗ[𝕜] H'}
    (h : ∀ a b, x (rankOne a b : _ →L[𝕜] _).toLinearMap = y (rankOne a b : _ →L[𝕜] _).toLinearMap) : x = y :=
  by
  ext a
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]

open scoped BigOperators

theorem rankOne.sum_orthonormalBasis_eq_id_lm {𝕜 : Type _} {E : Type _} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type _} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) : ∑ i, (rankOne (b i) (b i) : E →L[𝕜] E).toLinearMap = 1 :=
  by
  simp only [← ContinuousLinearMap.coe_sum, rankOne.sum_orthonormalBasis_eq_id b]
  rfl

theorem ContinuousLinearMap.coe_eq_zero {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂] (f : E₁ →L[𝕜] E₂) :
    (f : E₁ →ₗ[𝕜] E₂) = 0 ↔ f = 0 := by norm_cast

theorem rankOne.eq_zero_iff {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) : (rankOne x y : _ →L[𝕜] _) = 0 ↔ x = 0 ∨ y = 0 := by
  simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply, ContinuousLinearMap.zero_apply, smul_eq_zero,
    forall_or_right, forall_inner_eq_zero_iff, or_comm]

theorem rankOne.left_add {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x y : E₁) (z : E₂) : (rankOne (x + y) z : _ →L[𝕜] _) = rankOne x z + rankOne y z :=
  by
  simp only [map_add, AddMonoidHom.add_apply]

theorem rankOne.right_add {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y z : E₂) : (rankOne x (y + z) : _ →L[𝕜] _) = rankOne x y + rankOne x z :=
  by
  simp only [map_add]

theorem rankOne.left_sub {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x y : E₁) (z : E₂) : (rankOne (x - y) z : _ →L[𝕜] _) = rankOne x z - rankOne y z :=
  by
  simp only [map_sub, AddMonoidHom.sub_apply]

theorem rankOne.right_sub {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y z : E₂) : (rankOne x (y - z) : _ →L[𝕜] _) = rankOne x y - rankOne x z :=
  by
  simp only [map_sub]

theorem LinearMap.rankOne_comp {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
  [InnerProductSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₂] [FiniteDimensional 𝕜 E₃] (x : E₁) (y : E₂) (u : E₃ →ₗ[𝕜] E₂) :
    (rankOne x y : _ →L[𝕜] _).toLinearMap ∘ₗ u = (rankOne x (adjoint u y) : _ →L[𝕜] _) :=
  by
  ext
  simp_rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    LinearMap.adjoint_inner_left]

theorem LinearMap.rankOne_comp'  {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
  [InnerProductSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₂] [FiniteDimensional 𝕜 E₃] (x : E₁) (y : E₂) (u : E₂ →ₗ[𝕜] E₃) :
    (rankOne x y : _ →L[𝕜] _).toLinearMap ∘ₗ adjoint u = (rankOne x (u y) : _ →L[𝕜] _) :=
by rw [LinearMap.rankOne_comp, LinearMap.adjoint_adjoint]

theorem OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne {ι 𝕜 : Type _} [RCLike 𝕜] {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] {U : Submodule 𝕜 E}
    [CompleteSpace U] (b : OrthonormalBasis ι 𝕜 ↥U) :
    orthogonalProjection' U = ∑ i : ι, rankOne (b i : E) (b i : E) :=
  by
  ext
  simp_rw [orthogonalProjection'_apply, b.orthogonalProjection_eq_sum,
    ContinuousLinearMap.sum_apply, rankOne_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]

theorem LinearMap.comp_rankOne  {𝕜 E₁ E₂ E₃ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
  [InnerProductSpace 𝕜 E₃] [FiniteDimensional 𝕜 E₂] [FiniteDimensional 𝕜 E₃] (x : E₁) (y : E₂) (u : E₁ →ₗ[𝕜] E₃) :
    u ∘ₗ (rankOne x y : _ →L[𝕜] _).toLinearMap = (rankOne (u x) y : _ →L[𝕜] _) :=
  by
  ext
  simp_rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply, _root_.map_smul]


theorem _root_.rankOne_smul_smul {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) (r₁ r₂ : 𝕜) :
    rankOne (r₁ • x) (star r₂ • y) = (r₁ * r₂) • (rankOne x y : _ →L[𝕜] _) := by
  simp only [rankOne.smul_apply, rankOne.apply_smul, smul_smul, starRingEnd_apply, star_star, mul_comm]

theorem _root_.rankOne_lm_smul_smul {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) (r₁ r₂ : 𝕜) :
    (rankOne (r₁ • x) (star r₂ • y) : _ →L[𝕜] _).toLinearMap =
      (r₁ * r₂) • ((rankOne x y : _ →L[𝕜] _) : _ →ₗ[𝕜] _) :=
  by rw [rankOne_smul_smul, ContinuousLinearMap.coe_smul]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem _root_.rankOne_lm_sum_sum {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    {ι₁ ι₂ : Type _} [Fintype ι₁] [Fintype ι₂] (f : ι₁ → E₁) (g : ι₂ → E₂) :
    (rankOne (∑ i, f i) (∑ i, g i) : _ →L[𝕜] _).toLinearMap =
      ∑ i, ∑ j, ((rankOne (f i) (g j) : _ →L[𝕜] _) : _ →ₗ[𝕜] _) :=
  by simp_rw [sum_rankOne, rankOne_sum, ContinuousLinearMap.coe_sum]

theorem ContinuousLinearMap.linearMap_adjoint {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] (x : B →L[𝕜] C) :
    LinearMap.adjoint (x : B →ₗ[𝕜] C) =
      @ContinuousLinearMap.adjoint 𝕜 _ _ _ _ _ _ _ (FiniteDimensional.complete 𝕜 B)
        (FiniteDimensional.complete 𝕜 C) x :=
  rfl
