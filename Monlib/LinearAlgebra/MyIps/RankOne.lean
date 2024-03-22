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

variable {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- local notation "L(" x ")" => x →L[ℂ] x

local notation "⟪" x "," y "⟫_𝕜" => @inner 𝕜 _ _ x y

/-- we define the rank one operator $| x \rangle\!\langle y |$ by
  $x \mapsto \langle y,  z \rangle \cdot  x$ -/
def rankOne (x y : E) : E →L[𝕜] E where
  toFun z := ⟪y,z⟫_𝕜 • x
  map_add' u v := by simp_rw [inner_add_right, add_smul]
  map_smul' r u := by simp_rw [inner_smul_right, RingHom.id_apply, smul_smul]
  cont := Continuous.smul (Continuous.inner continuous_const continuous_id') (continuous_const)

-- local notation "|" x "⟩⟨" y "|" => rankOne x y

@[simp]
theorem rankOne_apply {x y : E} (z : E) : (rankOne x y : E →L[𝕜] E) z = ⟪y,z⟫_𝕜 • x :=
  rfl

open ContinuousLinearMap

/-- $| x \rangle\!\langle \alpha\cdot y | = \bar{\alpha} \cdot | x \rangle\!\langle y |$ -/
@[simp]
theorem rankOne.smul_apply {x y : E} {α : 𝕜} :
    rankOne x (α • y) = (starRingEnd 𝕜) α • (rankOne x y : E →L[𝕜] E) :=
  by
  ext
  simp_rw [ContinuousLinearMap.smul_apply, rankOne_apply, inner_smul_left, smul_smul]

/-- $| \alpha \cdot x \rangle\!\langle y | = \alpha \cdot | x \rangle\!\langle y |$ -/
@[simp]
theorem rankOne.apply_smul {x y : E} {α : 𝕜} : rankOne (α • x) y = α • (rankOne x y : E →L[𝕜] E) :=
  by
  ext
  simp_rw [ContinuousLinearMap.smul_apply, rankOne_apply, smul_smul, mul_comm]

@[simp]
theorem rankOne.smul_real_apply {x y : E} {α : ℝ} :
    rankOne x ((α : 𝕜) • y) = (α : 𝕜) • (rankOne x y : E →L[𝕜] E) := by
  simp_rw [rankOne.smul_apply, IsROrC.conj_ofReal]

/--
$| x \rangle\!\langle y | | z \rangle\!\langle w | = \langle y, z \rangle \cdot  | x \rangle\!\langle w |$ -/
@[simp]
theorem rankOne.apply_rankOne (x y z w : E) :
    (rankOne x y : E →L[𝕜] E) ∘L (rankOne z w : _) = ⟪y,z⟫_𝕜 • (rankOne x w : _) :=
  by
  ext r
  simp_rw [ContinuousLinearMap.smul_apply, comp_apply, rankOne_apply, inner_smul_right, mul_comm, smul_smul]

/-- $u \circ | x \rangle\!\langle y | = | u(x) \rangle\!\langle y |$ -/
theorem ContinuousLinearMap.comp_rankOne (x y : E) (u : E →L[𝕜] E) : u ∘L rankOne x y = rankOne (u x) y :=
  by
  ext r
  simp_rw [comp_apply, rankOne_apply, map_smul]

/-- $| x \rangle\!\langle y | \circ u  = | x \rangle\!\langle u^*(y) |$ -/
theorem ContinuousLinearMap.rankOne_comp [CompleteSpace E] (x y : E) (u : E →L[𝕜] E) :
    rankOne x y ∘L (u : E →L[𝕜] E) = rankOne x (adjoint u y) :=
  by
  ext r
  simp_rw [comp_apply, rankOne_apply, adjoint_inner_left]

/-- rank one operators given by norm one vectors are automatically idempotent -/
@[simp]
theorem rankOne.isIdempotentElem (x : E) (h : ‖x‖ = 1) : IsIdempotentElem (rankOne x x : E →L[𝕜] E) := by
  simp_rw [IsIdempotentElem, ContinuousLinearMap.ext_iff, mul_def, rankOne.apply_rankOne,
    inner_self_eq_norm_sq_to_K, h, IsROrC.ofReal_one, one_pow, one_smul,
    forall_const]

theorem rankOne.isSymmetric (x : E) : LinearMap.IsSymmetric ((rankOne x x : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
  simp_rw [LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
    inner_smul_right, inner_conj_symm, mul_comm, forall₂_true_iff]

/-- rank one operators are automatically self-adjoint -/
@[simp]
theorem rankOne.isSelfAdjoint [CompleteSpace E] (x : E) : IsSelfAdjoint (rankOne x x : E →L[𝕜] E) :=
  isSelfAdjoint_iff_isSymmetric.mpr (rankOne.isSymmetric x)

/-- $| x \rangle\!\langle y |^* = | y \rangle\!\langle x |$ -/
theorem rankOne.adjoint [CompleteSpace E] (x y : E) : adjoint (rankOne x y) = (rankOne y x : E →L[𝕜] E) :=
  by
  ext a
  apply @ext_inner_right 𝕜
  intro b
  simp_rw [adjoint_inner_left, rankOne_apply, inner_smul_left, inner_smul_right, inner_conj_symm,
    mul_comm]

theorem rankOne_inner_left (x y z w : E) : ⟪(rankOne x y : E →L[𝕜] E) z,w⟫_𝕜 = ⟪z,y⟫_𝕜 * ⟪x,w⟫_𝕜 := by
  rw [rankOne_apply, inner_smul_left, inner_conj_symm]

theorem rankOne_inner_right (x y z w : E) : ⟪x,(rankOne y z : E →L[𝕜] E) w⟫_𝕜 = ⟪z,w⟫_𝕜 * ⟪x,y⟫_𝕜 := by
  rw [rankOne_apply, inner_smul_right]

theorem ContinuousLinearMap.commutes_with_all_iff [CompleteSpace E] (T : E →L[𝕜] E) :
    (∀ S : E →L[𝕜] E, Commute S T) ↔ ∃ α : 𝕜, T = α • 1 :=
  by
  constructor
  · intro h
    have h' : ∀ x y : E, rankOne x y ∘L T = T ∘L rankOne x y := fun x y => h _
    simp_rw [ContinuousLinearMap.rankOne_comp, ContinuousLinearMap.comp_rankOne] at h'
    have h'' : ∀ x y : E, (rankOne (adjoint T y) x : E →L[𝕜] E) = rankOne y (T x) :=
      by
      intro x y
      nth_rw 1 [← rankOne.adjoint]
      rw [h', rankOne.adjoint]
    simp_rw [ext_iff, rankOne_apply] at h' h''
    by_cases H : ∀ x : E, x = 0
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

theorem ContinuousLinearMap.centralizer [CompleteSpace E] :
    (@Set.univ (E →L[𝕜] E)).centralizer = { x : E →L[𝕜] E | ∃ α : 𝕜, x = α • 1 } :=
  by
  simp_rw [Set.centralizer, Set.mem_univ, true_imp_iff, ← ContinuousLinearMap.commutes_with_all_iff]
  rfl

theorem ContinuousLinearMap.scalar_centralizer :
    {x : E →L[𝕜] E | ∃ α : 𝕜, x = α • 1}.centralizer = @Set.univ (E →L[𝕜] E) :=
  by
  simp_rw [Set.centralizer, Set.ext_iff, Set.mem_setOf, Set.mem_univ, iff_true_iff]
  rintro x y ⟨α, rfl⟩
  simp only [Algebra.smul_mul_assoc, one_mul, Algebra.mul_smul_comm, mul_one]

theorem ContinuousLinearMap.centralizer_centralizer [CompleteSpace E] :
    (@Set.univ (E →L[𝕜] E)).centralizer.centralizer = Set.univ := by
  rw [ContinuousLinearMap.centralizer, ContinuousLinearMap.scalar_centralizer]

theorem rankOne.zero_left {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : E) : (rankOne 0 x : E →L[𝕜] E) = 0 := by
  ext1
  simp_rw [rankOne_apply, smul_zero, ContinuousLinearMap.zero_apply]

theorem rankOne.zero_right {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x : E) : (rankOne x 0 : E →L[𝕜] E) = 0 := by
  ext1
  simp_rw [rankOne_apply, inner_zero_left, zero_smul, ContinuousLinearMap.zero_apply]

theorem rankOne.ext_iff {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) (h : (rankOne x x : E →L[𝕜] E) = rankOne y y) : ∃ α : 𝕜ˣ, x = (α : 𝕜) • y :=
  by
  have : x = 0 ↔ y = 0 :=
    by
    constructor <;> intro hh <;>
      simp only [hh, ContinuousLinearMap.ext_iff, rankOne.zero_left, ContinuousLinearMap.zero_apply,
        @eq_comm _ (0 : E →L[𝕜] E), rankOne_apply, smul_eq_zero] at h
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
    [InnerProductSpace 𝕜 F] (T S : E →L[𝕜] F) : T = S ↔ ∀ x y, ⟪T x,y⟫_𝕜 = ⟪S x,y⟫_𝕜 :=
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

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_1 x_2) -/
theorem ContinuousLinearMap.exists_sum_rankOne [FiniteDimensional 𝕜 E] (T : E →L[𝕜] E) :
    ∃ x y : Fin (FiniteDimensional.finrank 𝕜 E) × Fin (FiniteDimensional.finrank 𝕜 E) → E,
      T = ∑ i, |x i⟩⟨y i| :=
  by
  letI := FiniteDimensional.complete 𝕜 E
  let e := stdOrthonormalBasis 𝕜 E
  let a : Fin (FiniteDimensional.finrank 𝕜 E) × Fin (FiniteDimensional.finrank 𝕜 E) → E := fun ij =>
    e.repr (T (e ij.1)) ij.2 • e ij.2
  let b : Fin (FiniteDimensional.finrank 𝕜 E) × Fin (FiniteDimensional.finrank 𝕜 E) → E := fun ij =>
    e ij.1
  refine' ⟨a, b, _⟩
  simp only [a, b]
  simp only [ContinuousLinearMap.ext_inner_map, sum_apply, sum_inner, rankOne_inner_left,
    inner_smul_left, OrthonormalBasis.repr_apply_apply, inner_conj_symm]
  intro u v
  symm
  calc
    ∑ x : Fin (FiniteDimensional.finrank 𝕜 E) × Fin (FiniteDimensional.finrank 𝕜 E),
          ⟪u,e x.fst⟫_𝕜 * (⟪T (e x.fst),e x.snd⟫_𝕜 * ⟪e x.snd,v⟫_𝕜) =
        ∑ x_1 : Fin (FiniteDimensional.finrank 𝕜 E),
        ∑ x_2 : Fin (FiniteDimensional.finrank 𝕜 E),
          ⟪u,e x_1⟫_𝕜 * (⟪T (e x_1),e x_2⟫_𝕜 * ⟪e x_2,v⟫_𝕜) :=
      by simp_rw [← Finset.sum_product', Finset.univ_product_univ]
    _ = ∑ x_1, ⟪u,e x_1⟫_𝕜 * ⟪T (e x_1),v⟫_𝕜 := by
      simp_rw [← Finset.mul_sum, OrthonormalBasis.sum_inner_mul_inner]
    _ = ⟪T u,v⟫_𝕜 := by simp_rw [← adjoint_inner_right T, OrthonormalBasis.sum_inner_mul_inner]

theorem LinearMap.exists_sum_rankOne [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    ∃ x y : Fin (FiniteDimensional.finrank 𝕜 E) × Fin (FiniteDimensional.finrank 𝕜 E) → E,
      T = ∑ i, ↑(|x i⟩⟨y i| : E →L[𝕜] E) :=
  by
  obtain ⟨a, b, h⟩ := ContinuousLinearMap.exists_sum_rankOne (toContinuousLinearMap T)
  refine' ⟨a, b, _⟩
  simp_rw [← coe_sum, ← h]
  rfl

theorem rankOne.sum_orthonormalBasis_eq_id {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
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

variable {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x "," y "⟫_𝕜" => @inner 𝕜 _ _ x y

/-- same as `rank_one`, but as a linear map -/
def rankOneLm (x y : E) : E →ₗ[𝕜] E :=
  (rankOne x y).toLinearMap

@[simp]
theorem rankOneLm_apply (x y z : E) : (rankOneLm x y : E →ₗ[𝕜] E) z = ⟪y,z⟫_𝕜 • x :=
  rfl

theorem rankOneLm_comp_rankOneLm (x y z w : E) :
    (rankOneLm x y : E →ₗ[𝕜] E) ∘ₗ rankOneLm z w = ⟪y,z⟫_𝕜 • (rankOneLm x w : _) := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, rankOneLm_apply, LinearMap.smul_apply,
    inner_smul_right, mul_smul, rankOneLm_apply, smul_smul, mul_comm,
    forall_true_iff]

theorem rankOneLm_apply_rank_one (x y z w v : E) :
    (rankOneLm x y : E →ₗ[𝕜] E) ((rankOneLm z w : E →ₗ[𝕜] E) v) = (⟪y,z⟫_𝕜 * ⟪w,v⟫_𝕜) • x := by
  rw [← LinearMap.comp_apply, rankOneLm_comp_rankOneLm, LinearMap.smul_apply, rankOneLm_apply,
    smul_smul]

theorem rankOneLm_adjoint [FiniteDimensional 𝕜 E] (x y : E) :
    LinearMap.adjoint (rankOneLm x y : E →ₗ[𝕜] E) = rankOneLm y x :=
  by
  simp_rw [rankOneLm, LinearMap.adjoint_eq_toCLM_adjoint,
    ContinuousLinearMap.coe_inj, ← @rankOne.adjoint 𝕜 _ _ _ _ (FiniteDimensional.complete 𝕜 E) x y]
  rfl

open scoped BigOperators

theorem sum_rankOne {n : Type _} [Fintype n] (x : n → E) (y : E) :
    (rankOne (∑ i, x i) y : E →L[𝕜] E) = ∑ i, rankOne (x i) y :=
  by
  ext1 z
  simp_rw [ContinuousLinearMap.sum_apply, rankOne_apply, Finset.smul_sum]

theorem rankOne_sum {n : Type _} [Fintype n] (x : E) (y : n → E) :
    (rankOne x (∑ i, y i) : E →L[𝕜] E) = ∑ i, rankOne x (y i) :=
  by
  ext1 z
  simp_rw [ContinuousLinearMap.sum_apply, rankOne_apply, sum_inner, Finset.sum_smul]

theorem sum_rankOneLm {n : Type _} [Fintype n] (x : n → E) (y : E) :
    (rankOneLm (∑ i : n, x i) y : E →ₗ[𝕜] E) = ∑ i : n, rankOneLm (x i) y :=
  by
  rw [rankOneLm, sum_rankOne, ContinuousLinearMap.coe_sum]
  rfl

theorem rankOneLm_sum {n : Type _} [Fintype n] (x : E) (y : n → E) :
    (rankOneLm x (∑ i : n, y i) : E →ₗ[𝕜] E) = ∑ i : n, rankOneLm x (y i) :=
  by
  rw [rankOneLm, rankOne_sum, ContinuousLinearMap.coe_sum]
  rfl

end rankOneLm

theorem LinearMap.ext_of_rankOne {𝕜 H H' : Type _} [IsROrC 𝕜] [AddCommMonoid H'] [Module 𝕜 H']
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
    {x y : (H →L[𝕜] H) →ₗ[𝕜] H'} (h : ∀ a b : H, x (rankOne a b) = y (rankOne a b)) : x = y :=
  by
  ext a
  obtain ⟨α, β, rfl⟩ := ContinuousLinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]

theorem LinearMap.ext_of_rank_one' {𝕜 H H' : Type _} [IsROrC 𝕜] [AddCommMonoid H'] [Module 𝕜 H']
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
    {x y : (H →ₗ[𝕜] H) →ₗ[𝕜] H'}
    (h : ∀ a b : H, x ↑(@rankOne 𝕜 _ _ _ _ a b) = y ↑(@rankOne 𝕜 _ _ _ _ a b)) : x = y :=
  by
  ext a
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne a
  simp_rw [map_sum, h]

open scoped BigOperators

theorem rankOne.sum_orthonormalBasis_eq_id_lm {𝕜 : Type _} {E : Type _} [IsROrC 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type _} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) : ∑ i, (@rankOne 𝕜 E _ _ _ (b i) (b i) : E →ₗ[𝕜] E) = 1 :=
  by
  simp only [← ContinuousLinearMap.coe_sum, rankOne.sum_orthonormalBasis_eq_id b]
  rfl

theorem ContinuousLinearMap.coe_eq_zero {𝕜 E₁ E₂ : Type _} [IsROrC 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂] (f : E₁ →L[𝕜] E₂) :
    (f : E₁ →ₗ[𝕜] E₂) = 0 ↔ f = 0 := by norm_cast

theorem rankOne.eq_zero_iff {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) : (rankOne x y : E →L[𝕜] E) = 0 ↔ x = 0 ∨ y = 0 := by
  simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply, ContinuousLinearMap.zero_apply, smul_eq_zero,
    forall_or_right, forall_inner_eq_zero_iff, or_comm]

theorem rankOne.left_add {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y z : E) : (rankOne (x + y) z : E →L[𝕜] E) = rankOne x z + rankOne y z :=
  by
  ext
  simp only [rankOne_apply, ContinuousLinearMap.add_apply, smul_add]

theorem rankOne.right_add {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y z : E) : (rankOne x (y + z) : E →L[𝕜] E) = rankOne x y + rankOne x z :=
  by
  ext
  simp only [rankOne_apply, ContinuousLinearMap.add_apply, inner_add_left, add_smul]

theorem rankOne.left_sub {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y z : E) : (rankOne (x - y) z : E →L[𝕜] E) = rankOne x z - rankOne y z :=
  by
  ext
  simp only [rankOne_apply, ContinuousLinearMap.sub_apply, smul_sub]

theorem rankOne.right_sub {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y z : E) : (rankOne x (y - z) : E →L[𝕜] E) = rankOne x y - rankOne x z :=
  by
  ext
  simp only [rankOne_apply, ContinuousLinearMap.sub_apply, inner_sub_left, sub_smul]

theorem LinearMap.rankOne_comp {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (x y : E) (u : E →ₗ[𝕜] E) :
    ((rankOne x y : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ u = (rankOne x (adjoint u y) : E →L[𝕜] E) :=
  by
  ext
  simp_rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    LinearMap.adjoint_inner_left]

theorem LinearMap.rankOne_comp' {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (x y : E) (u : E →ₗ[𝕜] E) :
    ((rankOne x y : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ adjoint u = (rankOne x (u y) : E →L[𝕜] E) := by
  rw [LinearMap.rankOne_comp, LinearMap.adjoint_adjoint]

theorem OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne {ι 𝕜 : Type _} [IsROrC 𝕜] {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] {U : Submodule 𝕜 E}
    [CompleteSpace ↥U] (b : OrthonormalBasis ι 𝕜 ↥U) :
    orthogonalProjection' U = ∑ i : ι, rankOne (b i : E) (b i : E) :=
  by
  ext
  simp_rw [orthogonalProjection'_apply, b.orthogonalProjection_eq_sum,
    ContinuousLinearMap.sum_apply, rankOne_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]

theorem LinearMap.comp_rankOne {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x y : E) (u : E →ₗ[𝕜] E) :
    u ∘ₗ ((rankOne x y : E →L[𝕜] E) : E →ₗ[𝕜] E) = (rankOne (u x) y : E →L[𝕜] E) :=
  by
  ext
  simp_rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply, SMulHomClass.map_smul]
