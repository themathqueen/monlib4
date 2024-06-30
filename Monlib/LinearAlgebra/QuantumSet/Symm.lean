import Monlib.LinearAlgebra.IsReal
-- import Monlib.LinearAlgebra.MyIps.Nontracial
import Monlib.LinearAlgebra.Ips.OpUnop
import Monlib.LinearAlgebra.QuantumSet.Basic
import Monlib.LinearAlgebra.Ips.MulOp
import Monlib.LinearAlgebra.TensorProduct.FiniteDimensional

#align_import quantum_graph.symm

@[simps]
noncomputable def symmMap (R : Type _) [RCLike R] (M₁ M₂ : Type _) [NormedAddCommGroup M₁]
  [NormedAddCommGroup M₂]
    [InnerProductSpace R M₁] [InnerProductSpace R M₂] [StarAddMonoid M₁]
    [StarAddMonoid M₂] [StarModule R M₁] [StarModule R M₂] [FiniteDimensional R M₁]
    [FiniteDimensional R M₂] :
    (M₁ →ₗ[R] M₂) ≃ₗ[R] M₂ →ₗ[R] M₁
    where
  toFun f := LinearMap.adjoint (LinearMap.real f)
  invFun f := (LinearMap.adjoint f).real
  left_inv f := by simp only [LinearMap.adjoint_adjoint, LinearMap.real_real]
  right_inv f := by simp only [LinearMap.real_real, LinearMap.adjoint_adjoint]
  map_add' f g := by simp only [LinearMap.real_add, map_add]
  map_smul' c f := by
    simp only [LinearMap.real_smul, LinearMap.adjoint_smul, starRingEnd_self_apply,
      RingHom.id_apply]

theorem symmMap_real {R : Type _} [RCLike R] {M : Type _} [NormedAddCommGroup M]
    [InnerProductSpace R M] [StarAddMonoid M] [StarModule R M] [FiniteDimensional R M] :
    LinearMap.real (symmMap R M M : (M →ₗ[R] M) →ₗ[R] M →ₗ[R] M) =
      (symmMap R M M).symm :=
  by
  ext1 f
  simp_rw [LinearMap.real_apply, LinearEquiv.coe_coe, LinearMap.star_eq_adjoint,
    symmMap_apply, LinearMap.adjoint_adjoint]
  rfl

open scoped TensorProduct Matrix

-- variable {n : Type _} [Fintype n] [DecidableEq n] {s : n → Type _} [∀ i, Fintype (s i)]
--   [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
--   {n₂ : Type _} [Fintype n₂] [DecidableEq n₂] {s₂ : n₂ → Type _} [∀ i, Fintype (s₂ i)]
--   [∀ i, DecidableEq (s₂ i)] {φ : ∀ i, Module.Dual ℂ (Matrix (s₂ i) (s₂ i) ℂ)}

-- local notation "𝔹" => PiMat ℂ n s
-- local notation "𝔹₂" => PiMat ℂ n₂ s₂

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" x => LinearMap.mul' ℂ x

local notation "η" x => Algebra.linearMap ℂ x

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" => TensorProduct.assoc ℂ

-- local notation "υ⁻¹" x y z =>
  -- LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.assoc ℂ x y z))

local notation x "ϰ" y =>
  LinearEquiv.toLinearMap (TensorProduct.comm ℂ x y)

local notation x "ϰ⁻¹" y =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ x y))

local notation "τ" x =>
  LinearEquiv.toLinearMap (TensorProduct.lid ℂ x)

local notation "τ⁻¹" x =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ x))

local notation "id" x => (1 : x →ₗ[ℂ] x)

variable {A B : Type*} [ha:starAlgebra A] [hb:starAlgebra B]
  [hA : QuantumSet A] [hB : QuantumSet B]

theorem symmMap_rankOne_apply (a : A) (b : B) :
    symmMap _ _ _ (|a⟩⟨b| : B →ₗ[ℂ] A) =
      |hb.modAut (-(2*hB.k)-1) (star b)⟩⟨star a| :=
letI := FiniteDimensional.complete ℂ A
letI := FiniteDimensional.complete ℂ B
by rw [symmMap_apply, rankOne_real, ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint]

theorem symmMap_symm_rankOne_apply (a : A) (b : B) :
    (symmMap _ _ _).symm (|a⟩⟨b| : B →ₗ[ℂ] A) =
      |star b⟩⟨ha.modAut (-(2*hA.k)-1) (star a)| :=
letI := FiniteDimensional.complete ℂ A
letI := FiniteDimensional.complete ℂ B
by rw [symmMap_symm_apply, ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint, rankOne_real]

open scoped BigOperators

open TensorProduct

open Coalgebra LinearMap in
private noncomputable def symmMapAux :
  (A →ₗ[ℂ] B) →ₗ[ℂ] (B →ₗ[ℂ] A) :=
{ toFun := λ x => (TensorProduct.rid ℂ _).toLinearMap
    ∘ₗ (lTensor _ (counit ∘ₗ m _))
    ∘ₗ (υ _ _ _).toLinearMap
    ∘ₗ (rTensor _ (lTensor _ x))
    ∘ₗ (rTensor _ (comul ∘ₗ Algebra.linearMap ℂ _))
    ∘ₗ (τ⁻¹ _)
  map_add' := λ x y => by simp only [lTensor_add, rTensor_add, comp_add, add_comp]
  map_smul' := λ r x => by simp only [lTensor_smul, rTensor_smul, RingHom.id_apply,
    comp_smul, smul_comp] }
open Coalgebra LinearMap in
private lemma symmMapAux_apply (f : A →ₗ[ℂ] B) :
  symmMapAux f = (TensorProduct.rid ℂ _).toLinearMap
    ∘ₗ (lTensor _ (counit ∘ₗ m _))
    ∘ₗ (υ _ _ _).toLinearMap
    ∘ₗ (rTensor _ (lTensor _ f))
    ∘ₗ (rTensor _ (comul ∘ₗ Algebra.linearMap ℂ _))
    ∘ₗ (τ⁻¹ _) :=
rfl

set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 0 in
open Coalgebra LinearMap in
theorem symmMap_eq (f : A →ₗ[ℂ] B)
  (gns₁ : hA.k = 0) (gns₂ : hB.k = 0) :
  (symmMap ℂ A _) f = (TensorProduct.rid ℂ _).toLinearMap
    ∘ₗ (lTensor _ (counit ∘ₗ m _))
    ∘ₗ (υ _ _ _).toLinearMap
    ∘ₗ (rTensor _ (lTensor _ f))
    ∘ₗ (rTensor _ (comul ∘ₗ Algebra.linearMap ℂ _))
    ∘ₗ (τ⁻¹ _) :=
by
  rw [← symmMapAux_apply]
  revert f
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.ext_iff]
  apply ext_of_rank_one'
  intro x y
  rw [LinearEquiv.coe_toLinearMap, symmMap_rankOne_apply, eq_comm, LinearMap.ext_iff]
  intro a
  apply ext_inner_right ℂ
  intro b
  obtain ⟨α, β, this⟩ := TensorProduct.eq_span (comul (1 : A) : A ⊗[ℂ] A)
  simp_rw [symmMapAux_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, lid_symm_apply,
    rTensor_tmul, LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
    one_smul]
  rw [← this]
  simp_rw [_root_.map_sum, lTensor_tmul, sum_tmul, _root_.map_sum, assoc_tmul,
    lTensor_tmul, rid_tmul, sum_inner, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, ← smul_tmul', _root_.map_smul,
    ← inner_eq_counit', smul_eq_mul, LinearMap.mul'_apply, inner_smul_left,
    starRingEnd_apply, star_mul, ← starRingEnd_apply, inner_conj_symm, mul_assoc,
    ← Finset.mul_sum, mul_comm ⟪_, y⟫_ℂ, ← inner_tmul, ← sum_inner, this, comul_eq_mul_adjoint,
    adjoint_inner_left, mul'_apply, inner_tmul, QuantumSet.inner_star_left,
    ← inner_conj_symm (1 : A), QuantumSet.inner_conj_left, mul_one, one_mul, inner_conj_symm]
  simp only [gns₁, gns₂, zero_mul, zero_add, neg_zero, mul_zero, zero_sub,
    starAlgebra.modAut_zero, AlgEquiv.one_apply]

open Coalgebra LinearMap in
private noncomputable def symmMapSymmAux :
  (A →ₗ[ℂ] B) →ₗ[ℂ] (B →ₗ[ℂ] A) :=
{ toFun := λ x => (TensorProduct.lid ℂ A).toLinearMap
    ∘ₗ (rTensor _ (counit ∘ₗ m _))
    ∘ₗ (rTensor _ (lTensor _ x))
    ∘ₗ (υ _ _ _).symm.toLinearMap
    ∘ₗ (lTensor _ (comul ∘ₗ Algebra.linearMap ℂ _))
    ∘ₗ (TensorProduct.rid ℂ _).symm.toLinearMap
  map_add' := λ x y => by simp only [lTensor_add, rTensor_add, comp_add, add_comp]
  map_smul' := λ r x => by simp only [lTensor_smul, rTensor_smul, RingHom.id_apply,
    comp_smul, smul_comp] }
open Coalgebra LinearMap in
private lemma symmMapSymmAux_apply
  (f : A →ₗ[ℂ] B) :
  symmMapSymmAux f = (TensorProduct.lid ℂ A).toLinearMap
    ∘ₗ (rTensor _ (counit ∘ₗ m _))
    ∘ₗ (rTensor _ (lTensor _ f))
    ∘ₗ (υ _ _ _).symm.toLinearMap
    ∘ₗ (lTensor _ (comul ∘ₗ Algebra.linearMap ℂ _))
    ∘ₗ (TensorProduct.rid ℂ _).symm.toLinearMap :=
rfl

open LinearMap Coalgebra in
-- set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 0 in
theorem symmMap_symm_eq (f : A →ₗ[ℂ] B)
  (gns₁ : hA.k = 0) (gns₂ : hB.k = 0) :
  (symmMap ℂ _ _).symm f = (TensorProduct.lid ℂ A).toLinearMap
    ∘ₗ (rTensor _ (counit ∘ₗ m _))
    ∘ₗ (rTensor _ (lTensor _ f))
    ∘ₗ (υ _ _ _).symm.toLinearMap
    ∘ₗ (lTensor _ (comul ∘ₗ Algebra.linearMap ℂ _))
    ∘ₗ (TensorProduct.rid ℂ _).symm.toLinearMap :=
  by
  rw [← symmMapSymmAux_apply]
  revert f
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.ext_iff]
  apply ext_of_rank_one'
  intro x y
  rw [LinearEquiv.coe_toLinearMap, symmMap_symm_rankOne_apply, eq_comm, LinearMap.ext_iff]
  intro a
  apply ext_inner_right ℂ
  intro b
  obtain ⟨α, β, this⟩ := TensorProduct.eq_span (comul (1 : A) : A ⊗[ℂ] A)
  simp_rw [symmMapSymmAux_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, rid_symm_apply,
    lTensor_tmul, LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
    one_smul]
  rw [← this]
  simp_rw [tmul_sum, _root_.map_sum, assoc_symm_tmul, rTensor_tmul,
    lTensor_tmul, comp_apply, lid_tmul, sum_inner, mul'_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, mul_smul_comm, _root_.map_smul,
    ← inner_eq_counit', smul_eq_mul, inner_smul_left, starRingEnd_apply,
    star_mul, ← starRingEnd_apply, inner_conj_symm, mul_assoc,
    ← Finset.mul_sum, ← inner_tmul, ← sum_inner, this, comul_eq_mul_adjoint,
    adjoint_inner_left, mul'_apply, inner_tmul, QuantumSet.inner_star_left,
    mul_one, ← inner_conj_symm (1 : A), QuantumSet.inner_star_left, mul_one, inner_conj_symm]
  nth_rw 1 [QuantumSet.inner_conj]
  simp only [gns₁, gns₂, zero_mul, zero_add, neg_zero, mul_zero, zero_sub,
    starAlgebra.modAut_zero, star_star, AlgEquiv.one_apply]

open Coalgebra in
theorem symmMap_eq_self_tfae (f : B →ₗ[ℂ] B) (gns : hB.k = 0) :
    List.TFAE
      [symmMap _ _ _ f = f,
        (symmMap _ _ _).symm f = f,
        f.real = LinearMap.adjoint f,
        ∀ x y : B, counit (f x * y) = (counit (x * f y) : ℂ)] :=
by
  tfae_have 1 ↔ 2
  · rw [← LinearEquiv.eq_symm_apply, eq_comm]
  tfae_have 2 ↔ 3
  · rw [symmMap_symm_apply, LinearMap.real_inj_eq, LinearMap.real_real, eq_comm]
  tfae_have 3 → 4
  · intro h x y
    calc
      counit (f x * y) = ⟪star (f x), y⟫_ℂ := by
        rw [QuantumSet.inner_eq_counit, star_star, gns, hb.modAut_zero,
          AlgEquiv.one_apply]
      _ = ⟪f.real (star x), y⟫_ℂ := by simp_rw [LinearMap.real_apply, star_star]
      _ = ⟪LinearMap.adjoint f (star x), y⟫_ℂ := by rw [h]
      _ = ⟪star x, f y⟫_ℂ := by rw [LinearMap.adjoint_inner_left]
      _ = counit (x * f y) := by rw [hB.inner_eq_counit, star_star, gns,
        hb.modAut_zero, AlgEquiv.one_apply]
  tfae_have 4 → 3
  · intro h
    rw [LinearMap.ext_iff_inner_map]
    intro u
    rw [LinearMap.adjoint_inner_left]
    nth_rw 2 [hB.inner_eq_counit]
    simp only [gns, hb.modAut_zero, AlgEquiv.one_apply, hB.inner_eq_counit]
    rw [← h, LinearMap.real_apply, star_star]
  tfae_finish

theorem commute_real_real {R A : Type _} [Semiring R] [StarRing R] [AddCommMonoid A] [Module R A]
    [StarAddMonoid A] [StarModule R A] (f g : A →ₗ[R] A) :
    Commute (f.real : A →ₗ[R] A) (g.real : A →ₗ[R] A) ↔ Commute f g := by
  simp_rw [Commute, SemiconjBy, LinearMap.mul_eq_comp, ← LinearMap.real_comp, ←
    LinearMap.real_inj_eq]

theorem QuantumSet.modAut_real (r : ℝ) :
    (ha.modAut r).toLinearMap.real = (ha.modAut (-r)).toLinearMap :=
by
  rw [LinearMap.ext_iff]
  intro
  simp_rw [LinearMap.real_apply, AlgEquiv.toLinearMap_apply, ha.modAut_star, star_star]

theorem _root_.AlgEquiv.linearMap_comp_eq_iff {R E₁ E₂ E₃ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
    [AddCommMonoid E₃] [Algebra R E₁] [Algebra R E₂] [Module R E₃]
    (f : E₁ ≃ₐ[R] E₂) (x : E₂ →ₗ[R] E₃) (y : E₁ →ₗ[R] E₃) :
    x ∘ₗ f.toLinearMap = y ↔ x = y ∘ₗ f.symm.toLinearMap :=
by aesop
theorem _root_.AlgEquiv.comp_linearMap_eq_iff
  {R E₁ E₂ E₃ : Type _} [CommSemiring R] [Semiring E₁] [Semiring E₂]
  [AddCommMonoid E₃] [Algebra R E₁] [Algebra R E₂] [Module R E₃]
  (f : E₁ ≃ₐ[R] E₂) (x : E₃ →ₗ[R] E₁) (y : E₃ →ₗ[R] E₂) :
  f.toLinearMap ∘ₗ x = y ↔ x = f.symm.toLinearMap ∘ₗ y :=
by aesop

theorem linearMap_commute_modAut_pos_neg (r : ℝ) (x : B →ₗ[ℂ] B) :
    Commute x (hb.modAut r).toLinearMap ↔
      Commute x (hb.modAut (-r)).toLinearMap :=
  by
  simp_rw [Commute, SemiconjBy, LinearMap.mul_eq_comp]
  rw [AlgEquiv.linearMap_comp_eq_iff, ← QuantumSet.modAut_symm]
  nth_rw 1 [← AlgEquiv.comp_linearMap_eq_iff]
  rw [eq_comm]
  simp_rw [LinearMap.comp_assoc]

theorem symmMap_apply_eq_symmMap_symm_apply_iff
  (f : A →ₗ[ℂ] B) :
    symmMap ℂ _ _ f = (symmMap ℂ _ _).symm f ↔
      f ∘ₗ (ha.modAut (2*hA.k + 1)).toLinearMap = (hb.modAut (2 * hB.k + 1)).toLinearMap ∘ₗ f :=
  by
  rw [symmMap_apply, symmMap_symm_apply, LinearMap.adjoint_real_eq]
  simp_rw [@eq_comm _ (LinearMap.adjoint _), AlgEquiv.comp_linearMap_eq_iff,
    neg_sub_left, QuantumSet.modAut_symm]
  nth_rw 1 [← QuantumSet.modAut_isSelfAdjoint]
  nth_rw 2 [← QuantumSet.modAut_isSelfAdjoint]
  simp_rw [LinearMap.star_eq_adjoint, ← LinearMap.adjoint_comp,
    Function.Injective.eq_iff (LinearEquiv.injective _)]
  nth_rw 1 [LinearMap.real_inj_eq]
  simp only [LinearMap.real_comp, LinearMap.real_real, QuantumSet.modAut_real]
  rw [eq_comm]
  ring_nf

theorem Psi.real_apply (r₁ r₂ : ℝ) (f : A →ₗ[ℂ] B) :
    hA.Psi r₁ r₂ f.real =
      ((hb.modAut (2 * r₁)).toLinearMap ⊗ₘ
        ((ha.modAut (1 - 2 * (r₂ - hA.k))).op.toLinearMap))
      (star (hA.Psi r₁ r₂ f)) :=
by
  suffices
    ∀ (a : B) (b : A),
      hA.Psi r₁ r₂ (LinearMap.real |a⟩⟨b|) =
        ((hb.modAut (2 * r₁)).toLinearMap ⊗ₘ
            (ha.modAut (1 - 2 * (r₂ - hA.k))).op.toLinearMap)
          (star (hA.Psi r₁ r₂ |a⟩⟨b|))
    by
    obtain ⟨α, β, rfl⟩ := f.exists_sum_rankOne
    letI ttt : StarAddMonoid (B ⊗[ℂ] Aᵐᵒᵖ) := by infer_instance
    simp only [_root_.map_sum, LinearMap.real_sum, map_sum, star_sum, this]
  intro a b
  simp_rw [rankOne_real, hA.Psi_apply, hA.Psi_toFun_apply,
    star_tmul, map_tmul, AlgEquiv.toLinearMap_apply, AlgEquiv.op_apply_apply, ←
    MulOpposite.op_star, MulOpposite.unop_op, star_star, starAlgebra.modAut_star,
    QuantumSet.modAut_apply_modAut, star_star, neg_sub,
    sub_neg_eq_add]
  ring_nf

-- set_option maxHeartbeats 700000 in
-- set_option synthInstance.maxHeartbeats 0 in
theorem Psi.adjoint_apply (r₁ r₂ : ℝ) (f : A →ₗ[ℂ] B) :
    hB.Psi r₁ r₂ (LinearMap.adjoint f) =
      ((ha.modAut (r₁ - r₂)).toLinearMap ⊗ₘ
          ((hb.modAut (r₁ - r₂)).op.toLinearMap))
        (tenSwap (star (hA.Psi r₁ r₂ f))) :=
  by
  suffices
    ∀ (a : B) (b : A),
      hB.Psi r₁ r₂ (LinearMap.adjoint ↑|a⟩⟨b|) =
        ((ha.modAut (r₁ - r₂)).toLinearMap ⊗ₘ
            (hb.modAut (r₁ - r₂)).op.toLinearMap )
          (tenSwap (star (hA.Psi r₁ r₂ |a⟩⟨b|)))
    by
    obtain ⟨α, β, rfl⟩ := f.exists_sum_rankOne
    simp only [map_sum, star_sum, this]
  intro a b
  simp_rw [ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint, QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply,
    star_tmul, ← MulOpposite.op_star, tenSwap_apply', star_star, map_tmul,
    AlgEquiv.toLinearMap_apply, AlgEquiv.op_apply_apply, MulOpposite.unop_op,
    starAlgebra.modAut_star, QuantumSet.modAut_apply_modAut,
    sub_eq_add_neg, add_assoc, add_neg_cancel_comm_assoc, neg_add_self, add_zero]

theorem Psi.symmMap_apply (r₁ r₂ : ℝ) (f : A →ₗ[ℂ] B) :
    hB.Psi r₁ r₂ (symmMap _ _ _ f) =
      ((ha.modAut (r₁ + r₂ - 1 - (2 * hA.k))).toLinearMap ⊗ₘ
          (hb.modAut (-r₁ - r₂)).op.toLinearMap)
        (tenSwap (hA.Psi r₁ r₂ f)) :=
  by
  simp_rw [← LinearEquiv.coe_coe, ← LinearMap.comp_apply]
  revert f
  simp_rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, symmMap_rankOne_apply,
    QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply,
    tenSwap_apply', map_tmul, AlgEquiv.toLinearMap_apply, AlgEquiv.op_apply_apply,
    MulOpposite.unop_op, starAlgebra.modAut_star,
    QuantumSet.modAut_apply_modAut, star_star, sub_eq_add_neg,
    neg_add_cancel_comm, add_assoc]
  ring_nf

theorem Psi.symmMap_symm_apply (r₁ r₂ : ℝ) (f : A →ₗ[ℂ] B) :
    hB.Psi r₁ r₂ ((symmMap _ _ _).symm f) =
      ((ha.modAut (r₁ + r₂)).toLinearMap ⊗ₘ
          (hb.modAut (1 - r₁ - r₂ + (2 * hB.k))).op.toLinearMap)
        (tenSwap (hA.Psi r₁ r₂ f)) :=
by
  simp_rw [← LinearEquiv.coe_coe, ← LinearMap.comp_apply]
  revert f
  simp_rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, symmMap_symm_rankOne_apply,
    QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply,
    tenSwap_apply', map_tmul, AlgEquiv.toLinearMap_apply, AlgEquiv.op_apply_apply,
    MulOpposite.unop_op, starAlgebra.modAut_star,
    QuantumSet.modAut_apply_modAut, star_star, sub_eq_add_neg, add_assoc]
  ring_nf

theorem symmMap_apply_adjoint (x : A →ₗ[ℂ] B) :
    LinearMap.adjoint (symmMap ℂ A _ x)
      = ((symmMap ℂ _ _).symm) (LinearMap.adjoint x) :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp_rw [map_sum, ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint,
    symmMap_symm_apply, symmMap_apply, ContinuousLinearMap.linearMap_adjoint,
    rankOne_adjoint, LinearMap.adjoint_adjoint]

theorem symmMap_comp {C : Type*} [starAlgebra C] [QuantumSet C]
  (x : A →ₗ[ℂ] B) (y : C →ₗ[ℂ] A) :
  symmMap ℂ _ _ (x ∘ₗ y) = (symmMap ℂ _ _ y) ∘ₗ (symmMap ℂ _ _ x) :=
by
  simp_rw [symmMap_apply, LinearMap.real_comp, LinearMap.adjoint_comp]
