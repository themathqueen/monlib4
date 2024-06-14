/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.QuantumGraph.Nontracial

#align_import quantum_graph.example

/-!
  # Basic examples on quantum adjacency matrices

  This file contains elementary examples of quantum adjacency matrices, such as the complete graph and the trivial graph.
-/


-- import quantum_graph.basic
-- import quantum_graph.basic
open TensorProduct Matrix

open scoped TensorProduct BigOperators Kronecker Matrix Functional

variable {p : Type _} [Fintype p] [DecidableEq p] {n : p → Type _} [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)]
  {p₂ : Type*} [Fintype p₂] [DecidableEq p₂] {n₂ : p₂ → Type*} [∀ i, Fintype (n₂ i)]
  [∀ i, DecidableEq (n₂ i)]

local notation "ℍ" => PiMat ℂ p n
local notation "ℍ₂" => PiMat ℂ p₂ n₂

-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation "l(" x ")" => x →ₗ[ℂ] x

variable {φ : Π i : p, Module.Dual ℂ (Matrix (n i) (n i) ℂ)} {ψ : Π i, Module.Dual ℂ (Matrix (n₂ i) (n₂ i) ℂ)}

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  LinearEquiv.toLinearMap (TensorProduct.assoc ℂ ℍ ℍ ℍ)

local notation "υ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.assoc ℂ ℍ ℍ ℍ))

local notation "ϰ" =>
  LinearEquiv.toLinearMap ((TensorProduct.comm ℂ ℍ ℂ))

local notation "ϰ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ ℍ ℂ))

local notation "τ" =>
  LinearEquiv.toLinearMap (TensorProduct.lid ℂ ℍ)

local notation "τ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ ℍ))

local notation "id" => (1 : ℍ →ₗ[ℂ] ℍ)

noncomputable def Qam.completeGraph (E₁ E₂ : Type _) [One E₁] [One E₂] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] :
    E₂ →ₗ[ℂ] E₁ :=
  |(1 : E₁)⟩⟨(1 : E₂)|

theorem Qam.completeGraph_eq {E₁ E₂ : Type _} [One E₁] [One E₂] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] :
    Qam.completeGraph E₁ E₂ = |(1 : E₁)⟩⟨(1 : E₂)| :=
  rfl

variable {A B : Type*} [hA : QuantumSet A] [hB : QuantumSet B]

theorem Qam.completeGraph_eq' :
  Qam.completeGraph A B =
    Algebra.linearMap ℂ A ∘ₗ Coalgebra.counit :=
by
  -- rw [Coalgebra.counit_eq_unit_adjoint]
  rw [LinearMap.ext_iff]
  intro x
  simp_rw [Qam.completeGraph_eq, ContinuousLinearMap.coe_coe, LinearMap.comp_apply, rankOne_apply,
    QuantumSet.inner_eq_counit, star_one, one_mul]
  simp only [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]

open scoped schurMul
theorem Qam.Nontracial.CompleteGraph.qam :
  ((Qam.completeGraph A B) •ₛ (Qam.completeGraph A B)) = Qam.completeGraph A B :=
schurMul_one_one_left _

lemma Qam.Nontracial.CompleteGraph.adjoint_eq {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂]
    [FiniteDimensional ℂ E₁] [FiniteDimensional ℂ E₂]
    [IsScalarTower ℂ E₁ E₁] [IsScalarTower ℂ E₂ E₂]
    [SMulCommClass ℂ E₁ E₁] [SMulCommClass ℂ E₂ E₂] :
  LinearMap.adjoint (Qam.completeGraph E₁ E₂) = Qam.completeGraph E₂ E₁ :=
rankOneLm_adjoint _ _

theorem Qam.Nontracial.CompleteGraph.isSelfAdjoint {E : Type _} [One E] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] : _root_.IsSelfAdjoint (Qam.completeGraph E E) := by
  simp_rw [_root_.IsSelfAdjoint, Qam.completeGraph, LinearMap.star_eq_adjoint, ←
    rankOneLm_eq_rankOne, rankOneLm_adjoint]

theorem Qam.Nontracial.CompleteGraph.isReal :
    (Qam.completeGraph A B).IsReal := by
  simp_rw [Qam.completeGraph, LinearMap.isReal_iff, rankOne_real, star_one,
    QuantumSet.modAut_map_one]

theorem Qam.Nontracial.CompleteGraph.symm_eq :
  symmMap ℂ _ _ (Qam.completeGraph A B) = Qam.completeGraph B A :=
by simp_rw [Qam.completeGraph, symmMap_rankOne_apply, star_one, hB.modAut_map_one]
theorem Qam.Nontracial.CompleteGraph.is_symm :
  symmMap ℂ _ _ (Qam.completeGraph A A) = Qam.completeGraph A A :=
Qam.Nontracial.CompleteGraph.symm_eq

theorem Qam.Nontracial.CompleteGraph.is_reflexive :
  (Qam.completeGraph A A) •ₛ 1 = 1 :=
by
  obtain ⟨α, β, hαβ⟩ := (1 : l(A)).exists_sum_rankOne
  nth_rw 1 [hαβ]
  simp_rw [map_sum, Qam.completeGraph, schurMul.apply_rankOne, one_mul, ← hαβ]

theorem LinearMap.mul'_comp_mul'_adjoint_of_delta_form {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    (hφ : φ.IsFaithfulPosMap) (hφ₂ : φ.matrix⁻¹.trace = δ) :
  LinearMap.mul' ℂ (Matrix p p ℂ) ∘ₗ Coalgebra.comul = δ • 1 :=
by rw [Coalgebra.comul_eq_mul_adjoint, Qam.Nontracial.mul_comp_mul_adjoint, hφ₂]

theorem LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  m ∘ₗ Coalgebra.comul = δ • id :=
by
  rw [Coalgebra.comul_eq_mul_adjoint,
    LinearMap.pi_mul'_comp_mul'_adjoint_eq_smul_id_iff δ]
  exact hφ₂

theorem Qam.Nontracial.delta_ne_zero [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    [hφ : φ.IsFaithfulPosMap] (hφ₂ : φ.matrix⁻¹.trace = δ) : δ ≠ 0 :=
  by
  rw [← hφ₂]
  exact Matrix.PosDef.trace_ne_zero (PosDef.inv hφ.matrixIsPosDef)

theorem Pi.Qam.Nontracial.delta_ne_zero [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) : δ ≠ 0 :=
  by
  have : ∀ i, (φ i).matrix⁻¹.trace ≠ 0 := by
    intro i
    exact Matrix.PosDef.trace_ne_zero (PosDef.inv (hφ i).matrixIsPosDef)
  have this' : δ ≠ 0 ↔ ∀ i, (φ i).matrix⁻¹.trace ≠ 0 :=
    by
    constructor <;> rintro h i
    · exact this _
    · rw [i] at hφ₂
      let j : p := Classical.arbitrary p
      exact (h j) (hφ₂ j)
  rw [this']
  exact this

@[instance]
noncomputable def Qam.Nontracial.Mul'CompMul'Adjoint.invertible [Nonempty p]
    {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ} [hφ : φ.IsFaithfulPosMap]
    (hφ₂ : φ.matrix⁻¹.trace = δ) :
    @Invertible l(Matrix p p ℂ) { mul := (· ∘ₗ ·) } { one := 1 }
      (LinearMap.mul' ℂ (Matrix p p ℂ) ∘ₗ Coalgebra.comul) :=
  by
  rw [LinearMap.mul'_comp_mul'_adjoint_of_delta_form _ hφ₂]
  apply IsUnit.invertible
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_smul _ _ _, LinearMap.one_eq_id,
    LinearMap.ker_id]
  exact Qam.Nontracial.delta_ne_zero hφ₂

-- set_option maxHeartbeats 0 in
@[instance]
noncomputable def Pi.Qam.Nontracial.Mul'CompMul'Adjoint.invertible [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  @Invertible (ℍ →ₗ[ℂ] ℍ) { mul := (· ∘ₗ ·) } { one := id } (m ∘ₗ Coalgebra.comul) :=
by
  rw [LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form _ hφ₂]
  apply IsUnit.invertible
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_smul _ _ _, LinearMap.one_eq_id,
    LinearMap.ker_id]
  exact Pi.Qam.Nontracial.delta_ne_zero hφ₂

noncomputable def Qam.trivialGraph [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    (hφ : φ.IsFaithfulPosMap) (hφ₂ : φ.matrix⁻¹.trace = δ) : l(Matrix p p ℂ) :=
  by
  letI := hφ
  letI := Qam.Nontracial.Mul'CompMul'Adjoint.invertible hφ₂
  exact ⅟ (LinearMap.mul' ℂ (Matrix p p ℂ) ∘ₗ Coalgebra.comul)

set_option linter.unusedVariables false in
@[nolint unusedArguments]
noncomputable def Pi.Qam.trivialGraph [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) : l(ℍ) :=
(Pi.Qam.Nontracial.Mul'CompMul'Adjoint.invertible hφ₂).invOf
-- (⅟ (m ∘ₗ (LinearMap.adjoint m)))

-- set_option synthInstance.maxHeartbeats 0 in
theorem Qam.trivialGraph_eq [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
    Qam.trivialGraph hφ hφ₂ = δ⁻¹ • (1 : l(Matrix p p ℂ)) :=
  by
  letI := @Qam.Nontracial.Mul'CompMul'Adjoint.invertible p _ _ _ φ δ hφ hφ₂
  simp_rw [Qam.trivialGraph]
  apply invOf_eq_right_inv
  rw [LinearMap.mul'_comp_mul'_adjoint_of_delta_form _ hφ₂, smul_mul_smul, one_mul, mul_inv_cancel,
    one_smul]
  · exact Qam.Nontracial.delta_ne_zero hφ₂

-- set_option synthInstance.maxHeartbeats 0 in
-- set_option maxHeartbeats 0 in
theorem Pi.Qam.trivialGraph_eq [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
    Pi.Qam.trivialGraph hφ hφ₂ = δ⁻¹ • (1 : ℍ →ₗ[ℂ] ℍ) :=
  by
  letI := @Pi.Qam.Nontracial.Mul'CompMul'Adjoint.invertible p _ _ n _ _ φ _ _ δ _ hφ₂
  unfold trivialGraph
  apply invOf_eq_right_inv
  rw [LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form _ hφ₂, smul_mul_smul, one_mul, mul_inv_cancel,
    one_smul]
  · exact Pi.Qam.Nontracial.delta_ne_zero hφ₂

set_option synthInstance.maxHeartbeats 30000 in
theorem Qam.Nontracial.TrivialGraph.qam [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
    (Qam.trivialGraph hφ hφ₂) •ₛ (Qam.trivialGraph hφ hφ₂) = Qam.trivialGraph hφ hφ₂ :=
  by
  rw [Qam.trivialGraph_eq]
  simp_rw [_root_.map_smul, LinearMap.smul_apply, smul_smul, schurMul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [TensorProduct.map_one, LinearMap.one_eq_id, LinearMap.id_comp,
    LinearMap.mul'_comp_mul'_adjoint_of_delta_form _ hφ₂, smul_smul, mul_assoc]
  rw [inv_mul_cancel _, mul_one, LinearMap.one_eq_id]
  exact Qam.Nontracial.delta_ne_zero hφ₂

-- -- set_option synthInstance.maxHeartbeats 50000 in
-- theorem Pi.Qam.Nontracial.TrivialGraph.qam [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
--     [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
--     (Pi.Qam.trivialGraph hφ hφ₂) •ₛ (Pi.Qam.trivialGraph hφ hφ₂) =
--       (Pi.Qam.trivialGraph hφ hφ₂) :=
--   by
--   rw [Pi.Qam.trivialGraph_eq]
--   simp_rw [_root_.map_smul, LinearMap.smul_apply, smul_smul, schurMul]
--   simp only [LinearMap.coe_mk, AddHom.coe_mk]
--   simp_rw [TensorProduct.map_one, LinearMap.one_eq_id, LinearMap.id_comp,
--     LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul, mul_assoc]
--   rw [inv_mul_cancel _, mul_one, LinearMap.one_eq_id]
--   exact Pi.Qam.Nontracial.delta_ne_zero hφ₂

theorem Qam.Nontracial.TrivialGraph.qam.is_self_adjoint [Nonempty p]
    {φ : Module.Dual ℂ (Matrix p p ℂ)} [hφ : φ.IsFaithfulPosMap] {δ : ℂ}
    (hφ₂ : φ.matrix⁻¹.trace = δ) : LinearMap.adjoint (Qam.trivialGraph hφ hφ₂) = Qam.trivialGraph hφ hφ₂ :=
  by
  simp_rw [Qam.trivialGraph_eq, LinearMap.adjoint_smul, LinearMap.adjoint_one, starRingEnd_apply,
    star_inv', ← starRingEnd_apply]
  congr 2
  rw [← hφ₂, starRingEnd_apply, trace_star, hφ.matrixIsPosDef.1.inv.eq]

theorem Pi.Qam.Nontracial.TrivialGraph.qam.is_self_adjoint [Nonempty p] [∀ i, Nontrivial (n i)]
    {δ : ℂ} [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
    LinearMap.adjoint (Pi.Qam.trivialGraph hφ hφ₂) = Pi.Qam.trivialGraph hφ hφ₂ :=
  by
  simp_rw [Pi.Qam.trivialGraph_eq, LinearMap.adjoint_smul, LinearMap.adjoint_one, starRingEnd_apply,
    star_inv', ← starRingEnd_apply]
  congr 2
  have : ∀ i, ((φ i).matrix⁻¹.trace.re : ℂ) = (φ i).matrix⁻¹.trace :=
    by
    intro i
    rw [← Complex.conj_eq_iff_re, starRingEnd_apply, trace_star,
      (hφ i).matrixIsPosDef.1.inv.eq]
  simp_rw [hφ₂] at this
  rw [← this (Nonempty.some (by infer_instance)), Complex.conj_ofReal]

set_option synthInstance.maxHeartbeats 50000 in
theorem Qam.Nontracial.trivialGraph [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
    (Qam.trivialGraph hφ hφ₂) •ₛ 1 = 1 :=
  by
  rw [Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply]
  simp only [schurMul, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [TensorProduct.map_one, LinearMap.one_eq_id,
    LinearMap.id_comp, LinearMap.mul'_comp_mul'_adjoint_of_delta_form _ hφ₂, smul_smul,
    inv_mul_cancel (Qam.Nontracial.delta_ne_zero hφ₂), one_smul, LinearMap.one_eq_id]

-- set_option synthInstance.maxHeartbeats 50000 in
-- theorem Pi.Qam.Nontracial.trivialGraph [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
--     [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
--     (Pi.Qam.trivialGraph hφ hφ₂) •ₛ 1 = (1 : ℍ →ₗ[ℂ] ℍ) :=
--   by
--   rw [Pi.Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply]
--   simp_rw [schurIdempotent_apply_apply, TensorProduct.map_one, LinearMap.one_eq_id,
--     LinearMap.id_comp, LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul,
--     inv_mul_cancel (Pi.Qam.Nontracial.delta_ne_zero hφ₂), one_smul, LinearMap.one_eq_id]

theorem Qam.refl_idempotent_one_one_of_delta [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
    (1 : l(Matrix p p ℂ)) •ₛ (1 : l(Matrix p p ℂ)) = δ • (1 : l(Matrix p p ℂ)) := by
  simp_rw [schurMul_apply_apply, TensorProduct.map_one, LinearMap.one_comp,
    LinearMap.mul'_comp_mul'_adjoint_of_delta_form _ hφ₂]

-- theorem Pi.Qam.refl_idempotent_one_one_of_delta [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
--     [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
--     schurIdempotent (1 : l(ℍ)) (1 : l(ℍ)) = δ • (1 : l(ℍ)) := by
--   simp_rw [schurIdempotent_apply_apply, TensorProduct.map_one, LinearMap.one_comp,
--     LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂]

-- set_option synthInstance.maxHeartbeats 50000 in
theorem Qam.Lm.Nontracial.is_unreflexive_iff_reflexive_add_one [Nonempty p]
    {φ : Module.Dual ℂ (Matrix p p ℂ)} [hφ : φ.IsFaithfulPosMap] {δ : ℂ}
    (hφ₂ : φ.matrix⁻¹.trace = δ) (x : l(Matrix p p ℂ)) :
    x •ₛ 1 = 0 ↔ (δ⁻¹ • (x + 1)) •ₛ 1 = 1 :=
  by
  simp_rw [_root_.map_smul, LinearMap.smul_apply, _root_.map_add, LinearMap.add_apply,
    Qam.refl_idempotent_one_one_of_delta hφ₂, smul_add, smul_smul,
    inv_mul_cancel (Qam.Nontracial.delta_ne_zero hφ₂), one_smul, add_left_eq_self]
  rw [smul_eq_zero_iff_right (inv_ne_zero (Qam.Nontracial.delta_ne_zero hφ₂))]

-- theorem Pi.Qam.Lm.Nontracial.is_unreflexive_iff_reflexive_add_one [Nonempty p]
--     [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, (φ i).IsFaithfulPosMap]
--     (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) (x : l(ℍ)) :
--     schurIdempotent x 1 = 0 ↔ schurIdempotent (δ⁻¹ • (x + 1)) 1 = 1 :=
--   by
--   simp_rw [_root_.map_smul, LinearMap.smul_apply, _root_.map_add, LinearMap.add_apply,
--     Pi.Qam.refl_idempotent_one_one_of_delta hφ₂, smul_add, smul_smul,
--     inv_mul_cancel (Pi.Qam.Nontracial.delta_ne_zero hφ₂), one_smul, add_left_eq_self]
--   rw [smul_eq_zero_iff_right (inv_ne_zero (Pi.Qam.Nontracial.delta_ne_zero hφ₂))]

theorem Qam.refl_idempotent_completeGraph_left
  (x : A →ₗ[ℂ] B) : (Qam.completeGraph B A) •ₛ x = x :=
schurMul_one_one_left _

theorem Qam.refl_idempotent_completeGraph_right (x : A →ₗ[ℂ] B) :
  x •ₛ (Qam.completeGraph B A) = x :=
schurMul_one_one_right _

noncomputable def Qam.complement' {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₁]
    [FiniteDimensional ℂ E₂] [IsScalarTower ℂ E₁ E₁] [IsScalarTower ℂ E₂ E₂] [SMulCommClass ℂ E₁ E₁]
    [SMulCommClass ℂ E₂ E₂]
  (x : E₂ →ₗ[ℂ] E₁) : E₂ →ₗ[ℂ] E₁ :=
Qam.completeGraph E₁ E₂ - x

theorem Qam.Nontracial.Complement'.qam
    (x : A →ₗ[ℂ] B) :
    x •ₛ x = x ↔
      (Qam.complement' x) •ₛ (Qam.complement' x) = Qam.complement' x :=
  by
  simp only [Qam.complement', _root_.map_sub, LinearMap.sub_apply,
    Qam.refl_idempotent_completeGraph_left, Qam.refl_idempotent_completeGraph_right,
    Qam.Nontracial.CompleteGraph.qam]
  simp only [sub_right_inj, sub_eq_self]
  simp only [sub_eq_zero, @eq_comm _ x]

theorem Qam.Nontracial.Complement'.qam.isReal {φ : Module.Dual ℂ (Matrix p p ℂ)}
    {ψ : Module.Dual ℂ (Matrix p₂ p₂ ℂ)}
    [hφ : φ.IsFaithfulPosMap] [hψ : ψ.IsFaithfulPosMap]
    (x : (Matrix p p ℂ) →ₗ[ℂ] (Matrix p₂ p₂ ℂ)) : x.IsReal ↔ (Qam.complement' x).IsReal :=
  by
  simp only [Qam.complement', LinearMap.isReal_iff, LinearMap.real_sub,
    (LinearMap.isReal_iff _).mp (Qam.Nontracial.CompleteGraph.isReal)]
  simp only [sub_right_inj]

-- theorem Pi.Qam.Nontracial.Complement'.Qam.isReal [hφ : ∀ i, (φ i).IsFaithfulPosMap]
--   [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
--   (x : ℍ →ₗ[ℂ] ℍ₂) : x.IsReal ↔ (Qam.complement' x).IsReal :=
--   by
--   simp only [Qam.complement', LinearMap.isReal_iff, LinearMap.real_sub,
--     (LinearMap.isReal_iff _).mp (Qam.Nontracial.CompleteGraph.isReal)]
--   simp only [sub_right_inj]

theorem Qam.complement'_complement' {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₁]
    [FiniteDimensional ℂ E₂] [IsScalarTower ℂ E₁ E₁] [IsScalarTower ℂ E₂ E₂] [SMulCommClass ℂ E₁ E₁]
    [SMulCommClass ℂ E₂ E₂]
    (x : E₁ →ₗ[ℂ] E₂) : Qam.complement' (Qam.complement' x) = x :=
  sub_sub_cancel _ _

theorem Qam.Nontracial.Complement'.ir_reflexive
    (x : l(A)) (α : Prop) [Decidable α] :
    x •ₛ (1 : l(A)) = ite α (1 : l(A)) (0 : l(A)) ↔
      (Qam.complement' x) •ₛ (1 : l(A)) = ite α (0 : l(A)) (1 : l(A)) :=
by
  simp_rw [Qam.complement', _root_.map_sub, LinearMap.sub_apply,
    Qam.refl_idempotent_completeGraph_left]
  by_cases h : α <;> simp_rw [h]
  · simp_rw [if_true, sub_eq_zero, eq_comm]
  · simp_rw [if_false, sub_eq_self]

@[reducible]
class QamReflexive (x : l(A)) : Prop :=
toQam : x •ₛ x = x
toRefl : x •ₛ 1 = 1

lemma QamReflexive_iff (x : l(A)) :
    QamReflexive x ↔ x •ₛ x = x ∧ x •ₛ 1 = 1 :=
⟨λ h => ⟨h.toQam, h.toRefl⟩, λ h => ⟨h.1, h.2⟩⟩

@[reducible]
class QamIrreflexive (x : l(A)) : Prop :=
toQam : x •ₛ x = x
toIrrefl : x •ₛ 1 = 0

lemma QamIrreflexive_iff (x : l(A)) :
    QamIrreflexive x ↔ x •ₛ x = x ∧ x •ₛ 1 = 0 :=
⟨λ h => ⟨h.toQam, h.toIrrefl⟩, λ h => ⟨h.1, h.2⟩⟩

theorem Qam.complement'_is_irreflexive_iff
    (x : l(A)) : QamIrreflexive (Qam.complement' x) ↔ QamReflexive x :=
  by
  have := Qam.Nontracial.Complement'.ir_reflexive x True
  simp_rw [if_true] at this
  rw [QamReflexive_iff, QamIrreflexive_iff, ← Qam.Nontracial.Complement'.qam]
  simp_rw [this]

theorem Qam.complement'_is_reflexive_iff
    (x : l(A)) : QamReflexive (Qam.complement' x) ↔ QamIrreflexive x :=
  by
  have := Qam.Nontracial.Complement'.ir_reflexive x False
  simp_rw [if_false] at this
  rw [QamReflexive_iff, QamIrreflexive_iff, ← Qam.Nontracial.Complement'.qam, this]

noncomputable def Qam.complement'' [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    (hφ : φ.IsFaithfulPosMap) (hφ₂ : φ.matrix⁻¹.trace = δ) (x : l(Matrix p p ℂ)) :
    l(Matrix p p ℂ) :=
  x - Qam.trivialGraph hφ hφ₂

noncomputable def Pi.Qam.complement'' [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) (x : l(ℍ)) :
    l(ℍ) :=
  x - Pi.Qam.trivialGraph hφ hφ₂

theorem single_schurIdempotent_real {φ : Module.Dual ℂ (Matrix p p ℂ)}
  [φ.IsFaithfulPosMap] (x y : l(Matrix p p ℂ)) :
    (x •ₛ y).real = y.real •ₛ x.real :=
schurMul_real _ _

theorem schurIdempotent_reflexive_of_isReal {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] {x : l(Matrix p p ℂ)} (hx : x.IsReal) :
    x •ₛ 1 = 1 ↔ 1 •ₛ x = 1 :=
by
  rw [LinearMap.real_inj_eq, single_schurIdempotent_real, LinearMap.real_one, x.isReal_iff.mp hx]

-- theorem Pi.schurIdempotent_reflexive_of_isReal [hφ : ∀ i, (φ i).IsFaithfulPosMap] {x : l(ℍ)}
--     (hx : x.IsReal) : schurIdempotent x 1 = 1 ↔ schurIdempotent 1 x = 1 := by
--   rw [LinearMap.real_inj_eq, schurIdempotent_real, LinearMap.real_one, x.isReal_iff.mp hx]

theorem Qam.complement''_is_irreflexive_iff [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    [hφ : φ.IsFaithfulPosMap] (hφ₂ : φ.matrix⁻¹.trace = δ) {x : l(Matrix p p ℂ)}
    (hx : x.IsReal) : QamIrreflexive (Qam.complement'' hφ hφ₂ x) ↔ QamReflexive x :=
  by
  rw [QamReflexive_iff, QamIrreflexive_iff]
  have t1 := Qam.Nontracial.TrivialGraph.qam hφ₂
  have t2 := Qam.Nontracial.trivialGraph hφ₂
  have t3 : (Qam.complement'' hφ hφ₂ x) •ₛ 1 = 0 ↔ x •ₛ 1 = 1 := by
    simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t2, sub_eq_zero]
  rw [t3]
  simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t1, sub_sub]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine' ⟨_, h2⟩
  all_goals
    simp only [Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply, h2,
      (schurIdempotent_reflexive_of_isReal hx).mp h2, sub_self, add_zero, sub_left_inj] at h1 ⊢
    exact h1

-- theorem Pi.Qam.complement''_is_irreflexive_iff [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
--     [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)}
--     (hx : x.IsReal) : QamIrreflexive (Pi.Qam.complement'' hφ hφ₂ x) ↔ QamReflexive x :=
--   by
--   rw [QamReflexive_iff, QamIrreflexive_iff]
--   have t1 := @Pi.Qam.Nontracial.TrivialGraph.qam p _ _ n _ _ φ _ _ δ _ hφ₂
--   have t2 := @Pi.Qam.Nontracial.trivialGraph p _ _ n _ _ φ _ _ δ _ hφ₂
--   have t3 : schurIdempotent (Pi.Qam.complement'' hφ hφ₂ x) 1 = 0 ↔ schurIdempotent x 1 = 1 := by
--     simp_rw [Pi.Qam.complement'', map_sub, LinearMap.sub_apply, t2, sub_eq_zero]
--   rw [t3]
--   simp_rw [Pi.Qam.complement'', map_sub, LinearMap.sub_apply, t1, sub_sub]
--   constructor <;> rintro ⟨h1, h2⟩ <;> refine' ⟨_, h2⟩
--   all_goals
--     simp only [Pi.Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply, h2,
--       (Pi.schurIdempotent_reflexive_of_isReal hx).mp h2, sub_self, add_zero, sub_left_inj] at h1 ⊢
--     rw [h1]

noncomputable def Pi.Qam.irreflexiveComplement [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) (x : l(ℍ)) :
    l(ℍ) :=
  Qam.completeGraph ℍ ℍ - Pi.Qam.trivialGraph hφ hφ₂ - x

noncomputable def Pi.Qam.reflexiveComplement [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) (x : l(ℍ)) :
    l(ℍ) :=
  Qam.completeGraph ℍ ℍ + Pi.Qam.trivialGraph hφ hφ₂ - x

theorem Qam.Nontracial.trivialGraph.isReal [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
    (Qam.trivialGraph hφ hφ₂).IsReal :=
  by
  rw [LinearMap.isReal_iff, Qam.trivialGraph_eq, LinearMap.real_smul, LinearMap.real_one,
    starRingEnd_apply, star_inv']
  congr
  rw [← hφ₂]
  rw [trace_star, hφ.matrixIsPosDef.inv.1.eq]

theorem Pi.Qam.Nontracial.trivialGraph.isReal [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
    (Pi.Qam.trivialGraph hφ hφ₂).IsReal :=
  by
  rw [LinearMap.isReal_iff, Pi.Qam.trivialGraph_eq, LinearMap.real_smul, LinearMap.real_one,
    starRingEnd_apply, star_inv']
  congr
  rw [← hφ₂ (Nonempty.some (by infer_instance))]
  rw [trace_star, (hφ _).matrixIsPosDef.inv.1.eq]

-- theorem Pi.Qam.irreflexiveComplement.isReal [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
--     [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)}
--     (hx : x.IsReal) : (Pi.Qam.irreflexiveComplement hφ hφ₂ x).IsReal := by
--   rw [LinearMap.isReal_iff, Pi.Qam.irreflexiveComplement, LinearMap.real_sub, LinearMap.real_sub,
--     (LinearMap.isReal_iff (Qam.completeGraph ℍ ℍ)).mp Pi.Qam.Nontracial.CompleteGraph.isReal,
--     (LinearMap.isReal_iff (Pi.Qam.trivialGraph hφ hφ₂)).mp
--       (Pi.Qam.Nontracial.trivialGraph.isReal hφ₂),
--     (LinearMap.isReal_iff x).mp hx]

-- theorem Pi.Qam.reflexiveComplement.isReal [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
--     [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)}
--     (hx : x.IsReal) : (Pi.Qam.reflexiveComplement hφ hφ₂ x).IsReal := by
--   rw [LinearMap.isReal_iff, Pi.Qam.reflexiveComplement, LinearMap.real_sub, LinearMap.real_add,
--     (LinearMap.isReal_iff (Qam.completeGraph ℍ ℍ)).mp Pi.Qam.Nontracial.CompleteGraph.isReal,
--     (LinearMap.isReal_iff (Pi.Qam.trivialGraph hφ hφ₂)).mp
--       (Pi.Qam.Nontracial.trivialGraph.isReal hφ₂),
--     (LinearMap.isReal_iff x).mp hx]

theorem Pi.Qam.irreflexiveComplement_irreflexiveComplement [Nonempty p] [∀ i, Nontrivial (n i)]
    {δ : ℂ} [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ)
    {x : l(ℍ)} : Pi.Qam.irreflexiveComplement hφ hφ₂ (Pi.Qam.irreflexiveComplement hφ hφ₂ x) = x :=
  sub_sub_cancel _ _

theorem Pi.Qam.reflexiveComplement_reflexiveComplement [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)} :
    Pi.Qam.reflexiveComplement hφ hφ₂ (Pi.Qam.reflexiveComplement hφ hφ₂ x) = x :=
  sub_sub_cancel _ _

theorem Pi.Qam.trivialGraph_reflexiveComplement_eq_completeGraph [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
    Pi.Qam.reflexiveComplement hφ hφ₂ (Pi.Qam.trivialGraph hφ hφ₂) = Qam.completeGraph ℍ ℍ :=
by simp_rw [reflexiveComplement, add_sub_cancel_right]

theorem Pi.Qam.completeGraph_reflexiveComplement_eq_trivialGraph [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
    Pi.Qam.reflexiveComplement hφ hφ₂ (Qam.completeGraph ℍ ℍ) = Pi.Qam.trivialGraph hφ hφ₂ :=
  add_sub_cancel_left _ _

theorem Qam.complement'_eq {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₁]
    [FiniteDimensional ℂ E₂] [IsScalarTower ℂ E₁ E₁] [IsScalarTower ℂ E₂ E₂] [SMulCommClass ℂ E₁ E₁]
    [SMulCommClass ℂ E₂ E₂] (a : E₂ →ₗ[ℂ] E₁) :
    Qam.complement' a = Qam.completeGraph E₁ E₂ - a :=
  rfl

-- theorem Pi.Qam.irreflexiveComplement_is_irreflexive_qam_iff_irreflexive_qam [Nonempty p]
--     [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, (φ i).IsFaithfulPosMap]
--     (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)} (hx : x.IsReal) :
--     QamIrreflexive (Pi.Qam.irreflexiveComplement hφ hφ₂ x) ↔ QamIrreflexive x :=
--   by
--   rw [Pi.Qam.irreflexiveComplement, sub_sub, ← Qam.complement'_eq,
--     Qam.complement'_is_irreflexive_iff, ← Pi.Qam.complement''_is_irreflexive_iff hφ₂,
--     Pi.Qam.complement'', add_sub_cancel']
--   ·
--     rw [LinearMap.isReal_iff, LinearMap.real_add, x.isReal_iff.mp hx,
--       (Pi.Qam.trivialGraph hφ hφ₂).isReal_iff.mp (Pi.Qam.Nontracial.trivialGraph.isReal hφ₂)]

-- theorem Pi.Qam.reflexive_complment_is_reflexive_qam_iff_reflexive_qam [Nonempty p]
--     [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, (φ i).IsFaithfulPosMap]
--     (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)} (hx : x.IsReal) :
--     QamReflexive (Pi.Qam.reflexiveComplement hφ hφ₂ x) ↔ QamReflexive x :=
--   by
--   rw [Pi.Qam.reflexiveComplement, ← sub_sub_eq_add_sub, ← Qam.complement'_eq,
--     Qam.complement'_is_reflexive_iff]
--   exact Pi.Qam.complement''_is_irreflexive_iff hφ₂ hx
