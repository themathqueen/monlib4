/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import QuantumGraph.Nontracial

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

local notation "ℍ" => ∀ i, Matrix (n i) (n i) ℂ

local notation "ℍ_" i => Matrix (n i) (n i) ℂ

-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation "l(" x ")" => x →ₗ[ℂ] x

variable {φ : ∀ i, Module.Dual ℂ (ℍ_ i)} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap]

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" => (TensorProduct.assoc ℂ ℍ ℍ ℍ : (ℍ ⊗[ℂ] ℍ) ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ)

local notation "υ⁻¹" =>
  ((TensorProduct.assoc ℂ ℍ ℍ ℍ).symm : ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ) ⊗[ℂ] ℍ)

local notation "ϰ" => (↑(TensorProduct.comm ℂ ℍ ℂ) : ℍ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] ℍ)

local notation "ϰ⁻¹" => ((TensorProduct.comm ℂ ℍ ℂ).symm : ℂ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℂ)

local notation "τ" => (TensorProduct.lid ℂ ℍ : ℂ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ)

local notation "τ⁻¹" => ((TensorProduct.lid ℂ ℍ).symm : ℍ →ₗ[ℂ] ℂ ⊗[ℂ] ℍ)

local notation "id" => (1 : ℍ →ₗ[ℂ] ℍ)

noncomputable def Qam.completeGraph (E : Type _) [One E] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : E →ₗ[ℂ] E :=
  |(1 : E)⟩⟨(1 : E)|

theorem Qam.completeGraph_eq {E : Type _} [One E] [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Qam.completeGraph E = |(1 : E)⟩⟨(1 : E)| :=
  rfl

theorem Qam.completeGraph_eq' {φ : Module.Dual ℂ (Matrix p p ℂ)} [hφ : Fact φ.IsFaithfulPosMap] :
    Qam.completeGraph (Matrix p p ℂ) =
      Algebra.linearMap ℂ (Matrix p p ℂ) ∘ₗ (Algebra.linearMap ℂ (Matrix p p ℂ)).adjoint :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp_rw [Qam.completeGraph_eq, ContinuousLinearMap.coe_coe, LinearMap.comp_apply, rankOne_apply,
    Nontracial.unit_adjoint_eq, Module.Dual.IsFaithfulPosMap.inner_eq, conj_transpose_one,
    Matrix.one_mul]
  rfl

theorem Pi.Qam.completeGraph_eq' [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] :
    Qam.completeGraph ℍ = η ∘ₗ η.adjoint :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp_rw [Qam.completeGraph_eq, ContinuousLinearMap.coe_coe, LinearMap.comp_apply, rankOne_apply,
    Nontracial.Pi.unit_adjoint_eq, Module.Dual.pi.IsFaithfulPosMap.inner_eq, star_one, one_mul]
  rfl

theorem Qam.Nontracial.CompleteGraph.qam {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] :
    schurIdempotent (Qam.completeGraph E) (Qam.completeGraph E) = Qam.completeGraph E := by
  rw [Qam.completeGraph, schurIdempotent.apply_rankOne, one_mul]

theorem Qam.Nontracial.CompleteGraph.isSelfAdjoint {E : Type _} [One E] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] : @IsSelfAdjoint _ _ (Qam.completeGraph E) := by
  simp_rw [_root_.is_self_adjoint, Qam.completeGraph, LinearMap.star_eq_adjoint, ←
    rankOneLm_eq_rankOne, rankOneLm_adjoint]

theorem Qam.Nontracial.CompleteGraph.isReal {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] : (Qam.completeGraph (Matrix p p ℂ)).IsReal := by
  rw [Qam.completeGraph, LinearMap.isReal_iff, rankOne_real_apply, conj_transpose_one,
    _root_.map_one]

theorem Qam.Nontracial.CompleteGraph.is_symm {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] :
    LinearEquiv.symmMap ℂ (Matrix p p ℂ) (Qam.completeGraph (Matrix p p ℂ)) =
      Qam.completeGraph (Matrix p p ℂ) :=
  by simp_rw [Qam.completeGraph, Qam.RankOne.symmetric_eq, conj_transpose_one, _root_.map_one]

theorem Pi.Qam.Nontracial.CompleteGraph.isReal [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] :
    (Qam.completeGraph ℍ).IsReal := by
  rw [Qam.completeGraph, ← rankOneLm_eq_rankOne, LinearMap.isReal_iff, Pi.rankOneLm_real_apply,
    star_one, _root_.map_one]

theorem Pi.Qam.Nontracial.CompleteGraph.is_symm [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] :
    LinearEquiv.symmMap ℂ ℍ (Qam.completeGraph ℍ) = Qam.completeGraph ℍ := by
  simp_rw [Qam.completeGraph, LinearEquiv.symmMap_rankOne_apply, star_one, _root_.map_one]

theorem Qam.Nontracial.CompleteGraph.is_reflexive {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] :
    schurIdempotent (Qam.completeGraph E) 1 = 1 :=
  by
  obtain ⟨α, β, hαβ⟩ := (1 : l(E)).exists_sum_rankOne
  nth_rw_lhs 1 [hαβ]
  simp_rw [map_sum, Qam.completeGraph, schurIdempotent.apply_rankOne, one_mul, ← hαβ]

theorem LinearMap.mul'_comp_mul'_adjoint_of_delta_form {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    [hφ : Fact φ.IsFaithfulPosMap] (hφ₂ : φ.Matrix⁻¹.trace = δ) :
    LinearMap.mul' ℂ (Matrix p p ℂ) ∘ₗ (LinearMap.mul' ℂ (Matrix p p ℂ)).adjoint = δ • 1 := by
  rw [Qam.Nontracial.mul_comp_mul_adjoint, hφ₂]

theorem LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    m ∘ₗ m.adjoint = δ • id :=
  by
  rw [LinearMap.pi_mul'_comp_mul'_adjoint_eq_smul_id_iff δ]
  exact hφ₂
  exact _inst_5

theorem Qam.Nontracial.delta_ne_zero [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    [hφ : Fact φ.IsFaithfulPosMap] (hφ₂ : φ.Matrix⁻¹.trace = δ) : δ ≠ 0 :=
  by
  rw [← hφ₂]
  exact Matrix.PosDef.trace_ne_zero (pos_def.inv hφ.elim.matrix_is_pos_def)

theorem Pi.Qam.Nontracial.delta_ne_zero [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) : δ ≠ 0 :=
  by
  have : ∀ i, (φ i).Matrix⁻¹.trace ≠ 0 := by
    intro i
    exact Matrix.PosDef.trace_ne_zero (pos_def.inv (hφ i).elim.matrixIsPosDef)
  have this' : δ ≠ 0 ↔ ∀ i, (φ i).Matrix⁻¹.trace ≠ 0 :=
    by
    constructor <;> rintro h i
    · exact this _
    · rw [i] at *
      let j : p := Classical.arbitrary p
      exact (h j) (hφ₂ j)
  rw [this']
  exact this

@[instance]
noncomputable def Qam.Nontracial.Mul'CompMul'Adjoint.invertible [Nonempty p]
    {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ} [hφ : Fact φ.IsFaithfulPosMap]
    (hφ₂ : φ.Matrix⁻¹.trace = δ) :
    @Invertible l(Matrix p p ℂ) { mul := (· ∘ₗ ·) } { one := 1 }
      (LinearMap.mul' ℂ (Matrix p p ℂ) ∘ₗ (LinearMap.mul' ℂ (Matrix p p ℂ)).adjoint) :=
  by
  rw [LinearMap.mul'_comp_mul'_adjoint_of_delta_form hφ₂]
  apply IsUnit.invertible
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_smul _ _ _, LinearMap.one_eq_id,
    LinearMap.ker_id]
  exact Qam.Nontracial.delta_ne_zero hφ₂

@[instance]
noncomputable def Pi.Qam.Nontracial.Mul'CompMul'Adjoint.invertible [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    @Invertible (ℍ →ₗ[ℂ] ℍ) { mul := (· ∘ₗ ·) } { one := id } (m ∘ₗ m.adjoint) :=
  by
  rw [LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂]
  apply IsUnit.invertible
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_smul _ _ _, LinearMap.one_eq_id,
    LinearMap.ker_id]
  exact Pi.Qam.Nontracial.delta_ne_zero hφ₂

noncomputable def Qam.trivialGraph [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    (hφ : Fact φ.IsFaithfulPosMap) (hφ₂ : φ.Matrix⁻¹.trace = δ) : l(Matrix p p ℂ) :=
  by
  letI := hφ
  letI := Qam.Nontracial.Mul'CompMul'Adjoint.invertible hφ₂
  exact ⅟ (LinearMap.mul' ℂ (Matrix p p ℂ) ∘ₗ (LinearMap.mul' ℂ (Matrix p p ℂ)).adjoint)

noncomputable def Pi.Qam.trivialGraph [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, Fact (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) : l(ℍ) :=
  by
  letI := hφ
  letI := Pi.Qam.Nontracial.Mul'CompMul'Adjoint.invertible hφ₂
  exact ⅟ (m ∘ₗ m.adjoint)

theorem Qam.trivialGraph_eq [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.Matrix⁻¹.trace = δ) :
    Qam.trivialGraph hφ hφ₂ = δ⁻¹ • (1 : l(Matrix p p ℂ)) :=
  by
  haveI := @Qam.Nontracial.Mul'CompMul'Adjoint.invertible p _ _ _ φ δ hφ hφ₂
  simp_rw [Qam.trivialGraph]
  apply invOf_eq_right_inv
  rw [LinearMap.mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_mul_smul, one_mul, mul_inv_cancel,
    one_smul]
  · exact Qam.Nontracial.delta_ne_zero hφ₂

theorem Pi.Qam.trivialGraph_eq [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    Pi.Qam.trivialGraph hφ hφ₂ = δ⁻¹ • (1 : ℍ →ₗ[ℂ] ℍ) :=
  by
  haveI := @Pi.Qam.Nontracial.Mul'CompMul'Adjoint.invertible p _ _ n _ _ φ _ _ δ _ hφ₂
  simp_rw [Pi.Qam.trivialGraph]
  apply invOf_eq_right_inv
  rw [LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_mul_smul, one_mul, mul_inv_cancel,
    one_smul]
  · exact Pi.Qam.Nontracial.delta_ne_zero hφ₂

theorem Qam.Nontracial.TrivialGraph.qam [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.Matrix⁻¹.trace = δ) :
    schurIdempotent (Qam.trivialGraph hφ hφ₂) (Qam.trivialGraph hφ hφ₂) = Qam.trivialGraph hφ hφ₂ :=
  by
  rw [Qam.trivialGraph_eq]
  let hQ := Module.Dual.IsFaithfulPosMap.matrixIsPosDef hφ.elim
  simp_rw [SMulHomClass.map_smul, LinearMap.smul_apply, smul_smul, schurIdempotent,
    LinearMap.coe_mk, TensorProduct.map_one, LinearMap.one_eq_id, LinearMap.id_comp,
    LinearMap.mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul, mul_assoc]
  rw [inv_mul_cancel _, mul_one, LinearMap.one_eq_id]
  exact Qam.Nontracial.delta_ne_zero hφ₂

theorem Pi.Qam.Nontracial.TrivialGraph.qam [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    schurIdempotent (Pi.Qam.trivialGraph hφ hφ₂) (Pi.Qam.trivialGraph hφ hφ₂) =
      Pi.Qam.trivialGraph hφ hφ₂ :=
  by
  rw [Pi.Qam.trivialGraph_eq]
  let hQ := Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hφ
  let Q := Module.Dual.pi.matrixBlock φ
  simp_rw [SMulHomClass.map_smul, LinearMap.smul_apply, smul_smul, schurIdempotent,
    LinearMap.coe_mk, TensorProduct.map_one, LinearMap.one_eq_id, LinearMap.id_comp,
    LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul, mul_assoc]
  rw [inv_mul_cancel _, mul_one, LinearMap.one_eq_id]
  exact Pi.Qam.Nontracial.delta_ne_zero hφ₂

theorem Qam.Nontracial.TrivialGraph.qam.is_self_adjoint [Nonempty p]
    {φ : Module.Dual ℂ (Matrix p p ℂ)} [hφ : Fact φ.IsFaithfulPosMap] {δ : ℂ}
    (hφ₂ : φ.Matrix⁻¹.trace = δ) : (Qam.trivialGraph hφ hφ₂).adjoint = Qam.trivialGraph hφ hφ₂ :=
  by
  simp_rw [Qam.trivialGraph_eq, LinearMap.adjoint_smul, LinearMap.adjoint_one, starRingEnd_apply,
    star_inv', ← starRingEnd_apply]
  congr 2
  rw [← hφ₂, starRingEnd_apply, trace_star, hφ.elim.matrix_is_pos_def.1.inv.Eq]

theorem Pi.Qam.Nontracial.TrivialGraph.qam.is_self_adjoint [Nonempty p] [∀ i, Nontrivial (n i)]
    {δ : ℂ} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    (Pi.Qam.trivialGraph hφ hφ₂).adjoint = Pi.Qam.trivialGraph hφ hφ₂ :=
  by
  simp_rw [Pi.Qam.trivialGraph_eq, LinearMap.adjoint_smul, LinearMap.adjoint_one, starRingEnd_apply,
    star_inv', ← starRingEnd_apply]
  congr 2
  have : ∀ i, ((φ i).Matrix⁻¹.trace.re : ℂ) = (φ i).Matrix⁻¹.trace :=
    by
    intro i
    rw [← Complex.conj_eq_iff_re, starRingEnd_apply, trace_star,
      (hφ i).elim.matrixIsPosDef.1.inv.Eq]
  simp_rw [hφ₂] at this
  rw [← this (Nonempty.some _inst_5), Complex.conj_ofReal]

theorem Qam.Nontracial.trivialGraph [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.Matrix⁻¹.trace = δ) :
    schurIdempotent (Qam.trivialGraph hφ hφ₂) 1 = 1 :=
  by
  rw [Qam.trivialGraph_eq, SMulHomClass.map_smul, LinearMap.smul_apply]
  simp_rw [schurIdempotent, LinearMap.coe_mk, TensorProduct.map_one, LinearMap.one_eq_id,
    LinearMap.id_comp, LinearMap.mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul,
    inv_mul_cancel (Qam.Nontracial.delta_ne_zero hφ₂), one_smul, LinearMap.one_eq_id]

theorem Pi.Qam.Nontracial.trivialGraph [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    schurIdempotent (Pi.Qam.trivialGraph hφ hφ₂) 1 = 1 :=
  by
  rw [Pi.Qam.trivialGraph_eq, SMulHomClass.map_smul, LinearMap.smul_apply]
  simp_rw [schurIdempotent, LinearMap.coe_mk, TensorProduct.map_one, LinearMap.one_eq_id,
    LinearMap.id_comp, LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul,
    inv_mul_cancel (Pi.Qam.Nontracial.delta_ne_zero hφ₂), one_smul, LinearMap.one_eq_id]

theorem Qam.refl_idempotent_one_one_of_delta [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.Matrix⁻¹.trace = δ) :
    schurIdempotent (1 : l(Matrix p p ℂ)) (1 : l(Matrix p p ℂ)) = δ • (1 : l(Matrix p p ℂ)) := by
  simp_rw [schurIdempotent, LinearMap.coe_mk, TensorProduct.map_one, LinearMap.one_comp,
    LinearMap.mul'_comp_mul'_adjoint_of_delta_form hφ₂]

theorem Pi.Qam.refl_idempotent_one_one_of_delta [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    schurIdempotent (1 : l(ℍ)) (1 : l(ℍ)) = δ • (1 : l(ℍ)) := by
  simp_rw [schurIdempotent, LinearMap.coe_mk, TensorProduct.map_one, LinearMap.one_comp,
    LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂]

theorem Qam.Lm.Nontracial.is_unreflexive_iff_reflexive_add_one [Nonempty p]
    {φ : Module.Dual ℂ (Matrix p p ℂ)} [hφ : Fact φ.IsFaithfulPosMap] {δ : ℂ}
    (hφ₂ : φ.Matrix⁻¹.trace = δ) (x : l(Matrix p p ℂ)) :
    schurIdempotent x 1 = 0 ↔ schurIdempotent (δ⁻¹ • (x + 1)) 1 = 1 :=
  by
  simp_rw [SMulHomClass.map_smul, LinearMap.smul_apply, _root_.map_add, LinearMap.add_apply,
    Qam.refl_idempotent_one_one_of_delta hφ₂, smul_add, smul_smul,
    inv_mul_cancel (Qam.Nontracial.delta_ne_zero hφ₂), one_smul, add_left_eq_self]
  rw [smul_eq_zero_iff_right (inv_ne_zero (Qam.Nontracial.delta_ne_zero hφ₂))]

theorem Pi.Qam.Lm.Nontracial.is_unreflexive_iff_reflexive_add_one [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) (x : l(ℍ)) :
    schurIdempotent x 1 = 0 ↔ schurIdempotent (δ⁻¹ • (x + 1)) 1 = 1 :=
  by
  simp_rw [SMulHomClass.map_smul, LinearMap.smul_apply, _root_.map_add, LinearMap.add_apply,
    Pi.Qam.refl_idempotent_one_one_of_delta hφ₂, smul_add, smul_smul,
    inv_mul_cancel (Pi.Qam.Nontracial.delta_ne_zero hφ₂), one_smul, add_left_eq_self]
  rw [smul_eq_zero_iff_right (inv_ne_zero (Pi.Qam.Nontracial.delta_ne_zero hφ₂))]

theorem Qam.refl_idempotent_completeGraph_left {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E]
    (x : l(E)) : schurIdempotent (Qam.completeGraph E) x = x :=
  schurIdempotent_one_one_left _

theorem Qam.refl_idempotent_completeGraph_right {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E]
    (x : l(E)) : schurIdempotent x (Qam.completeGraph E) = x :=
  schurIdempotent_one_one_right _

noncomputable def Qam.complement' {E : Type _} [NormedAddCommGroupOfRing E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] (x : l(E)) : l(E) :=
  Qam.completeGraph E - x

theorem Qam.Nontracial.Complement'.qam {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E]
    (x : l(E)) :
    schurIdempotent x x = x ↔
      schurIdempotent (Qam.complement' x) (Qam.complement' x) = Qam.complement' x :=
  by
  simp only [Qam.complement', _root_.map_sub, LinearMap.sub_apply,
    Qam.refl_idempotent_completeGraph_left, Qam.refl_idempotent_completeGraph_right,
    Qam.Nontracial.CompleteGraph.qam]
  simp only [sub_right_inj, sub_eq_self]
  simp only [sub_eq_zero, @eq_comm _ x]

theorem Qam.Nontracial.Complement'.qam.isReal {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] (x : l(Matrix p p ℂ)) : x.IsReal ↔ (Qam.complement' x).IsReal :=
  by
  simp only [Qam.complement', LinearMap.isReal_iff, LinearMap.real_sub,
    (LinearMap.isReal_iff _).mp (@Qam.Nontracial.CompleteGraph.isReal p _ _ φ _)]
  simp only [sub_right_inj]

theorem Pi.Qam.Nontracial.Complement'.Qam.isReal [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap]
    (x : l(ℍ)) : x.IsReal ↔ (Qam.complement' x).IsReal :=
  by
  simp only [Qam.complement', LinearMap.isReal_iff, LinearMap.real_sub,
    (LinearMap.isReal_iff _).mp (@Pi.Qam.Nontracial.CompleteGraph.isReal p _ _ n _ _ φ _)]
  simp only [sub_right_inj]

theorem Qam.complement'_complement' {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E]
    (x : l(E)) : Qam.complement' (Qam.complement' x) = x :=
  sub_sub_cancel _ _

theorem Qam.Nontracial.Complement'.ir_reflexive {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E]
    (x : l(E)) (α : Prop) [Decidable α] :
    schurIdempotent x (1 : l(E)) = ite α (1 : l(E)) (0 : l(E)) ↔
      schurIdempotent (Qam.complement' x) (1 : l(E)) = ite α (0 : l(E)) (1 : l(E)) :=
  by
  simp_rw [Qam.complement', _root_.map_sub, LinearMap.sub_apply,
    Qam.refl_idempotent_completeGraph_left]
  by_cases α <;> simp_rw [h]
  · simp_rw [if_true, sub_eq_zero, eq_comm]
  · simp_rw [if_false, sub_eq_self]

def QamReflexive {E : Type _} [NormedAddCommGroupOfRing E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] (x : l(E)) : Prop :=
  schurIdempotent x x = x ∧ schurIdempotent x 1 = 1

def QamIrreflexive {E : Type _} [NormedAddCommGroupOfRing E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] (x : l(E)) : Prop :=
  schurIdempotent x x = x ∧ schurIdempotent x 1 = 0

theorem Qam.complement'_is_irreflexive_iff {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E]
    (x : l(E)) : QamIrreflexive (Qam.complement' x) ↔ QamReflexive x :=
  by
  have := Qam.Nontracial.Complement'.ir_reflexive x True
  simp_rw [if_true] at this
  rw [QamReflexive, QamIrreflexive, ← Qam.Nontracial.Complement'.qam]
  simp_rw [this]

theorem Qam.complement'_is_reflexive_iff {E : Type _} [NormedAddCommGroupOfRing E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E]
    (x : l(E)) : QamReflexive (Qam.complement' x) ↔ QamIrreflexive x :=
  by
  have := Qam.Nontracial.Complement'.ir_reflexive x False
  simp_rw [if_false] at this
  rw [QamReflexive, QamIrreflexive, ← Qam.Nontracial.Complement'.qam, this]

noncomputable def Qam.complement'' [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    (hφ : Fact φ.IsFaithfulPosMap) (hφ₂ : φ.Matrix⁻¹.trace = δ) (x : l(Matrix p p ℂ)) :
    l(Matrix p p ℂ) :=
  x - Qam.trivialGraph hφ hφ₂

noncomputable def Pi.Qam.complement'' [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, Fact (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) (x : l(ℍ)) :
    l(ℍ) :=
  x - Pi.Qam.trivialGraph hφ hφ₂

theorem single_schurIdempotent_real {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] (x y : l(Matrix p p ℂ)) :
    (schurIdempotent x y).Real = schurIdempotent y.Real x.Real :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  obtain ⟨γ, δ, rfl⟩ := y.exists_sum_rank_one
  simp only [LinearMap.real_sum, map_sum, LinearMap.sum_apply, rankOne_real_apply,
    schurIdempotent.apply_rankOne, mul_eq_mul, conj_transpose_mul]
  simp only [← mul_eq_mul, _root_.map_mul]
  rw [Finset.sum_comm]

theorem schurIdempotent_reflexive_of_isReal {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] {x : l(Matrix p p ℂ)} (hx : x.IsReal) :
    schurIdempotent x 1 = 1 ↔ schurIdempotent 1 x = 1 := by
  rw [LinearMap.real_inj_eq, single_schurIdempotent_real, LinearMap.real_one, x.is_real_iff.mp hx]

theorem Pi.schurIdempotent_reflexive_of_isReal [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] {x : l(ℍ)}
    (hx : x.IsReal) : schurIdempotent x 1 = 1 ↔ schurIdempotent 1 x = 1 := by
  rw [LinearMap.real_inj_eq, schurIdempotent_real, LinearMap.real_one, x.is_real_iff.mp hx]

theorem Qam.complement''_is_irreflexive_iff [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)} {δ : ℂ}
    [hφ : Fact φ.IsFaithfulPosMap] (hφ₂ : φ.Matrix⁻¹.trace = δ) {x : l(Matrix p p ℂ)}
    (hx : x.IsReal) : QamIrreflexive (Qam.complement'' hφ hφ₂ x) ↔ QamReflexive x :=
  by
  rw [QamReflexive, QamIrreflexive]
  have t1 := Qam.Nontracial.TrivialGraph.qam hφ₂
  have t2 := Qam.Nontracial.trivialGraph hφ₂
  have t3 : schurIdempotent (Qam.complement'' hφ hφ₂ x) 1 = 0 ↔ schurIdempotent x 1 = 1 := by
    simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t2, sub_eq_zero]
  rw [t3]
  simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t1, sub_sub]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine' ⟨_, h2⟩
  all_goals
    simp only [Qam.trivialGraph_eq, SMulHomClass.map_smul, LinearMap.smul_apply, h2,
      (schurIdempotent_reflexive_of_isReal hx).mp h2, sub_self, add_zero, sub_left_inj] at h1 ⊢
    exact h1

theorem Pi.Qam.complement''_is_irreflexive_iff [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) {x : l(ℍ)}
    (hx : x.IsReal) : QamIrreflexive (Pi.Qam.complement'' hφ hφ₂ x) ↔ QamReflexive x :=
  by
  rw [QamReflexive, QamIrreflexive]
  have t1 := @Pi.Qam.Nontracial.TrivialGraph.qam p _ _ n _ _ φ _ _ δ _ hφ₂
  have t2 := @Pi.Qam.Nontracial.trivialGraph p _ _ n _ _ φ _ _ δ _ hφ₂
  have t3 : schurIdempotent (Pi.Qam.complement'' hφ hφ₂ x) 1 = 0 ↔ schurIdempotent x 1 = 1 := by
    simp_rw [Pi.Qam.complement'', map_sub, LinearMap.sub_apply, t2, sub_eq_zero]
  rw [t3]
  simp_rw [Pi.Qam.complement'', map_sub, LinearMap.sub_apply, t1, sub_sub]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine' ⟨_, h2⟩
  all_goals
    simp only [Pi.Qam.trivialGraph_eq, SMulHomClass.map_smul, LinearMap.smul_apply, h2,
      (Pi.schurIdempotent_reflexive_of_isReal hx).mp h2, sub_self, add_zero, sub_left_inj] at h1 ⊢
    exact h1

noncomputable def Pi.Qam.irreflexiveComplement [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, Fact (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) (x : l(ℍ)) :
    l(ℍ) :=
  Qam.completeGraph ℍ - Pi.Qam.trivialGraph hφ hφ₂ - x

noncomputable def Pi.Qam.reflexiveComplement [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    (hφ : ∀ i, Fact (φ i).IsFaithfulPosMap) (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) (x : l(ℍ)) :
    l(ℍ) :=
  Qam.completeGraph ℍ + Pi.Qam.trivialGraph hφ hφ₂ - x

theorem Qam.Nontracial.trivialGraph.isReal [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : Fact φ.IsFaithfulPosMap] {δ : ℂ} (hφ₂ : φ.Matrix⁻¹.trace = δ) :
    (Qam.trivialGraph hφ hφ₂).IsReal :=
  by
  rw [LinearMap.isReal_iff, Qam.trivialGraph_eq, LinearMap.real_smul, LinearMap.real_one,
    starRingEnd_apply, star_inv']
  congr
  rw [← hφ₂]
  rw [trace_star, hφ.elim.matrix_is_pos_def.inv.1.Eq]

theorem Pi.Qam.Nontracial.trivialGraph.isReal [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    (Pi.Qam.trivialGraph hφ hφ₂).IsReal :=
  by
  rw [LinearMap.isReal_iff, Pi.Qam.trivialGraph_eq, LinearMap.real_smul, LinearMap.real_one,
    starRingEnd_apply, star_inv']
  congr
  rw [← hφ₂ (Nonempty.some _inst_5)]
  rw [trace_star, (hφ _).elim.matrixIsPosDef.inv.1.Eq]

theorem Pi.Qam.irreflexiveComplement.isReal [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) {x : l(ℍ)}
    (hx : x.IsReal) : (Pi.Qam.irreflexiveComplement hφ hφ₂ x).IsReal := by
  rw [LinearMap.isReal_iff, Pi.Qam.irreflexiveComplement, LinearMap.real_sub, LinearMap.real_sub,
    (LinearMap.isReal_iff (Qam.completeGraph ℍ)).mp Pi.Qam.Nontracial.CompleteGraph.isReal,
    (LinearMap.isReal_iff (Pi.Qam.trivialGraph hφ hφ₂)).mp
      (Pi.Qam.Nontracial.trivialGraph.isReal hφ₂),
    (LinearMap.isReal_iff x).mp hx]

theorem Pi.Qam.reflexiveComplement.isReal [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) {x : l(ℍ)}
    (hx : x.IsReal) : (Pi.Qam.reflexiveComplement hφ hφ₂ x).IsReal := by
  rw [LinearMap.isReal_iff, Pi.Qam.reflexiveComplement, LinearMap.real_sub, LinearMap.real_add,
    (LinearMap.isReal_iff (Qam.completeGraph ℍ)).mp Pi.Qam.Nontracial.CompleteGraph.isReal,
    (LinearMap.isReal_iff (Pi.Qam.trivialGraph hφ hφ₂)).mp
      (Pi.Qam.Nontracial.trivialGraph.isReal hφ₂),
    (LinearMap.isReal_iff x).mp hx]

theorem Pi.Qam.irreflexiveComplement_irreflexiveComplement [Nonempty p] [∀ i, Nontrivial (n i)]
    {δ : ℂ} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ)
    {x : l(ℍ)} : Pi.Qam.irreflexiveComplement hφ hφ₂ (Pi.Qam.irreflexiveComplement hφ hφ₂ x) = x :=
  sub_sub_cancel _ _

theorem Pi.Qam.reflexiveComplement_reflexiveComplement [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) {x : l(ℍ)} :
    Pi.Qam.reflexiveComplement hφ hφ₂ (Pi.Qam.reflexiveComplement hφ hφ₂ x) = x :=
  sub_sub_cancel _ _

theorem Pi.Qam.trivialGraph_reflexiveComplement_eq_completeGraph [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    Pi.Qam.reflexiveComplement hφ hφ₂ (Pi.Qam.trivialGraph hφ hφ₂) = Qam.completeGraph ℍ :=
  add_sub_cancel _ _

theorem Pi.Qam.completeGraph_reflexiveComplement_eq_trivialGraph [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) :
    Pi.Qam.reflexiveComplement hφ hφ₂ (Qam.completeGraph ℍ) = Pi.Qam.trivialGraph hφ hφ₂ :=
  add_sub_cancel' _ _

theorem Qam.complement'_eq {E : Type _} [NormedAddCommGroupOfRing E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] (a : l(E)) :
    Qam.complement' a = Qam.completeGraph E - a :=
  rfl

theorem Pi.Qam.irreflexiveComplement_is_irreflexive_qam_iff_irreflexive_qam [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) {x : l(ℍ)} (hx : x.IsReal) :
    QamIrreflexive (Pi.Qam.irreflexiveComplement hφ hφ₂ x) ↔ QamIrreflexive x :=
  by
  rw [Pi.Qam.irreflexiveComplement, sub_sub, ← Qam.complement'_eq,
    Qam.complement'_is_irreflexive_iff, ← Pi.Qam.complement''_is_irreflexive_iff hφ₂,
    Pi.Qam.complement'', add_sub_cancel']
  ·
    rw [LinearMap.isReal_iff, LinearMap.real_add, x.is_real_iff.mp hx,
      (Pi.Qam.trivialGraph hφ hφ₂).isReal_iff.mp (Pi.Qam.Nontracial.trivialGraph.isReal hφ₂)]

theorem Pi.Qam.reflexive_complment_is_reflexive_qam_iff_reflexive_qam [Nonempty p]
    [∀ i, Nontrivial (n i)] {δ : ℂ} [hφ : ∀ i, Fact (φ i).IsFaithfulPosMap]
    (hφ₂ : ∀ i, (φ i).Matrix⁻¹.trace = δ) {x : l(ℍ)} (hx : x.IsReal) :
    QamReflexive (Pi.Qam.reflexiveComplement hφ hφ₂ x) ↔ QamReflexive x :=
  by
  rw [Pi.Qam.reflexiveComplement, ← sub_sub_eq_add_sub, ← Qam.complement'_eq,
    Qam.complement'_is_reflexive_iff]
  exact Pi.Qam.complement''_is_irreflexive_iff hφ₂ hx

