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

variable {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [hA : QuantumSet A] [hB : QuantumSet B]

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
    _root_.map_one]

theorem Qam.Nontracial.CompleteGraph.symm_eq :
  symmMap ℂ _ _ (Qam.completeGraph A B) = Qam.completeGraph B A :=
by simp_rw [Qam.completeGraph, symmMap_rankOne_apply, star_one, _root_.map_one]
theorem Qam.Nontracial.CompleteGraph.is_symm :
  symmMap ℂ _ _ (Qam.completeGraph A A) = Qam.completeGraph A A :=
Qam.Nontracial.CompleteGraph.symm_eq

theorem Qam.Nontracial.CompleteGraph.is_reflexive :
  (Qam.completeGraph A A) •ₛ 1 = 1 :=
by
  obtain ⟨α, β, hαβ⟩ := (1 : l(A)).exists_sum_rankOne
  nth_rw 1 [hαβ]
  simp_rw [map_sum, Qam.completeGraph, schurMul.apply_rankOne, one_mul, ← hαβ]

open scoped ComplexOrder
@[reducible]
class QuantumSetDeltaForm (A : Type*) [NormedAddCommGroupOfRing A] [QuantumSet A] where
  delta : ℂ
  delta_pos : 0 < delta
  mul_comp_comul_eq : LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul = delta • 1

theorem LinearMap.mul'_comp_mul'_adjoint_of_delta_form {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] :
  LinearMap.mul' ℂ (Matrix p p ℂ) ∘ₗ Coalgebra.comul = φ.matrix⁻¹.trace • 1 :=
by rw [Coalgebra.comul_eq_mul_adjoint, Qam.Nontracial.mul_comp_mul_adjoint]

theorem LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  m ∘ₗ Coalgebra.comul = δ • id :=
by
  rw [Coalgebra.comul_eq_mul_adjoint,
    LinearMap.pi_mul'_comp_mul'_adjoint_eq_smul_id_iff δ]
  exact hφ₂

theorem Qam.Nontracial.delta_pos [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] : 0 < φ.matrix⁻¹.trace :=
  by
  rw [IsHermitian.trace_eq (PosDef.inv hφ.matrixIsPosDef).1, RCLike.pos_def]
  simp only [RCLike.ofReal_im, and_true]
  rw [← IsHermitian.trace_eq]
  exact Matrix.PosDef.pos_trace (PosDef.inv hφ.matrixIsPosDef)

theorem Pi.Qam.Nontracial.delta_ne_zero [Nonempty p] [∀ i, Nontrivial (n i)] {δ : ℂ}
    [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) : 0 < δ :=
  by
  let j : p := Classical.arbitrary p
  rw [← hφ₂ j]
  exact Qam.Nontracial.delta_pos

-- set_option maxHeartbeats 0 in
noncomputable
instance Matrix.quantumSetDeltaForm [Nonempty p] {φ : Module.Dual ℂ (Matrix p p ℂ)}
    [hφ : φ.IsFaithfulPosMap] :
    QuantumSetDeltaForm (Matrix p p ℂ) where
  delta := φ.matrix⁻¹.trace
  delta_pos := Qam.Nontracial.delta_pos
  mul_comp_comul_eq := by rw [LinearMap.mul'_comp_mul'_adjoint_of_delta_form]

set_option synthInstance.checkSynthOrder false in
noncomputable instance PiMat.quantumSetDeltaForm [Nonempty p] [∀ i, Nontrivial (n i)] {d : ℂ}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap] [hφ₂ : Fact (∀ i, (φ i).matrix⁻¹.trace = d)] :
    QuantumSetDeltaForm (PiMat ℂ p n) where
  delta := d
  delta_pos := Pi.Qam.Nontracial.delta_ne_zero hφ₂.out
  mul_comp_comul_eq := by
    rw [LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form]
    exact hφ₂.out

@[instance]
noncomputable def QuantumSet.DeltaForm.mul_comp_comul_isInvertible {A : Type*} [NormedAddCommGroupOfRing A]
  [QuantumSet A] [hA2 : QuantumSetDeltaForm A] :
  Invertible (LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul) :=
by
  apply IsUnit.invertible
  rw [LinearMap.isUnit_iff_ker_eq_bot, hA2.mul_comp_comul_eq, LinearMap.ker_smul, LinearMap.one_eq_id,
    LinearMap.ker_id]
  exact ne_of_gt hA2.delta_pos


noncomputable def Qam.trivialGraph (A : Type*) [NormedAddCommGroupOfRing A] [QuantumSet A]
  [QuantumSetDeltaForm A] :
  l(A) :=
⅟ (LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul)

variable {A : Type*} [NormedAddCommGroupOfRing A] [hA : QuantumSet A]

theorem Qam.trivialGraph_eq [hA2 : QuantumSetDeltaForm A] :
    Qam.trivialGraph A = hA2.delta⁻¹ • (1 : l(A)) :=
  by
  simp_rw [Qam.trivialGraph]
  apply invOf_eq_right_inv
  rw [hA2.mul_comp_comul_eq, smul_mul_smul, one_mul, mul_inv_cancel,
    one_smul]
  · exact ne_of_gt hA2.delta_pos

theorem Qam.Nontracial.TrivialGraph.qam [hA2 : QuantumSetDeltaForm A] :
    (Qam.trivialGraph A) •ₛ (Qam.trivialGraph A) = Qam.trivialGraph A :=
  by
  rw [Qam.trivialGraph_eq]
  simp_rw [_root_.map_smul, LinearMap.smul_apply, smul_smul, schurMul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [TensorProduct.map_one, LinearMap.one_eq_id, LinearMap.id_comp,
    hA2.mul_comp_comul_eq, smul_smul, mul_assoc]
  rw [inv_mul_cancel _, mul_one, LinearMap.one_eq_id]
  . exact ne_of_gt hA2.delta_pos

theorem Qam.Nontracial.TrivialGraph.qam.is_self_adjoint [hA2 : QuantumSetDeltaForm A] :
    LinearMap.adjoint (Qam.trivialGraph A) = Qam.trivialGraph A :=
  by
  simp_rw [Qam.trivialGraph_eq, LinearMap.adjoint_smul, LinearMap.adjoint_one, starRingEnd_apply,
    star_inv', ← starRingEnd_apply]
  congr 2
  have := hA2.delta_pos
  rw [RCLike.pos_def, ← RCLike.conj_eq_iff_im] at this
  exact this.2

theorem Qam.Nontracial.trivialGraph [hA2 : QuantumSetDeltaForm A] :
    (Qam.trivialGraph A) •ₛ 1 = 1 :=
  by
  rw [Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply]
  simp only [schurMul, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [TensorProduct.map_one, LinearMap.one_eq_id,
    LinearMap.id_comp, hA2.mul_comp_comul_eq, smul_smul,
    inv_mul_cancel (ne_of_gt hA2.delta_pos), one_smul, LinearMap.one_eq_id]

theorem Qam.refl_idempotent_one_one_of_delta [hA2 : QuantumSetDeltaForm A] :
    (1 : _) •ₛ (1 : l(A)) = hA2.delta • (1 : l(A)) := by
  simp_rw [schurMul_apply_apply, TensorProduct.map_one, LinearMap.one_comp, hA2.mul_comp_comul_eq]

theorem Qam.Lm.Nontracial.is_unreflexive_iff_reflexive_add_one [hA2 : QuantumSetDeltaForm A]
    (x : l(A)) :
    x •ₛ 1 = 0 ↔ (hA2.delta⁻¹ • (x + 1)) •ₛ 1 = 1 :=
  by
  simp_rw [_root_.map_smul, LinearMap.smul_apply, _root_.map_add, LinearMap.add_apply,
    Qam.refl_idempotent_one_one_of_delta, smul_add, smul_smul,
    inv_mul_cancel (ne_of_gt hA2.delta_pos), one_smul, add_left_eq_self]
  rw [smul_eq_zero_iff_right (inv_ne_zero (ne_of_gt hA2.delta_pos))]

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

theorem Qam.Nontracial.Complement'.qam.isReal
    (x : A →ₗ[ℂ] B) : x.IsReal ↔ (Qam.complement' x).IsReal :=
  by
  simp only [Qam.complement', LinearMap.isReal_iff, LinearMap.real_sub,
    (LinearMap.isReal_iff _).mp (Qam.Nontracial.CompleteGraph.isReal)]
  simp only [sub_right_inj]

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

noncomputable def Qam.complement'' [QuantumSetDeltaForm A]
  (x : l(A)) :
    l(A) :=
  x - Qam.trivialGraph A

theorem schurMul_reflexive_of_isReal {x : l(A)} (hx : x.IsReal) :
    x •ₛ 1 = 1 ↔ 1 •ₛ x = 1 :=
by
  rw [LinearMap.real_inj_eq, schurMul_real, LinearMap.real_one, x.isReal_iff.mp hx]

theorem Qam.complement''_is_irreflexive_iff [hA2 : QuantumSetDeltaForm A] {x : l(A)}
    (hx : x.IsReal) : QamIrreflexive (Qam.complement'' x) ↔ QamReflexive x :=
  by
  rw [QamReflexive_iff, QamIrreflexive_iff]
  have t1 := @Qam.Nontracial.TrivialGraph.qam A _ _ _
  have t2 := @Qam.Nontracial.trivialGraph A _ _ _
  have t3 : (Qam.complement'' x) •ₛ 1 = 0 ↔ x •ₛ 1 = 1 := by
    simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t2, sub_eq_zero]
  rw [t3]
  simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t1, sub_sub]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine' ⟨_, h2⟩
  all_goals
    simp only [Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply, h2,
      (schurMul_reflexive_of_isReal hx).mp h2, sub_self, add_zero, sub_left_inj] at h1 ⊢
    exact h1

noncomputable def Qam.irreflexiveComplement [QuantumSetDeltaForm A] (x : l(A)) :
    l(A) :=
Qam.completeGraph A A - Qam.trivialGraph A - x

noncomputable def Qam.reflexiveComplement [QuantumSetDeltaForm A] (x : l(A)) :
  l(A) :=
Qam.completeGraph A A + Qam.trivialGraph A - x

theorem Qam.Nontracial.trivialGraph.isReal [hA2 : QuantumSetDeltaForm A] :
    (Qam.trivialGraph A).IsReal :=
  by
  rw [LinearMap.isReal_iff, Qam.trivialGraph_eq, LinearMap.real_smul, LinearMap.real_one,
    starRingEnd_apply, star_inv']
  congr
  have := hA2.delta_pos
  rw [RCLike.pos_def, ← RCLike.conj_eq_iff_im] at this
  exact this.2

theorem Qam.irreflexiveComplement.isReal [hA2 : QuantumSetDeltaForm A]
  {x : l(A)} (hx : x.IsReal) : (Qam.irreflexiveComplement x).IsReal := by
  rw [LinearMap.isReal_iff, Qam.irreflexiveComplement, LinearMap.real_sub, LinearMap.real_sub,
    (LinearMap.isReal_iff (Qam.completeGraph A A)).mp Qam.Nontracial.CompleteGraph.isReal,
    (LinearMap.isReal_iff (Qam.trivialGraph A)).mp
      Qam.Nontracial.trivialGraph.isReal,
    (LinearMap.isReal_iff x).mp hx]

theorem Qam.reflexiveComplement.isReal [hA2 : QuantumSetDeltaForm A] {x : l(A)}
    (hx : x.IsReal) : (Qam.reflexiveComplement x).IsReal := by
  rw [LinearMap.isReal_iff, Qam.reflexiveComplement, LinearMap.real_sub, LinearMap.real_add,
    (LinearMap.isReal_iff (Qam.completeGraph A A)).mp Qam.Nontracial.CompleteGraph.isReal,
    (LinearMap.isReal_iff (Qam.trivialGraph A)).mp
      Qam.Nontracial.trivialGraph.isReal,
    (LinearMap.isReal_iff x).mp hx]

theorem Qam.irreflexiveComplement_irreflexiveComplement [QuantumSetDeltaForm A]
    {x : l(A)} : Qam.irreflexiveComplement (Qam.irreflexiveComplement x) = x :=
  sub_sub_cancel _ _

theorem Qam.reflexiveComplement_reflexiveComplement [QuantumSetDeltaForm A] {x : l(A)} :
    Qam.reflexiveComplement (Qam.reflexiveComplement x) = x :=
  sub_sub_cancel _ _

theorem Qam.trivialGraph_reflexiveComplement_eq_completeGraph [QuantumSetDeltaForm A] :
    Qam.reflexiveComplement (Qam.trivialGraph A) = Qam.completeGraph A A :=
by simp_rw [reflexiveComplement, add_sub_cancel_right]

theorem Qam.completeGraph_reflexiveComplement_eq_trivialGraph [QuantumSetDeltaForm A] :
    Qam.reflexiveComplement (Qam.completeGraph A A) = Qam.trivialGraph A :=
  add_sub_cancel_left _ _

theorem Qam.complement'_eq {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₁]
    [FiniteDimensional ℂ E₂] [IsScalarTower ℂ E₁ E₁] [IsScalarTower ℂ E₂ E₂] [SMulCommClass ℂ E₁ E₁]
    [SMulCommClass ℂ E₂ E₂] (a : E₂ →ₗ[ℂ] E₁) :
    Qam.complement' a = Qam.completeGraph E₁ E₂ - a :=
  rfl

theorem Qam.irreflexiveComplement_is_irreflexive_qam_iff_irreflexive_qam
  [hA2 : QuantumSetDeltaForm A] {x : l(A)} (hx : x.IsReal) :
    QamIrreflexive (Qam.irreflexiveComplement x) ↔ QamIrreflexive x :=
  by
  rw [Qam.irreflexiveComplement, sub_sub, ← Qam.complement'_eq,
    Qam.complement'_is_irreflexive_iff, ← Qam.complement''_is_irreflexive_iff,
    Qam.complement'', add_sub_cancel_left]
  ·
    rw [LinearMap.isReal_iff, LinearMap.real_add, x.isReal_iff.mp hx,
      (Qam.trivialGraph A).isReal_iff.mp Qam.Nontracial.trivialGraph.isReal]

theorem Qam.reflexive_complment_is_reflexive_qam_iff_reflexive_qam
  [hA2 : QuantumSetDeltaForm A] {x : l(A)} (hx : x.IsReal) :
    QamReflexive (Qam.reflexiveComplement x) ↔ QamReflexive x :=
  by
  rw [Qam.reflexiveComplement, ← sub_sub_eq_add_sub, ← Qam.complement'_eq,
    Qam.complement'_is_reflexive_iff]
  exact Qam.complement''_is_irreflexive_iff hx
