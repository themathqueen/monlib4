/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Ips.MatIps
import Monlib.LinearAlgebra.Ips.Nontracial
import Monlib.LinearAlgebra.Ips.TensorHilbert
import Monlib.LinearAlgebra.IsReal
import Monlib.LinearAlgebra.Ips.Frob
import Monlib.LinearAlgebra.TensorFinite
import Monlib.LinearAlgebra.Ips.OpUnop
import Monlib.LinearAlgebra.LmulRmul
import Monlib.LinearAlgebra.QuantumSet.SchurMul
import Monlib.LinearAlgebra.QuantumSet.Symm
import Monlib.LinearAlgebra.QuantumSet.Instances

#align_import quantum_graph.nontracial

/-!
 # Quantum graphs: quantum adjacency matrices

 This file defines the quantum adjacency matrix of a quantum graph.
-/


variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

open scoped TensorProduct BigOperators Kronecker

local notation "ℍ" => Matrix n n ℂ
local notation "ℍ₂" => Matrix p p ℂ

local notation "⊗K" => Matrix (n × n) (n × n) ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "L(" x ")" => x →L[ℂ] x

local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable {φ : Module.Dual ℂ (Matrix n n ℂ)} {ψ : Module.Dual ℂ (Matrix p p ℂ)}

open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  LinearEquiv.toLinearMap (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ))

local notation "υ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ)))

local notation "ϰ" =>
  LinearEquiv.toLinearMap ((TensorProduct.comm ℂ (Matrix n n ℂ) ℂ))

local notation "ϰ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ (Matrix n n ℂ) ℂ))

local notation "τ" =>
  LinearEquiv.toLinearMap (TensorProduct.lid ℂ (Matrix n n ℂ))

local notation "τ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ (Matrix n n ℂ)))

local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

set_option linter.unusedVariables false in
@[reducible, nolint unusedArguments]
noncomputable def Qam.reflIdempotent (hφ : φ.IsFaithfulPosMap) :=
-- l(ℍ) →ₗ[ℂ] l(ℍ) →ₗ[ℂ] l(ℍ) :=
@schurMul _ _ hφ.quantumSet hφ.quantumSet

theorem Qam.RankOne.reflIdempotent_eq [hφ : φ.IsFaithfulPosMap] (a b c d : ℍ) :
    Qam.reflIdempotent hφ ↑|a⟩⟨b| ↑|c⟩⟨d| = |a * c⟩⟨b * d| :=
  schurMul.apply_rankOne a b c d

open TensorProduct

-- noncomputable def qam.symm (hφ : φ.is_faithful_pos_map) :
--   l(ℍ) ≃ₗ[ℂ] l(ℍ) :=
-- begin
--   letI := fact.mk hφ,
--   exact ((linear_equiv.symm_map ℂ ℍ : l(ℍ) ≃ₗ[ℂ] l(ℍ))),
-- end
theorem Finset.sum_fin_one {α : Type _} [AddCommMonoid α] (f : Fin 1 → α) : ∑ i, f i = f 0 := by
  simp only [Fintype.univ_ofSubsingleton, Fin.mk_zero, Finset.sum_singleton]

theorem rankOne_real_apply [φ.IsFaithfulPosMap] [hψ : ψ.IsFaithfulPosMap] (a : ℍ) (b : ℍ₂) :
    (|a⟩⟨b| : ℍ₂ →ₗ[ℂ] ℍ).real = |aᴴ⟩⟨hψ.sig (-1) bᴴ| :=
_root_.rankOne_real _ _

theorem Qam.RankOne.symmetric_eq [φ.IsFaithfulPosMap] [hψ : ψ.IsFaithfulPosMap]
  (a : ℍ) (b : ℍ₂) :
    (symmMap ℂ ℍ₂ ℍ) |a⟩⟨b| = |hψ.sig (-1) bᴴ⟩⟨aᴴ| :=
symmMap_rankOne_apply _ _

theorem Qam.RankOne.symmetric'_eq [hφ : φ.IsFaithfulPosMap] [ψ.IsFaithfulPosMap]
  (a : ℍ) (b : ℍ₂) :
    (symmMap ℂ ℍ ℍ₂).symm |a⟩⟨b| = |bᴴ⟩⟨hφ.sig (-1) aᴴ| :=
symmMap_symm_rankOne_apply _ _

theorem Qam.symm_adjoint_eq_symm'_of_adjoint [φ.IsFaithfulPosMap] (x : l(ℍ)) :
  LinearMap.adjoint (symmMap ℂ ℍ _ x) = ((symmMap ℂ ℍ _).symm) (LinearMap.adjoint x) :=
symmMap_apply_adjoint _

private theorem commute.adjoint_adjoint {K E : Type _} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [CompleteSpace E] {f g : E →L[K] E} :
    Commute (ContinuousLinearMap.adjoint f) (ContinuousLinearMap.adjoint g) ↔ Commute f g :=
  commute_star_star

private theorem commute.adjoint_adjoint_lm {K E : Type _} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [FiniteDimensional K E] {f g : E →ₗ[K] E} :
    Commute (LinearMap.adjoint f) (LinearMap.adjoint g) ↔ Commute f g :=
  commute_star_star

theorem LinearMap.adjoint_real_apply [hφ : φ.IsFaithfulPosMap] (f : ℍ →ₗ[ℂ] ℍ) :
    (LinearMap.adjoint f).real =
      (hφ.sig 1).toLinearMap ∘ₗ LinearMap.adjoint f.real ∘ₗ (hφ.sig (-1)).toLinearMap :=
adjoint_real_eq _

theorem Module.Dual.IsFaithfulPosMap.sig_zero'  [hφ : φ.IsFaithfulPosMap] : hφ.sig 0 = 1 :=
QuantumSet.modAut_zero

private theorem comp_sig_eq  [hφ : φ.IsFaithfulPosMap] (t : ℝ) (f g : ℍ →ₗ[ℂ] ℍ) :
    f ∘ₗ (hφ.sig t).toLinearMap = g ↔ f = g ∘ₗ (hφ.sig (-t)).toLinearMap :=
by
  rw [LinearEquiv.linearMap_comp_eq_iff, hφ.sig_symm_eq]

theorem LinearMap.IsReal.adjoint_isReal_iff_commute_with_sig  [hφ : φ.IsFaithfulPosMap] {f : ℍ →ₗ[ℂ] ℍ} (hf : f.IsReal) :
    (LinearMap.adjoint f).IsReal ↔ Commute f (hφ.sig 1).toLinearMap :=
  by
  rw [LinearMap.isReal_iff] at hf
  let σ := hφ.sig
  have : Commute f (σ 1).toLinearMap ↔ Commute (LinearMap.adjoint f) (σ 1).toLinearMap :=
    by
    simp_rw [σ]
    nth_rw 2 [← Module.Dual.IsFaithfulPosMap.sig_adjoint]
    rw [commute.adjoint_adjoint_lm]
  rw [this]
  clear this
  rw [LinearMap.isReal_iff, LinearMap.adjoint_real_apply, hf, ← LinearMap.comp_assoc, comp_sig_eq,
    neg_neg]
  simp_rw [Commute, SemiconjBy, LinearMap.mul_eq_comp, @eq_comm _ _ ((σ 1).toLinearMap ∘ₗ _)]

theorem sig_apply_posDef_matrix_hMul [hφ : φ.IsFaithfulPosMap] (t : ℝ) (x : ℍ) :
    hφ.sig t (hφ.matrixIsPosDef.rpow t * x) = x * hφ.matrixIsPosDef.rpow t := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, ← Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    neg_add_self, PosDef.rpow_zero, Matrix.one_mul]

theorem sig_apply_posDef_matrix_mul' [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
  hφ.sig 1 (φ.matrix * x) = x * φ.matrix :=
  by
  nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  rw [← sig_apply_posDef_matrix_hMul, PosDef.rpow_one_eq_self]

theorem sig_apply_matrix_hMul_posDef [hφ : φ.IsFaithfulPosMap] (t : ℝ) (x : ℍ) :
    hφ.sig t (x * hφ.matrixIsPosDef.rpow (-t)) = hφ.matrixIsPosDef.rpow (-t) * x :=
  by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    neg_add_self, PosDef.rpow_zero, Matrix.mul_one]

theorem sig_apply_matrix_hMul_posDef' [hφ : φ.IsFaithfulPosMap] (x : ℍ) : hφ.sig (-1) (x * φ.matrix) = φ.matrix * x :=
  by
  nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw 2 [← neg_neg (1 : ℝ)]
  rw [← sig_apply_matrix_hMul_posDef, neg_neg, PosDef.rpow_one_eq_self]

theorem sig_apply_matrix_hMul_posDef'' [hφ : φ.IsFaithfulPosMap] (x : ℍ) : hφ.sig 1 (x * φ.matrix⁻¹) = φ.matrix⁻¹ * x :=
  by
  nth_rw 2 [← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef]
  rw [← sig_apply_matrix_hMul_posDef, PosDef.rpow_neg_one_eq_inv_self]

theorem sig_apply_basis [hφ : φ.IsFaithfulPosMap] (i : n × n) :
    hφ.sig 1 (hφ.basis i) =
      φ.matrix⁻¹ * e_{i.1,i.2} * hφ.matrixIsPosDef.rpow (1 / 2) :=
  by
  rw [Module.Dual.IsFaithfulPosMap.basis_apply]
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    PosDef.rpow_neg_one_eq_inv_self]
  norm_num

theorem Qam.symm'_symm_real_apply_adjoint_tFAE [hφ : φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) :
    List.TFAE
      [symmMap ℂ ℍ _ A = A, (symmMap ℂ ℍ _).symm A = A, A.real = LinearMap.adjoint A,
        ∀ x y, φ (A x * y) = φ (x * A y)] :=
by
  suffices φ = Coalgebra.counit by simp_rw [this]; exact symmMap_eq_self_tfae _
  ext
  simp_rw [← Coalgebra.inner_eq_counit', Module.Dual.IsFaithfulPosMap.inner_eq, conjTranspose_one,
    one_mul]

theorem sig_comp_eq_iff [hφ : φ.IsFaithfulPosMap]  (t : ℝ) (A B : ℍ →ₗ[ℂ] ℍ) :
    (hφ.sig t).toLinearMap.comp A = B ↔ A = (hφ.sig (-t)).toLinearMap.comp B :=
by
  rw [LinearEquiv.comp_linearMap_eq_iff, Module.Dual.IsFaithfulPosMap.sig_symm_eq]

theorem Module.Dual.IsFaithfulPosMap.sig_real [hφ : φ.IsFaithfulPosMap]  {t : ℝ} :
    (hφ.sig t).toLinearMap.real = (hφ.sig (-t)).toLinearMap :=
QuantumSet.modAut_real _

theorem Qam.commute_with_sig_iff_symm_eq_symm' [hφ : φ.IsFaithfulPosMap]  {A : ℍ →ₗ[ℂ] ℍ} :
    symmMap ℂ ℍ _ A = (symmMap ℂ ℍ _).symm A ↔
      Commute A (hφ.sig 1).toLinearMap :=
by
  rw [symmMap_apply, symmMap_symm_apply, LinearMap.adjoint_real_apply, eq_comm,
    sig_comp_eq_iff, ← star_inj]
  simp_rw [LinearMap.star_eq_adjoint, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    Module.Dual.IsFaithfulPosMap.sig_adjoint]
  rw [LinearMap.real_inj_eq]
  simp_rw [LinearMap.real_comp, LinearMap.real_real, Module.Dual.IsFaithfulPosMap.sig_real, neg_neg]
  rw [eq_comm]
  rfl

theorem Qam.commute_with_sig_of_symm [hφ : φ.IsFaithfulPosMap] {A : ℍ →ₗ[ℂ] ℍ} (hA : symmMap ℂ ℍ _ A = A) :
    Commute A (hφ.sig 1).toLinearMap :=
by rw [← Qam.commute_with_sig_iff_symm_eq_symm', hA, LinearEquiv.eq_symm_apply, hA]

-- `τ ϰ (1 ⊗ η⋆ m) (m⋆ η ⊗ 1) τ⁻¹ = 1`
theorem Qam.symm_one [hφ : φ.IsFaithfulPosMap] : symmMap ℂ ℍ _ 1 = (1 : l(ℍ)) := by
  rw [symmMap_apply, LinearMap.real_one, LinearMap.adjoint_one]

def Qam (φ : Module.Dual ℂ ℍ) [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :=
  Qam.reflIdempotent hφ x x = x

def Qam.IsSelfAdjoint [φ.IsFaithfulPosMap] (x : l(ℍ)) : Prop :=
  LinearMap.adjoint x = x

def Qam.IsSymm [φ.IsFaithfulPosMap] (x : l(ℍ)) : Prop :=
  symmMap ℂ ℍ _ x = x

def QamLmNontracialIsReflexive (hφ : φ.IsFaithfulPosMap) (x : ℍ →ₗ[ℂ] ℍ) : Prop :=
  Qam.reflIdempotent hφ x 1 = (1 : l(ℍ))

def QamLmNontracialIsUnreflexive (hφ : φ.IsFaithfulPosMap) (x : ℍ →ₗ[ℂ] ℍ) : Prop :=
  Qam.reflIdempotent hφ x 1 = (0 : l(ℍ))

theorem stdBasisMatrix_squash (i j k l : n) (x : Matrix n n ℂ) :
    e_{i,j} * x * e_{k,l} = x j k • e_{i,l} := by
  ext i_1 j_1
  simp_rw [Matrix.mul_apply, Matrix.smul_apply, stdBasisMatrix, smul_ite, mul_boole, boole_mul, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, smul_eq_mul, mul_one, MulZeroClass.mul_zero]
  simp_rw [← ite_and, @and_comm (l = j_1) (i = i_1)]

theorem rankOneLm_smul {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) (r : 𝕜) : (rankOneLm x (r • y) : E →ₗ[𝕜] E) = starRingEnd 𝕜 r • rankOneLm x y := by
  rw [rankOneLm, rankOne.smul_apply]; rfl

theorem smul_rankOneLm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) (r : 𝕜) : (rankOneLm (r • x) y : E →ₗ[𝕜] E) = r • rankOneLm x y := by
  rw [rankOneLm, rankOne.apply_smul]; rfl

open scoped ComplexOrder
private theorem nontracial_basis_apply {Q : ℍ} (hQ : Q.PosDef) (i j k l : n) :
    (e_{i,j} * hQ.rpow (-(1 / 2))) k l = ite (i = k) (hQ.rpow (-(1 / 2)) j l) 0 := by
  simp_rw [mul_apply, stdBasisMatrix, boole_mul, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

noncomputable def sigop (hφ : φ.IsFaithfulPosMap) (t : ℝ) : l(ℍᵐᵒᵖ) :=
  (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) ∘ₗ (hφ.sig t).toLinearMap ∘ₗ (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ)

private theorem Psi.symmetric_rank_one [hφ : φ.IsFaithfulPosMap] (a b : ℍ) (t s : ℝ) :
    hφ.psi t s (symmMap ℂ ℍ _ |a⟩⟨b|) =
      ((hφ.sig (t + s - 1)).toLinearMap ⊗ₘ sigop hφ (-t - s))
        (tenSwap (hφ.psi t s |a⟩⟨b|)) :=
  by
  simp_rw [sigop, Qam.RankOne.symmetric_eq, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tenSwap_apply, map_tmul, LinearMap.comp_apply,
    unop_apply, op_apply, MulOpposite.unop_op, LinearEquiv.coe_toLinearMap,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, Module.Dual.IsFaithfulPosMap.sig_apply_sig,
    conjTranspose_conjTranspose, sub_add_comm, ← sub_eq_add_neg, sub_sub_cancel_left]
  ring_nf

set_option synthInstance.maxHeartbeats 0 in
theorem Psi.symmetric [hφ : φ.IsFaithfulPosMap] (a : l(ℍ)) (t s : ℝ) :
    hφ.psi t s (symmMap ℂ ℍ _ a) =
      ((hφ.sig (t + s - 1)).toLinearMap ⊗ₘ sigop hφ (-t - s))
        (tenSwap (hφ.psi t s a)) :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rankOne
  simp_rw [map_sum, Psi.symmetric_rank_one]

private theorem Psi.symmetric'_rank_one [hφ : φ.IsFaithfulPosMap] (a b : ℍ) (t s : ℝ) :
    hφ.psi t s ((symmMap ℂ ℍ _).symm |a⟩⟨b|) =
      ((hφ.sig (t + s)).toLinearMap ⊗ₘ sigop hφ (1 - t - s))
        (tenSwap (hφ.psi t s |a⟩⟨b|)) :=
  by
  simp_rw [sigop, Qam.RankOne.symmetric'_eq, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tenSwap_apply, map_tmul, LinearMap.comp_apply,
    op_apply, unop_apply, MulOpposite.unop_op, LinearEquiv.coe_toLinearMap,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, neg_neg,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, conjTranspose_conjTranspose]
  ring_nf

set_option synthInstance.maxHeartbeats 0 in
theorem Psi.symmetric' [hφ : φ.IsFaithfulPosMap] (a : l(ℍ)) (t s : ℝ) :
    hφ.psi t s ((symmMap ℂ ℍ _).symm a) =
      ((hφ.sig (t + s)).toLinearMap ⊗ₘ sigop hφ (1 - t - s))
        (tenSwap (hφ.psi t s a)) :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rankOne
  simp_rw [map_sum, Psi.symmetric'_rank_one]

private theorem Psi.idempotent_rank_one [hφ : φ.IsFaithfulPosMap] (a b c d : ℍ) (t s : ℝ) :
    hφ.psi t s (Qam.reflIdempotent hφ ↑|a⟩⟨b| ↑|c⟩⟨d|) =
      hφ.psi t s |a⟩⟨b| * hφ.psi t s |c⟩⟨d| :=
  by
  simp_rw [Qam.RankOne.reflIdempotent_eq, Module.Dual.IsFaithfulPosMap.psi_apply,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, Algebra.TensorProduct.tmul_mul_tmul,
    op_apply, ← MulOpposite.op_mul, ← conjTranspose_mul, Module.Dual.IsFaithfulPosMap.sig.map_mul']

set_option synthInstance.maxHeartbeats 0 in
theorem Psi.reflIdempotent [hφ : φ.IsFaithfulPosMap] (A B : l(ℍ)) (t s : ℝ) :
    hφ.psi t s (Qam.reflIdempotent hφ A B) = hφ.psi t s A * hφ.psi t s B :=
  by
  obtain ⟨Aα, Aβ, rfl⟩ := A.exists_sum_rankOne
  obtain ⟨Bα, Bβ, rfl⟩ := B.exists_sum_rankOne
  simp_rw [map_sum, LinearMap.sum_apply, map_sum, Psi.idempotent_rank_one, Finset.mul_sum,
    Finset.sum_mul]

theorem tenSwap_sig [hφ : φ.IsFaithfulPosMap] (x y : ℝ) :
    (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ
        TensorProduct.map ((hφ.sig x).toLinearMap : l(ℍ)) (sigop hφ y : l(ℍᵐᵒᵖ)) =
      (((hφ.sig y).toLinearMap : l(ℍ)) ⊗ₘ sigop hφ x : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ tenSwap :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp only [LinearMap.comp_apply, map_tmul, tenSwap_apply, op_apply, unop_apply,
    MulOpposite.unop_op, MulOpposite.op_unop]
  rfl

private theorem Psi.adjoint_rank_one [hφ : φ.IsFaithfulPosMap] (a b : ℍ) (t s : ℝ) :
    hφ.psi t s (LinearMap.adjoint ((|a⟩⟨b|))) =
      ((hφ.sig (t - s)).toLinearMap ⊗ₘ sigop hφ (t - s))
        (tenSwap (star (hφ.psi t s (|a⟩⟨b|)))) :=
  by
  simp_rw [← rankOneLm_eq_rankOne, sigop]
  rw [rankOneLm_adjoint]
  simp_rw [rankOneLm_eq_rankOne, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tensor_op_star_apply, unop_apply, op_apply,
    MulOpposite.unop_op, star_eq_conjTranspose, conjTranspose_conjTranspose, ←
    LinearMap.comp_apply]
  have := fun x y => @tenSwap_sig n _ _ φ hφ x y
  simp_rw [sigop] at this
  rw [← this]
  rw [LinearMap.comp_apply, map_tmul, LinearMap.comp_apply, tenSwap_apply, op_apply,
    MulOpposite.unop_op, Module.Dual.IsFaithfulPosMap.sig_conjTranspose, LinearEquiv.coe_toLinearMap,
    LinearMap.comp_apply, unop_apply, MulOpposite.unop_op, LinearEquiv.coe_toLinearMap,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig hφ, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig]
  ring_nf

set_option synthInstance.maxHeartbeats 0 in
theorem Psi.adjoint [hφ : φ.IsFaithfulPosMap] (a : l(ℍ)) (t s : ℝ) :
    hφ.psi t s (LinearMap.adjoint a) =
      ((hφ.sig (t - s)).toLinearMap ⊗ₘ sigop hφ (t - s))
        (tenSwap (star (hφ.psi t s a))) :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rankOne
  simp_rw [map_sum, Psi.adjoint_rank_one, star_sum, map_sum]

private theorem one_to_continuous_linear_map : LinearMap.toContinuousLinearMap (1 : ℍ →ₗ[ℂ] ℍ) = 1 :=
  rfl

theorem Qam.reflexive_eq_rankOne [hφ : φ.IsFaithfulPosMap] (a b : ℍ) :
    Qam.reflIdempotent hφ (|a⟩⟨b|) 1 = LinearMap.mulLeft ℂ (a * bᴴ) :=
  by
  have : ∀ x y : ℍ, ⟪x, y⟫_ℂ = φ (star x * y) := Module.Dual.IsFaithfulPosMap.inner_eq
  rw [LinearMap.mulLeft_mul, ← lmul_eq_mul bᴴ, ← star_eq_conjTranspose, ←
    lmul_adjoint]
  exact schurMul_one_right_rankOne _ _

theorem Qam.reflexive'_eq_rankOne [hφ : φ.IsFaithfulPosMap] (a b : ℍ) :
    Qam.reflIdempotent hφ 1 |a⟩⟨b| = LinearMap.mulRight ℂ (hφ.sig (-1) bᴴ * a) :=
  by
  simp_rw [← ext_inner_map]
  intro u
  let f := @Module.Dual.IsFaithfulPosMap.orthonormalBasis n _ _ φ hφ
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm f, map_sum, LinearMap.sum_apply]
  simp_rw [Qam.RankOne.reflIdempotent_eq, LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, LinearMap.mulRight_apply, sum_inner,
    InnerProductSpace.Core.inner_smul_left, Module.Dual.IsFaithfulPosMap.inner_right_conj hφ _ a,
    Module.Dual.IsFaithfulPosMap.inner_right_conj hφ _ b, inner_conj_symm,
    OrthonormalBasis.sum_inner_mul_inner, ← Module.Dual.IsFaithfulPosMap.inner_right_conj,
    Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg, PosDef.rpow_one_eq_self,
    PosDef.rpow_neg_one_eq_inv_self, Matrix.mul_assoc]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem map_sig_star [hφ : φ.IsFaithfulPosMap] (t s : ℝ) (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
    star (((hφ.sig t).toLinearMap ⊗ₘ sigop hφ s) x) =
      ((hφ.sig (-t)).toLinearMap ⊗ₘ sigop hφ (-s)) (star x) :=
x.induction_on
  (by simp only [star_zero, map_zero])
  (fun _ _ =>
    by simp only [map_tmul, tensor_op_star_apply, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
    LinearMap.comp_apply, op_apply, unop_apply, MulOpposite.unop_op, MulOpposite.op_unop,
    LinearEquiv.coe_toLinearMap, sigop, star_eq_conjTranspose])
  (fun z w hz hw => by simp only [_root_.map_add, hz, hw, StarAddMonoid.star_add])

theorem op_sig_unop_comp [hφ : φ.IsFaithfulPosMap] (t s : ℝ) : sigop hφ t ∘ₗ sigop hφ s = sigop hφ (t + s) :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp only [LinearMap.comp_apply, sigop, unop_op, Module.Dual.IsFaithfulPosMap.sig_apply_sig,
    LinearEquiv.coe_toLinearMap]

theorem map_sig_injective [hφ : φ.IsFaithfulPosMap] (t s : ℝ) :
    Function.Injective ⇑((hφ.sig t).toLinearMap ⊗ₘ sigop hφ s) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        ((hφ.sig (-t)).toLinearMap ⊗ₘ sigop hφ (-s))
          (((hφ.sig t).toLinearMap ⊗ₘ sigop hφ s) a) :=
    by
    intro a
    simp only [← LinearMap.comp_apply, ← map_comp, op_sig_unop_comp,
      Module.Dual.IsFaithfulPosMap.sig_comp_sig, neg_add_self,
      Module.Dual.IsFaithfulPosMap.sig_zero', LinearMap.one_comp, op_comp_unop,
      TensorProduct.map_one, LinearMap.one_apply]
    simp only [LinearEquiv.coe_toLinearMap_one, sigop, Module.Dual.IsFaithfulPosMap.sig_zero']
    simp only [LinearMap.id_comp, op_comp_unop, LinearMap.one_eq_id, TensorProduct.map_id]
    rfl
  rw [this a]
  simp_rw [h]
  rw [← this b]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem map_sig_eq [hφ : φ.IsFaithfulPosMap] (t s : ℝ) :
    TensorProduct.map (hφ.sig t).toLinearMap (sigop hφ s) =
      LinearMap.mulLeft ℂ
          (hφ.matrixIsPosDef.rpow (-t) ⊗ₜ
            (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.matrixIsPosDef.rpow s)) ∘ₗ
        LinearMap.mulRight ℂ
          (hφ.matrixIsPosDef.rpow t ⊗ₜ
            (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.matrixIsPosDef.rpow (-s))) :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  let b' := (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) b
  have : b = (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) b' := rfl
  simp only [this, map_tmul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, Algebra.TensorProduct.tmul_mul_tmul, sigop, unop_op,
    Module.Dual.IsFaithfulPosMap.sig_apply, LinearMap.coe_mk, AddHom.coe_mk, ← MulOpposite.op_mul,
    Matrix.mul_assoc, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv, MulOpposite.coe_opLinearEquiv_symm, unop_apply, op_apply,
    MulOpposite.unop_op]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem map_sig_mulLeft_injective [hφ : φ.IsFaithfulPosMap] (t s : ℝ) :
    Function.Injective
      (LinearMap.mulLeft ℂ
        (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
          (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.matrixIsPosDef.rpow s))) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        (LinearMap.mulLeft ℂ
            (hφ.matrixIsPosDef.rpow (-t) ⊗ₜ[ℂ]
              (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.matrixIsPosDef.rpow (-s))))
          (LinearMap.mulLeft ℂ
            (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
              (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.matrixIsPosDef.rpow s))
            a) :=
    by
    intro a
    simp_rw [← LinearMap.comp_apply, ← LinearMap.mulLeft_mul, Algebra.TensorProduct.tmul_mul_tmul,
      op_apply, ← MulOpposite.op_mul, PosDef.rpow_mul_rpow, neg_add_self, add_neg_self,
      PosDef.rpow_zero, MulOpposite.op_one, ← Algebra.TensorProduct.one_def, LinearMap.mulLeft_one,
      LinearMap.id_apply]
  rw [this a, h, ← this]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem map_sig_mulRight_injective [hφ : φ.IsFaithfulPosMap] (t s : ℝ) :
    Function.Injective
      (LinearMap.mulRight ℂ
        (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
          (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.matrixIsPosDef.rpow s))) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        (LinearMap.mulRight ℂ
            (hφ.matrixIsPosDef.rpow (-t) ⊗ₜ[ℂ]
              (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.matrixIsPosDef.rpow (-s))))
          (LinearMap.mulRight ℂ
            (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
              (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.matrixIsPosDef.rpow s))
            a) :=
    by
    intro a
    simp_rw [← LinearMap.comp_apply, ← LinearMap.mulRight_mul, Algebra.TensorProduct.tmul_mul_tmul,
      op_apply, ← MulOpposite.op_mul, PosDef.rpow_mul_rpow, neg_add_self, add_neg_self,
      PosDef.rpow_zero, MulOpposite.op_one, ← Algebra.TensorProduct.one_def,
      LinearMap.mulRight_one, LinearMap.id_apply]
  rw [this a, h, ← this]

theorem LinearMap.matrix.mulRight_adjoint [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    LinearMap.adjoint (LinearMap.mulRight ℂ x) = LinearMap.mulRight ℂ (hφ.sig (-1) xᴴ) :=
  by
  symm
  rw [@LinearMap.eq_adjoint_iff ℂ _]
  intro a b
  simp_rw [LinearMap.mulRight_apply, Module.Dual.IsFaithfulPosMap.sig_apply,
    neg_neg, PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self, ←
    Module.Dual.IsFaithfulPosMap.inner_left_conj]

theorem LinearMap.matrix.mulLeft_adjoint [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    LinearMap.adjoint (LinearMap.mulLeft ℂ x) = LinearMap.mulLeft ℂ xᴴ :=
  by
  symm
  rw [@LinearMap.eq_adjoint_iff ℂ _]
  intro a b
  simp_rw [LinearMap.mulLeft_apply, ←
    Module.Dual.IsFaithfulPosMap.inner_right_hMul]

theorem Qam.ir_refl_iff_ir_refl'_of_real [hφ : φ.IsFaithfulPosMap] {A : ℍ →ₗ[ℂ] ℍ} (hA : A.IsReal) (p : Prop) [Decidable p] :
    Qam.reflIdempotent hφ A 1 = ite p 1 0 ↔ Qam.reflIdempotent hφ 1 A = ite p 1 0 :=
  by
  rw [LinearMap.isReal_iff] at hA
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rankOne
  simp_rw [LinearMap.real_sum, rankOne_real_apply] at hA
  nth_rw 1 [← hA]
  simp_rw [map_sum, LinearMap.sum_apply, Qam.reflexive_eq_rankOne, Qam.reflexive'_eq_rankOne, ←
    conjTranspose_mul, ← @LinearMap.matrix.mulLeft_adjoint n _ _ φ _, ← map_sum]
  have t3 : ∀ a : l(ℍ), LinearMap.adjoint a = ite p 1 0 ↔ a = ite p 1 0 :=
    by
    intro a
    refine' ⟨fun h => _, fun h => _⟩
    · apply_fun LinearMap.adjoint at h
      simp_rw [LinearMap.adjoint_adjoint, ← LinearMap.star_eq_adjoint, star_ite, star_one,
        star_zero] at h
      exact h
    · rw [h]
      simp_rw [← LinearMap.star_eq_adjoint, star_ite, star_one, star_zero]
  simp_rw [t3, LinearMap.mulLeft_sum, LinearMap.mulRight_sum,
    LinearMap.mulLeft_eq_one_or_zero_iff_mulRight]

theorem Qam.realOfSelfAdjointSymm [hφ : φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ)
    (h1 : LinearMap.adjoint A = A) (h2 : symmMap ℂ ℍ _ A = A) : A.IsReal :=
  by
  rw [LinearMap.isReal_iff]
  rw [symmMap_apply, ← LinearMap.star_eq_adjoint, star_eq_iff_star_eq,
    LinearMap.star_eq_adjoint, h1] at h2
  exact h2.symm

theorem Qam.self_adjoint_of_symm_real [hφ : φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ)
    (h1 : symmMap ℂ ℍ _ A = A) (h2 : A.IsReal) : LinearMap.adjoint A = A :=
  by
  rw [LinearMap.isReal_iff] at h2
  rw [symmMap_apply, h2] at h1
  exact h1

theorem Qam.symm_of_real_self_adjoint [hφ : φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) (h1 : A.IsReal)
    (h2 : LinearMap.adjoint A = A) : symmMap ℂ ℍ _ A = A :=
  by
  rw [symmMap_apply, (LinearMap.isReal_iff _).mp h1]
  exact h2

theorem Qam.self_adjoint_symm_real_tfae [hφ : φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) :
    List.TFAE
      [LinearMap.adjoint A = A ∧ symmMap ℂ ℍ _ A = A, LinearMap.adjoint A = A ∧ A.IsReal,
        symmMap ℂ ℍ _ A = A ∧ A.IsReal] :=
  by
  tfae_have 1 → 2
  · intro h
    exact ⟨h.1, Qam.realOfSelfAdjointSymm A h.1 h.2⟩
  tfae_have 2 → 3
  · intro h
    exact ⟨Qam.symm_of_real_self_adjoint A h.2 h.1, h.2⟩
  tfae_have 3 → 1
  · intro h
    exact ⟨Qam.self_adjoint_of_symm_real A h.1 h.2, h.1⟩
  tfae_finish

set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 0 in
theorem Psi.real [hφ : φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) (t s : ℝ) :
    hφ.psi t s A.real =
      ((hφ.sig (2 * t)).toLinearMap ⊗ₘ sigop hφ (1 - 2 * s)) (star (hφ.psi t s A)) :=
  by
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rankOne
  simp_rw [LinearMap.real_sum, map_sum, star_sum]
  simp only [map_sum, rankOne_real_apply, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tensor_op_star_apply, unop_op,
    conjTranspose_conjTranspose, map_tmul, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, sigop, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, star_eq_conjTranspose]
  simp only [neg_add_rev, neg_neg, two_mul, add_assoc, add_neg_cancel_right]
  simp_rw [sub_add, sub_eq_add_neg, add_neg_self, add_zero,
    add_assoc, add_neg_self, add_zero]

theorem sigop_zero [hφ : φ.IsFaithfulPosMap] : sigop hφ 0 = 1 := by
  rw [sigop, Module.Dual.IsFaithfulPosMap.sig_zero']
  simp only [LinearEquiv.coe_toLinearMap_one, LinearMap.id_comp, op_comp_unop]

theorem Qam.isReal_and_idempotent_iff_psi_orthogonal_projection [hφ : φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) :
    Qam.reflIdempotent hφ A A = A ∧ A.IsReal ↔
      IsIdempotentElem (hφ.psi 0 (1 / 2) A) ∧
        star (hφ.psi 0 (1 / 2) A) = hφ.psi 0 (1 / 2) A :=
  by
  nth_rw 1 [← Function.Injective.eq_iff (LinearEquiv.injective (hφ.psi 0 (1 / 2)))]
  rw [LinearMap.isReal_iff, ← Function.Injective.eq_iff (hφ.psi 0 (1 / 2)).injective,
    Psi.reflIdempotent, Psi.real, MulZeroClass.mul_zero, Module.Dual.IsFaithfulPosMap.sig_zero',
    one_div, mul_inv_cancel (two_ne_zero' ℝ), sub_self, sigop_zero]
  simp only [LinearEquiv.coe_toLinearMap_one, LinearMap.one_eq_id, TensorProduct.map_id,
    LinearMap.id_apply, IsIdempotentElem]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem sig_map_sigop_comp_psi [hφ : φ.IsFaithfulPosMap] (t s r q : ℝ) :
    TensorProduct.map (hφ.sig t).toLinearMap (sigop hφ s) ∘ hφ.psi r q =
      hφ.psi (r + t) (q - s) :=
  by
  ext x
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp_rw [Function.comp_apply, map_sum, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, map_tmul, sigop, LinearMap.comp_apply, unop_op,
    LinearEquiv.coe_toLinearMap, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, neg_sub, sub_eq_add_neg, add_comm]

theorem sig_map_sigop_apply_psi [hφ : φ.IsFaithfulPosMap] (t s r q : ℝ) (A : ℍ →ₗ[ℂ] ℍ) :
    (TensorProduct.map (hφ.sig t).toLinearMap (sigop hφ s)) (hφ.psi r q A) =
      hφ.psi (r + t) (q - s) A :=
  by
  have := @sig_map_sigop_comp_psi n _ _ φ _ t s r q
  simp_rw [Function.funext_iff, Function.comp_apply] at this
  exact this _

-- :TODO:
-- lemma qam.is_qam_iff_Psi_orthogonal_projection_and_swap (A : ℍ →ₗ[ℂ] ℍ) :
--   (qam.refl_idempotent hφ A A = A ∧ A.is_real ∧ qam.symm hφ A = A)
--     ↔ (is_idempotent_elem (hφ.Psi 0 (1/2) A)
--     ∧ star (hφ.Psi 0 (1/2) A) = hφ.Psi 0 (1/2) A
--       ∧ hφ.Psi 0 (1/2) A = ten_swap (hφ.Psi (1/2) 0 A)) :=
-- begin
--   rw [← and_assoc, qam.is_real_and_idempotent_iff_Psi_orthogonal_projection,
--     list.tfae.out (qam.self_adjoint_symm_real_tfae hφ A) 0 2,
--     and_rotate, and_comm A.is_real],
--   -- have : ∀ t, sigop hφ t = op ∘ₗ sig hφ.matrixIsPosDef t ∘ₗ unop := λ _, rfl,
--   refine ⟨λ h, ⟨h.2, _⟩, λ h, ⟨_, h.1⟩⟩,
--   { rcases h with ⟨h1, h2, h3⟩,
--     rw qam.symm_iff_symm' at h1,
--     apply_fun hφ.Psi 0 (1/2) at h1,
--     simp_rw [Psi.symmetric' hφ] at h1,
--     ring_nf at h1,
--     simp_rw [← linear_map.comp_apply, ← ten_swap_sig, linear_map.comp_apply,
--       sig_map_sigop_apply_Psi, sub_self, zero_add] at h1,
--     exact h1.symm, },
--   { rw qam.symm_iff_symm',
--     apply_fun hφ.Psi 0 (1/2) using (linear_equiv.injective _),
--     simp_rw [Psi.symmetric' hφ],
--     ring_nf,
--     simp_rw [← linear_map.comp_apply, ← ten_swap_sig, linear_map.comp_apply,
--       sig_map_sigop_apply_Psi, sub_self, zero_add, h.2], },
-- end
