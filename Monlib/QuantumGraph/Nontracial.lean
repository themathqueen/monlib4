/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyIps.Nontracial
import LinearAlgebra.MyIps.MatIps
import LinearAlgebra.MyIps.TensorHilbert
import LinearAlgebra.IsReal
import LinearAlgebra.MyIps.Frob
import LinearAlgebra.TensorFinite
import LinearAlgebra.MyIps.OpUnop
import LinearAlgebra.LmulRmul
import QuantumGraph.SchurIdempotent
import QuantumGraph.Symm

#align_import quantum_graph.nontracial

/-!
 # Quantum graphs: quantum adjacency matrices

 This file defines the quantum adjacency matrix of a quantum graph.
-/


variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

open scoped TensorProduct BigOperators Kronecker

local notation "ℍ" => Matrix n n ℂ

local notation "⊗K" => Matrix (n × n) (n × n) ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "L(" x ")" => x →L[ℂ] x

local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable {φ : Module.Dual ℂ ℍ} [hφ : Fact φ.IsFaithfulPosMap] {ψ : Module.Dual ℂ (Matrix p p ℂ)}
  (hψ : ψ.IsFaithfulPosMap)

open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ) :
    (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "υ⁻¹" =>
  ((TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ)).symm :
    Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ)

local notation "ϰ" =>
  (↑(TensorProduct.comm ℂ (Matrix n n ℂ) ℂ) : Matrix n n ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "ϰ⁻¹" =>
  ((TensorProduct.comm ℂ (Matrix n n ℂ) ℂ).symm : ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] ℂ)

local notation "τ" => (TensorProduct.lid ℂ (Matrix n n ℂ) : ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

local notation "τ⁻¹" =>
  ((TensorProduct.lid ℂ (Matrix n n ℂ)).symm : Matrix n n ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

open scoped Functional

noncomputable def Qam.reflIdempotent (hφ : φ.IsFaithfulPosMap) : l(ℍ) →ₗ[ℂ] l(ℍ) →ₗ[ℂ] l(ℍ) :=
  letI := Fact.mk hφ
  schurIdempotent

theorem Qam.RankOne.reflIdempotent_eq [hφ : Fact φ.IsFaithfulPosMap] (a b c d : ℍ) :
    Qam.reflIdempotent hφ.elim ↑|a⟩⟨b| ↑|c⟩⟨d| = |a ⬝ c⟩⟨b ⬝ d| :=
  schurIdempotent.apply_rankOne a b c d

open TensorProduct

-- noncomputable def qam.symm (hφ : φ.is_faithful_pos_map) :
--   l(ℍ) ≃ₗ[ℂ] l(ℍ) :=
-- begin
--   letI := fact.mk hφ,
--   exact ((linear_equiv.symm_map ℂ ℍ : l(ℍ) ≃ₗ[ℂ] l(ℍ))),
-- end
theorem Finset.sum_fin_one {α : Type _} [AddCommMonoid α] (f : Fin 1 → α) : ∑ i, f i = f 0 := by
  simp only [Fintype.univ_ofSubsingleton, Fin.mk_zero, Finset.sum_singleton]

theorem rankOne_real_apply [hφ : Fact φ.IsFaithfulPosMap] (a b : ℍ) :
    (|a⟩⟨b| : ℍ →ₗ[ℂ] ℍ).Real = |aᴴ⟩⟨hφ.elim.sig (-1) bᴴ| :=
  by
  have :=
    @Pi.rankOneLm_real_apply _ _ _ _ _ _ (fun i : Fin 1 => φ) (fun i => hφ) (fun i : Fin 1 => a)
      fun i : Fin 1 => b
  simp only [LinearMap.ext_iff, Function.funext_iff, Fin.forall_fin_one, ← rankOneLm_eq_rankOne,
    rankOneLm_apply, LinearMap.real_eq] at this ⊢
  simp only [Pi.star_apply, Pi.smul_apply, PiLp.inner_apply,
    Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks, Finset.sum_fin_one] at this
  intros
  exact this (fun _ => x) _ _

theorem Qam.RankOne.symmetric_eq (a b : ℍ) :
    (LinearEquiv.symmMap ℂ ℍ) |a⟩⟨b| = |hφ.elim.sig (-1) bᴴ⟩⟨aᴴ| := by
  simp_rw [LinearEquiv.symmMap_apply, rankOne_real_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint]

theorem Qam.RankOne.symmetric'_eq (a b : ℍ) :
    (LinearEquiv.symmMap ℂ ℍ).symm |a⟩⟨b| = |bᴴ⟩⟨hφ.elim.sig (-1) aᴴ| := by
  simp_rw [LinearEquiv.symmMap_symm_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    rankOneLm_eq_rankOne, rankOne_real_apply]

theorem Qam.symm_adjoint_eq_symm'_of_adjoint [hφ : Fact φ.IsFaithfulPosMap] (x : l(ℍ)) :
    (LinearEquiv.symmMap ℂ ℍ x).adjoint = (LinearEquiv.symmMap ℂ ℍ).symm x.adjoint :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp_rw [map_sum, ← rankOneLm_eq_rankOne, rankOneLm_adjoint, rankOneLm_eq_rankOne,
    Qam.RankOne.symmetric_eq, Qam.RankOne.symmetric'_eq, ← rankOneLm_eq_rankOne, rankOneLm_adjoint]

private theorem commute.adjoint_adjoint {K E : Type _} [IsROrC K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [CompleteSpace E] {f g : E →L[K] E} :
    Commute f.adjoint g.adjoint ↔ Commute f g :=
  commute_star_star

private theorem commute.adjoint_adjoint_lm {K E : Type _} [IsROrC K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [FiniteDimensional K E] {f g : E →ₗ[K] E} :
    Commute f.adjoint g.adjoint ↔ Commute f g :=
  commute_star_star

theorem LinearMap.adjoint_real_eq (f : ℍ →ₗ[ℂ] ℍ) :
    f.adjoint.Real =
      (hφ.elim.sig 1).toLinearMap ∘ₗ f.Real.adjoint ∘ₗ (hφ.elim.sig (-1)).toLinearMap :=
  by
  rw [← ext_inner_map]
  intro u
  nth_rw_lhs 1 [Nontracial.inner_symm]
  simp_rw [LinearMap.real_eq, star_eq_conj_transpose, conj_transpose_conj_transpose,
    LinearMap.adjoint_inner_right]
  nth_rw_lhs 1 [Nontracial.inner_symm]
  simp_rw [conj_transpose_conj_transpose, ← Module.Dual.IsFaithfulPosMap.sig_conjTranspose, ←
    star_eq_conj_transpose, ← LinearMap.real_eq f, LinearMap.comp_apply]
  simp_rw [← LinearMap.adjoint_inner_left f.real, ← AlgEquiv.toLinearMap_apply, ←
    LinearMap.adjoint_inner_left (hφ.elim.sig 1).toLinearMap,
    Module.Dual.IsFaithfulPosMap.sig_adjoint]

theorem Module.Dual.IsFaithfulPosMap.sig_trans_sig (x y : ℝ) :
    (hφ.elim.sig y).trans (hφ.elim.sig x) = hφ.elim.sig (x + y) :=
  by
  ext1
  simp_rw [AlgEquiv.trans_apply, Module.Dual.IsFaithfulPosMap.sig_apply_sig]

theorem Module.Dual.IsFaithfulPosMap.sig_comp_sig (x y : ℝ) :
    (hφ.elim.sig x).toLinearMap.comp (hφ.elim.sig y).toLinearMap =
      (hφ.elim.sig (x + y)).toLinearMap :=
  by
  ext1 <;>
    simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      Module.Dual.IsFaithfulPosMap.sig_apply_sig]

theorem Module.Dual.IsFaithfulPosMap.sig_zero' : hφ.elim.sig 0 = 1 :=
  by
  rw [AlgEquiv.ext_iff]
  intros
  rw [Module.Dual.IsFaithfulPosMap.sig_zero]
  rfl

private theorem comp_sig_eq (t : ℝ) (f g : ℍ →ₗ[ℂ] ℍ) :
    f ∘ₗ (hφ.elim.sig t).toLinearMap = g ↔ f = g ∘ₗ (hφ.elim.sig (-t)).toLinearMap :=
  by
  constructor <;> rintro rfl
  all_goals rw [LinearMap.comp_assoc, Module.Dual.IsFaithfulPosMap.sig_comp_sig]
  on_goal 1 => rw [add_neg_self]
  on_goal 2 => rw [neg_add_self]
  all_goals
    rw [Module.Dual.IsFaithfulPosMap.sig_zero', AlgEquiv.one_toLinearMap, LinearMap.comp_one]

theorem LinearMap.IsReal.adjoint_isReal_iff_commute_with_sig {f : ℍ →ₗ[ℂ] ℍ} (hf : f.IsReal) :
    f.adjoint.IsReal ↔ Commute f (hφ.elim.sig 1).toLinearMap :=
  by
  rw [LinearMap.isReal_iff] at hf
  let σ := hφ.elim.sig
  have : Commute f (σ 1).toLinearMap ↔ Commute f.adjoint (σ 1).toLinearMap :=
    by
    simp_rw [σ]
    nth_rw_rhs 1 [← Module.Dual.IsFaithfulPosMap.sig_adjoint]
    rw [commute.adjoint_adjoint_lm]
  rw [this]
  clear this
  rw [LinearMap.isReal_iff, LinearMap.adjoint_real_eq, hf, ← LinearMap.comp_assoc, comp_sig_eq,
    neg_neg]
  simp_rw [Commute, SemiconjBy, LinearMap.mul_eq_comp, @eq_comm _ _ ((σ 1).toLinearMap ∘ₗ _)]

theorem sig_apply_pos_def_matrix_hMul (t : ℝ) (x : ℍ) :
    hφ.elim.sig t (hφ.elim.matrixIsPosDef.rpow t ⬝ x) = x ⬝ hφ.elim.matrixIsPosDef.rpow t := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, ← Matrix.mul_assoc, pos_def.rpow_mul_rpow,
    neg_add_self, pos_def.rpow_zero, Matrix.one_mul]

theorem sig_apply_pos_def_matrix_mul' (x : ℍ) : hφ.elim.sig 1 (φ.Matrix ⬝ x) = x ⬝ φ.Matrix :=
  by
  nth_rw_rhs 1 [← pos_def.rpow_one_eq_self hφ.elim.matrix_is_pos_def]
  rw [← sig_apply_pos_def_matrix_hMul, pos_def.rpow_one_eq_self]

theorem sig_apply_matrix_hMul_pos_def (t : ℝ) (x : ℍ) :
    hφ.elim.sig t (x ⬝ hφ.elim.matrixIsPosDef.rpow (-t)) = hφ.elim.matrixIsPosDef.rpow (-t) ⬝ x :=
  by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, pos_def.rpow_mul_rpow,
    neg_add_self, pos_def.rpow_zero, Matrix.mul_one]

theorem sig_apply_matrix_hMul_pos_def' (x : ℍ) : hφ.elim.sig (-1) (x ⬝ φ.Matrix) = φ.Matrix ⬝ x :=
  by
  nth_rw_rhs 1 [← pos_def.rpow_one_eq_self hφ.elim.matrix_is_pos_def]
  nth_rw_rhs 1 [← neg_neg (1 : ℝ)]
  rw [← sig_apply_matrix_hMul_pos_def, neg_neg, pos_def.rpow_one_eq_self]

theorem sig_apply_matrix_hMul_pos_def'' (x : ℍ) : hφ.elim.sig 1 (x ⬝ φ.Matrix⁻¹) = φ.Matrix⁻¹ ⬝ x :=
  by
  nth_rw_rhs 1 [← pos_def.rpow_neg_one_eq_inv_self hφ.elim.matrix_is_pos_def]
  rw [← sig_apply_matrix_hMul_pos_def, pos_def.rpow_neg_one_eq_inv_self]

theorem sig_apply_basis (i : n × n) :
    hφ.elim.sig 1 (hφ.elim.Basis i) =
      φ.Matrix⁻¹ ⬝ e_{i.1,i.2} ⬝ hφ.elim.matrixIsPosDef.rpow (1 / 2) :=
  by
  rw [Module.Dual.IsFaithfulPosMap.basis_apply]
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, pos_def.rpow_mul_rpow,
    pos_def.rpow_neg_one_eq_inv_self]
  norm_num

theorem Qam.symm'_symm_real_eq_adjoint_tFAE [hφ : Fact φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) :
    TFAE
      [LinearEquiv.symmMap ℂ ℍ A = A, (LinearEquiv.symmMap ℂ ℍ).symm A = A, A.Real = A.adjoint,
        ∀ x y, φ (A x ⬝ y) = φ (x ⬝ A y)] :=
  by
  tfae_have 1 ↔ 2
  · simp_rw [LinearEquiv.symmMap_symm_apply, LinearEquiv.symmMap_apply, ← LinearMap.star_eq_adjoint,
      star_eq_iff_star_eq]
    rw [LinearMap.real_inj_eq, LinearMap.real_real]
  tfae_have 2 ↔ 3
  · rw [LinearEquiv.symmMap_symm_apply]
    nth_rw_lhs 1 [LinearMap.real_inj_eq]
    rw [LinearMap.real_real, eq_comm]
  tfae_have 3 → 4
  · intro h x y
    calc
      φ (A x ⬝ y) = ⟪(A x)ᴴ, y⟫_ℂ := by
        rw [Module.Dual.IsFaithfulPosMap.inner_eq, conj_transpose_conj_transpose]
      _ = ⟪A.real xᴴ, y⟫_ℂ := by
        simp_rw [LinearMap.real_eq, star_eq_conj_transpose, conj_transpose_conj_transpose]
      _ = ⟪A.adjoint xᴴ, y⟫_ℂ := by rw [h]
      _ = ⟪xᴴ, A y⟫_ℂ := by rw [LinearMap.adjoint_inner_left]
      _ = φ (x ⬝ A y) := by
        rw [Module.Dual.IsFaithfulPosMap.inner_eq, conj_transpose_conj_transpose]
  tfae_have 4 → 3
  · intro h
    rw [LinearMap.ext_iff_inner_map]
    intro u
    rw [LinearMap.adjoint_inner_left]
    nth_rw_rhs 1 [Module.Dual.IsFaithfulPosMap.inner_eq]
    rw [← h, LinearMap.real_eq, Module.Dual.IsFaithfulPosMap.inner_eq, star_eq_conj_transpose,
      conj_transpose_conj_transpose]
    rfl
  tfae_finish

theorem sig_comp_eq_iff (t : ℝ) (A B : ℍ →ₗ[ℂ] ℍ) :
    (hφ.elim.sig t).toLinearMap.comp A = B ↔ A = (hφ.elim.sig (-t)).toLinearMap.comp B :=
  by
  constructor <;> rintro rfl
  all_goals rw [← LinearMap.comp_assoc, Module.Dual.IsFaithfulPosMap.sig_comp_sig]
  on_goal 1 => rw [neg_add_self]
  on_goal 2 => rw [add_neg_self]
  all_goals
    rw [Module.Dual.IsFaithfulPosMap.sig_zero', AlgEquiv.one_toLinearMap, LinearMap.one_comp]

theorem Module.Dual.IsFaithfulPosMap.sig_real {t : ℝ} :
    (hφ.elim.sig t).toLinearMap.Real = (hφ.elim.sig (-t)).toLinearMap :=
  by
  ext1
  simp_rw [LinearMap.real_eq, AlgEquiv.toLinearMap_apply, star_eq_conj_transpose,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, conj_transpose_conj_transpose]

theorem Qam.commute_with_sig_iff_symm_eq_symm' {A : ℍ →ₗ[ℂ] ℍ} :
    LinearEquiv.symmMap ℂ ℍ A = (LinearEquiv.symmMap ℂ ℍ).symm A ↔
      Commute A (hφ.elim.sig 1).toLinearMap :=
  by
  rw [LinearEquiv.symmMap_apply, LinearEquiv.symmMap_symm_apply, LinearMap.adjoint_real_eq, eq_comm,
    sig_comp_eq_iff, ← star_inj]
  simp_rw [LinearMap.star_eq_adjoint, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    Module.Dual.IsFaithfulPosMap.sig_adjoint]
  rw [LinearMap.real_inj_eq]
  simp_rw [LinearMap.real_comp, LinearMap.real_real, Module.Dual.IsFaithfulPosMap.sig_real, neg_neg]
  rw [eq_comm]
  rfl

theorem Qam.commute_with_sig_of_symm {A : ℍ →ₗ[ℂ] ℍ} (hA : LinearEquiv.symmMap ℂ ℍ A = A) :
    Commute A (hφ.elim.sig 1).toLinearMap := by
  rw [← Qam.commute_with_sig_iff_symm_eq_symm', hA, LinearEquiv.eq_symm_apply, hA]

-- `τ ϰ (1 ⊗ η⋆ m) (m⋆ η ⊗ 1) τ⁻¹ = 1`
theorem Qam.symm_one [hφ : Fact φ.IsFaithfulPosMap] : LinearEquiv.symmMap ℂ ℍ 1 = (1 : l(ℍ)) := by
  rw [LinearEquiv.symmMap_apply, LinearMap.real_one, LinearMap.adjoint_one]

def Qam (φ : Module.Dual ℂ ℍ) [hφ : Fact φ.IsFaithfulPosMap] (x : l(ℍ)) :=
  Qam.reflIdempotent hφ.elim x x = x

def Qam.IsSelfAdjoint [hφ : Fact φ.IsFaithfulPosMap] (x : l(ℍ)) : Prop :=
  x.adjoint = x

def Qam.IsSymm [hφ : Fact φ.IsFaithfulPosMap] (x : l(ℍ)) : Prop :=
  LinearEquiv.symmMap ℂ ℍ x = x

def QamLmNontracialIsReflexive (x : ℍ →ₗ[ℂ] ℍ) : Prop :=
  Qam.reflIdempotent hφ.elim x 1 = (1 : l(ℍ))

def QamLmNontracialIsUnreflexive (x : ℍ →ₗ[ℂ] ℍ) : Prop :=
  Qam.reflIdempotent hφ.elim x 1 = (0 : l(ℍ))

theorem stdBasisMatrix_squash (i j k l : n) (x : Matrix n n ℂ) :
    e_{i,j} ⬝ x ⬝ e_{k,l} = x j k • e_{i,l} := by
  ext1
  simp_rw [mul_apply, Pi.smul_apply, std_basis_matrix, smul_ite, mul_boole, boole_mul, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, smul_eq_mul, mul_one, MulZeroClass.mul_zero]
  simp_rw [← ite_and, and_comm' (l = j_1) (i = i_1)]

theorem rankOneLm_smul {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) (r : 𝕜) : (rankOneLm x (r • y) : E →ₗ[𝕜] E) = starRingEnd 𝕜 r • rankOneLm x y := by
  rw [rankOneLm, rankOne.smul_apply] <;> rfl

theorem smul_rankOneLm {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) (r : 𝕜) : (rankOneLm (r • x) y : E →ₗ[𝕜] E) = r • rankOneLm x y := by
  rw [rankOneLm, rankOne.apply_smul] <;> rfl

private theorem nontracial_basis_apply {Q : ℍ} (hQ : Q.PosDef) (i j k l : n) :
    (e_{i,j} ⬝ hQ.rpow (-(1 / 2))) k l = ite (i = k) (hQ.rpow (-(1 / 2)) j l) 0 := by
  simp_rw [mul_apply, std_basis_matrix, boole_mul, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

noncomputable def sigop (hφ : φ.IsFaithfulPosMap) (t : ℝ) : l(ℍᵐᵒᵖ) :=
  (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) ∘ₗ (hφ.sig t).toLinearMap ∘ₗ (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ)

private theorem Psi.symmetric_rank_one (a b : ℍ) (t s : ℝ) :
    hφ.elim.psi t s (LinearEquiv.symmMap ℂ ℍ |a⟩⟨b|) =
      ((hφ.elim.sig (t + s - 1)).toLinearMap ⊗ₘ sigop hφ.elim (-t - s))
        (tenSwap (hφ.elim.psi t s |a⟩⟨b|)) :=
  by
  simp_rw [sigop, Qam.RankOne.symmetric_eq, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tenSwap_apply, map_tmul, LinearMap.comp_apply,
    unop_apply, op_apply, MulOpposite.unop_op, AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, Module.Dual.IsFaithfulPosMap.sig_apply_sig,
    conj_transpose_conj_transpose, sub_add_comm, ← sub_eq_add_neg, sub_sub_cancel_left]
  ring_nf

theorem Psi.symmetric (a : l(ℍ)) (t s : ℝ) :
    hφ.elim.psi t s (LinearEquiv.symmMap ℂ ℍ a) =
      ((hφ.elim.sig (t + s - 1)).toLinearMap ⊗ₘ sigop hφ.elim (-t - s))
        (tenSwap (hφ.elim.psi t s a)) :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one
  simp_rw [map_sum, Psi.symmetric_rank_one]

private theorem Psi.symmetric'_rank_one (a b : ℍ) (t s : ℝ) :
    hφ.elim.psi t s ((LinearEquiv.symmMap ℂ ℍ).symm |a⟩⟨b|) =
      ((hφ.elim.sig (t + s)).toLinearMap ⊗ₘ sigop hφ.elim (1 - t - s))
        (tenSwap (hφ.elim.psi t s |a⟩⟨b|)) :=
  by
  simp_rw [sigop, Qam.RankOne.symmetric'_eq, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tenSwap_apply, map_tmul, LinearMap.comp_apply,
    op_apply, unop_apply, MulOpposite.unop_op, AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose, neg_neg,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, conj_transpose_conj_transpose]
  ring_nf

theorem Psi.symmetric' (a : l(ℍ)) (t s : ℝ) :
    hφ.elim.psi t s ((LinearEquiv.symmMap ℂ ℍ).symm a) =
      ((hφ.elim.sig (t + s)).toLinearMap ⊗ₘ sigop hφ.elim (1 - t - s))
        (tenSwap (hφ.elim.psi t s a)) :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one
  simp_rw [map_sum, Psi.symmetric'_rank_one]

private theorem Psi.idempotent_rank_one (a b c d : ℍ) (t s : ℝ) :
    hφ.elim.psi t s (Qam.reflIdempotent hφ.elim ↑|a⟩⟨b| ↑|c⟩⟨d|) =
      hφ.elim.psi t s |a⟩⟨b| * hφ.elim.psi t s |c⟩⟨d| :=
  by
  simp_rw [Qam.RankOne.reflIdempotent_eq, Module.Dual.IsFaithfulPosMap.psi_apply,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_eq_mul,
    op_apply, ← MulOpposite.op_mul, mul_eq_mul, ← conj_transpose_mul, ← mul_eq_mul, _root_.map_mul]

theorem Psi.reflIdempotent (A B : l(ℍ)) (t s : ℝ) :
    hφ.elim.psi t s (Qam.reflIdempotent hφ.elim A B) = hφ.elim.psi t s A * hφ.elim.psi t s B :=
  by
  obtain ⟨Aα, Aβ, rfl⟩ := A.exists_sum_rank_one
  obtain ⟨Bα, Bβ, rfl⟩ := B.exists_sum_rank_one
  simp_rw [map_sum, LinearMap.sum_apply, map_sum, Psi.idempotent_rank_one, Finset.mul_sum,
    Finset.sum_mul]

theorem tenSwap_sig (x y : ℝ) :
    (tenSwap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ
        TensorProduct.map ((hφ.elim.sig x).toLinearMap : l(ℍ)) (sigop hφ.elim y : l(ℍᵐᵒᵖ)) =
      (((hφ.elim.sig y).toLinearMap : l(ℍ)) ⊗ₘ sigop hφ.elim x : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ tenSwap :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp only [LinearMap.comp_apply, map_tmul, tenSwap_apply, op_apply, unop_apply,
    MulOpposite.unop_op, MulOpposite.op_unop]
  rfl

private theorem Psi.adjoint_rank_one (a b : ℍ) (t s : ℝ) :
    hφ.elim.psi t s (|a⟩⟨b| : l(ℍ)).adjoint =
      ((hφ.elim.sig (t - s)).toLinearMap ⊗ₘ sigop hφ.elim (t - s))
        (tenSwap (star (hφ.elim.psi t s |a⟩⟨b|))) :=
  by
  simp_rw [← rankOneLm_eq_rankOne, sigop]
  rw [rankOneLm_adjoint]
  simp_rw [rankOneLm_eq_rankOne, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tensor_op_star_apply, unop_apply, op_apply,
    MulOpposite.unop_op, star_eq_conj_transpose, conj_transpose_conj_transpose, ←
    LinearMap.comp_apply]
  have := @tenSwap_sig n _ _ φ _
  simp_rw [sigop] at this
  simp_rw [← this, LinearMap.comp_apply, map_tmul, LinearMap.comp_apply, unop_apply,
    MulOpposite.unop_op, Module.Dual.IsFaithfulPosMap.sig_conjTranspose, AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, tenSwap_apply, op_apply, MulOpposite.unop_op]
  ring_nf

theorem Psi.adjoint (a : l(ℍ)) (t s : ℝ) :
    hφ.elim.psi t s a.adjoint =
      ((hφ.elim.sig (t - s)).toLinearMap ⊗ₘ sigop hφ.elim (t - s))
        (tenSwap (star (hφ.elim.psi t s a))) :=
  by
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one
  simp_rw [map_sum, Psi.adjoint_rank_one, star_sum, map_sum]

private theorem one_to_continuous_linear_map : (1 : ℍ →ₗ[ℂ] ℍ).toContinuousLinearMap = 1 :=
  rfl

theorem Qam.reflexive_eq_rankOne (a b : ℍ) :
    Qam.reflIdempotent hφ.elim |a⟩⟨b| 1 = LinearMap.mulLeft ℂ (a ⬝ bᴴ) :=
  by
  have : ∀ x y : ℍ, ⟪x, y⟫_ℂ = φ (star x * y) := Module.Dual.IsFaithfulPosMap.inner_eq
  rw [← mul_eq_mul, LinearMap.mulLeft_mul, ← lmul_eq_mul bᴴ, ← star_eq_conj_transpose, ←
    lmul_adjoint this]
  exact schurIdempotent_one_right_rankOne this _ _

theorem Qam.reflexive'_eq_rankOne (a b : ℍ) :
    Qam.reflIdempotent hφ.elim 1 |a⟩⟨b| = LinearMap.mulRight ℂ (hφ.elim.sig (-1) bᴴ ⬝ a) :=
  by
  simp_rw [← ext_inner_map]
  intro u
  let f := @Module.Dual.IsFaithfulPosMap.orthonormalBasis n _ _ φ _
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm f, map_sum, LinearMap.sum_apply]
  simp_rw [Qam.RankOne.reflIdempotent_eq, LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, LinearMap.mulRight_apply, mul_eq_mul, sum_inner,
    InnerProductSpace.Core.inner_smul_left, Module.Dual.IsFaithfulPosMap.inner_right_conj _ a,
    Module.Dual.IsFaithfulPosMap.inner_right_conj _ b, inner_conj_symm,
    OrthonormalBasis.sum_inner_mul_inner, ← Module.Dual.IsFaithfulPosMap.inner_right_conj,
    Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg, pos_def.rpow_one_eq_self,
    pos_def.rpow_neg_one_eq_inv_self, Matrix.mul_assoc]

theorem map_sig_star (t s : ℝ) (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
    star (((hφ.elim.sig t).toLinearMap ⊗ₘ sigop hφ.elim s) x) =
      ((hφ.elim.sig (-t)).toLinearMap ⊗ₘ sigop hφ.elim (-s)) (star x) :=
  by
  apply x.induction_on
  · simp only [star_zero, map_zero]
  · intros
    simp only [map_tmul, tensor_op_star_apply, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
      LinearMap.comp_apply, op_apply, unop_apply, MulOpposite.unop_op, MulOpposite.op_unop,
      AlgEquiv.toLinearMap_apply, sigop, star_eq_conj_transpose]
  · intro z w hz hw
    simp only [_root_.map_add, hz, hw, StarAddMonoid.star_add]

theorem op_sig_unop_comp (t s : ℝ) : sigop hφ.elim t ∘ₗ sigop hφ.elim s = sigop hφ.elim (t + s) :=
  by
  rw [LinearMap.ext_iff]
  intro x
  simp only [LinearMap.comp_apply, sigop, unop_op, Module.Dual.IsFaithfulPosMap.sig_apply_sig,
    AlgEquiv.toLinearMap_apply]

theorem map_sig_injective (t s : ℝ) :
    Function.Injective ⇑((hφ.elim.sig t).toLinearMap ⊗ₘ sigop hφ.elim s) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        ((hφ.elim.sig (-t)).toLinearMap ⊗ₘ sigop hφ.elim (-s))
          (((hφ.elim.sig t).toLinearMap ⊗ₘ sigop hφ.elim s) a) :=
    by
    intro a
    simp only [← LinearMap.comp_apply, ← map_comp, op_sig_unop_comp,
      Module.Dual.IsFaithfulPosMap.sig_comp_sig, neg_add_self,
      Module.Dual.IsFaithfulPosMap.sig_zero', LinearMap.one_comp, op_comp_unop,
      TensorProduct.map_one, LinearMap.one_apply, AlgEquiv.one_toLinearMap]
    simp only [sigop, Module.Dual.IsFaithfulPosMap.sig_zero', AlgEquiv.one_toLinearMap,
      LinearMap.one_comp, op_comp_unop, TensorProduct.map_one, LinearMap.one_apply]
  rw [this a]
  simp_rw [h]
  rw [← this b]

theorem map_sig_eq (t s : ℝ) :
    TensorProduct.map (hφ.elim.sig t).toLinearMap (sigop hφ.elim s) =
      LinearMap.mulLeft ℂ
          (hφ.elim.matrixIsPosDef.rpow (-t) ⊗ₜ
            (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrixIsPosDef.rpow s)) ∘ₗ
        LinearMap.mulRight ℂ
          (hφ.elim.matrixIsPosDef.rpow t ⊗ₜ
            (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrixIsPosDef.rpow (-s))) :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  let b' := (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) b
  have : b = (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) b' := rfl
  simp only [this, map_tmul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, Algebra.TensorProduct.tmul_mul_tmul, sigop, unop_op,
    Module.Dual.IsFaithfulPosMap.sig_apply, LinearMap.coe_mk, ← MulOpposite.op_mul, mul_eq_mul,
    Matrix.mul_assoc, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv, MulOpposite.coe_opLinearEquiv_symm, unop_apply, op_apply,
    MulOpposite.unop_op]

theorem map_sig_mulLeft_injective (t s : ℝ) :
    Function.Injective
      (LinearMap.mulLeft ℂ
        (hφ.elim.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
          (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrixIsPosDef.rpow s))) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        (LinearMap.mulLeft ℂ
            (hφ.elim.matrix_is_pos_def.rpow (-t) ⊗ₜ[ℂ]
              (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow (-s))))
          (LinearMap.mulLeft ℂ
            (hφ.elim.matrix_is_pos_def.rpow t ⊗ₜ[ℂ]
              (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow s))
            a) :=
    by
    intro a
    simp_rw [← LinearMap.comp_apply, ← LinearMap.mulLeft_mul, Algebra.TensorProduct.tmul_mul_tmul,
      op_apply, ← MulOpposite.op_mul, mul_eq_mul, pos_def.rpow_mul_rpow, neg_add_self, add_neg_self,
      pos_def.rpow_zero, MulOpposite.op_one, ← Algebra.TensorProduct.one_def, LinearMap.mulLeft_one,
      LinearMap.id_apply]
  rw [this a, h, ← this]

theorem map_sig_mulRight_injective (t s : ℝ) :
    Function.Injective
      (LinearMap.mulRight ℂ
        (hφ.elim.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
          (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrixIsPosDef.rpow s))) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        (LinearMap.mulRight ℂ
            (hφ.elim.matrix_is_pos_def.rpow (-t) ⊗ₜ[ℂ]
              (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow (-s))))
          (LinearMap.mulRight ℂ
            (hφ.elim.matrix_is_pos_def.rpow t ⊗ₜ[ℂ]
              (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow s))
            a) :=
    by
    intro a
    simp_rw [← LinearMap.comp_apply, ← LinearMap.mulRight_mul, Algebra.TensorProduct.tmul_mul_tmul,
      op_apply, ← MulOpposite.op_mul, mul_eq_mul, pos_def.rpow_mul_rpow, neg_add_self, add_neg_self,
      pos_def.rpow_zero, MulOpposite.op_one, ← Algebra.TensorProduct.one_def,
      LinearMap.mulRight_one, LinearMap.id_apply]
  rw [this a, h, ← this]

theorem LinearMap.Matrix.mulRight_adjoint (x : ℍ) :
    (LinearMap.mulRight ℂ x).adjoint = LinearMap.mulRight ℂ (hφ.elim.sig (-1) xᴴ) :=
  by
  symm
  rw [@LinearMap.eq_adjoint_iff ℂ _]
  intro a b
  simp_rw [LinearMap.mulRight_apply, Matrix.hMul_eq_hMul, Module.Dual.IsFaithfulPosMap.sig_apply,
    neg_neg, pos_def.rpow_one_eq_self, pos_def.rpow_neg_one_eq_inv_self, ←
    Module.Dual.IsFaithfulPosMap.inner_left_conj]

theorem LinearMap.Matrix.mulLeft_adjoint [hφ : Fact φ.IsFaithfulPosMap] (x : ℍ) :
    (LinearMap.mulLeft ℂ x).adjoint = LinearMap.mulLeft ℂ xᴴ :=
  by
  symm
  rw [@LinearMap.eq_adjoint_iff ℂ _]
  intro a b
  simp_rw [LinearMap.mulLeft_apply, Matrix.hMul_eq_hMul, ←
    Module.Dual.IsFaithfulPosMap.inner_right_hMul]

theorem Qam.ir_refl_iff_ir_refl'_of_real {A : ℍ →ₗ[ℂ] ℍ} (hA : A.IsReal) (p : Prop) [Decidable p] :
    Qam.reflIdempotent hφ.elim A 1 = ite p 1 0 ↔ Qam.reflIdempotent hφ.elim 1 A = ite p 1 0 :=
  by
  rw [LinearMap.isReal_iff] at hA
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one
  simp_rw [LinearMap.real_sum, rankOne_real_apply] at hA
  nth_rw_lhs 1 [← hA]
  simp_rw [map_sum, LinearMap.sum_apply, Qam.reflexive_eq_rankOne, Qam.reflexive'_eq_rankOne, ←
    conj_transpose_mul, ← @LinearMap.Matrix.mulLeft_adjoint n _ _ φ _, ← map_sum]
  have t3 : ∀ a : l(ℍ), a.adjoint = ite p 1 0 ↔ a = ite p 1 0 :=
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

theorem Qam.realOfSelfAdjointSymm [hφ : Fact φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ)
    (h1 : A.adjoint = A) (h2 : LinearEquiv.symmMap ℂ ℍ A = A) : A.IsReal :=
  by
  rw [LinearMap.isReal_iff]
  rw [LinearEquiv.symmMap_apply, ← LinearMap.star_eq_adjoint, star_eq_iff_star_eq,
    LinearMap.star_eq_adjoint, h1] at h2
  exact h2.symm

theorem Qam.self_adjoint_of_symm_real [hφ : Fact φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ)
    (h1 : LinearEquiv.symmMap ℂ ℍ A = A) (h2 : A.IsReal) : A.adjoint = A :=
  by
  rw [LinearMap.isReal_iff] at h2
  rw [LinearEquiv.symmMap_apply, h2] at h1
  exact h1

theorem Qam.symm_of_real_self_adjoint [hφ : Fact φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) (h1 : A.IsReal)
    (h2 : A.adjoint = A) : LinearEquiv.symmMap ℂ ℍ A = A :=
  by
  rw [LinearEquiv.symmMap_apply, (LinearMap.isReal_iff _).mp h1]
  exact h2

theorem Qam.self_adjoint_symm_real_tFAE [hφ : Fact φ.IsFaithfulPosMap] (A : ℍ →ₗ[ℂ] ℍ) :
    TFAE
      [A.adjoint = A ∧ LinearEquiv.symmMap ℂ ℍ A = A, A.adjoint = A ∧ A.IsReal,
        LinearEquiv.symmMap ℂ ℍ A = A ∧ A.IsReal] :=
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

theorem Psi.real (A : ℍ →ₗ[ℂ] ℍ) (t s : ℝ) :
    hφ.elim.psi t s A.Real =
      ((hφ.elim.sig (2 * t)).toLinearMap ⊗ₘ sigop hφ.elim (1 - 2 * s)) (star (hφ.elim.psi t s A)) :=
  by
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one
  simp_rw [LinearMap.real_sum, map_sum, star_sum]
  simp only [map_sum, rankOne_real_apply, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, tensor_op_star_apply, unop_op,
    conj_transpose_conj_transpose, map_tmul, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, sigop, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, star_eq_conj_transpose]
  simp only [neg_add_rev, neg_neg, two_mul, add_assoc, add_neg_cancel_right]
  simp_rw [sub_add, add_sub_cancel, sub_eq_add_neg]

theorem sigop_zero : sigop hφ.elim 0 = 1 := by
  rw [sigop, Module.Dual.IsFaithfulPosMap.sig_zero', AlgEquiv.one_toLinearMap, LinearMap.one_comp,
    op_comp_unop]

theorem Qam.isReal_and_idempotent_iff_psi_orthogonal_projection (A : ℍ →ₗ[ℂ] ℍ) :
    Qam.reflIdempotent hφ.elim A A = A ∧ A.IsReal ↔
      IsIdempotentElem (hφ.elim.psi 0 (1 / 2) A) ∧
        star (hφ.elim.psi 0 (1 / 2) A) = hφ.elim.psi 0 (1 / 2) A :=
  by
  nth_rw_lhs 1 [← Function.Injective.eq_iff (hφ.elim.Psi 0 (1 / 2)).Injective]
  rw [LinearMap.isReal_iff, ← Function.Injective.eq_iff (hφ.elim.Psi 0 (1 / 2)).Injective,
    Psi.reflIdempotent, Psi.real, MulZeroClass.mul_zero, Module.Dual.IsFaithfulPosMap.sig_zero',
    one_div, mul_inv_cancel (two_ne_zero' ℝ), sub_self, sigop_zero, AlgEquiv.one_toLinearMap,
    TensorProduct.map_one, LinearMap.one_apply, IsIdempotentElem]

theorem sig_map_sigop_comp_psi (t s r q : ℝ) :
    TensorProduct.map (hφ.elim.sig t).toLinearMap (sigop hφ.elim s) ∘ hφ.elim.psi r q =
      hφ.elim.psi (r + t) (q - s) :=
  by
  ext1
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  simp_rw [Function.comp_apply, map_sum, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk,
    Module.Dual.IsFaithfulPosMap.psiToFun'_apply, map_tmul, sigop, LinearMap.comp_apply, unop_op,
    AlgEquiv.toLinearMap_apply, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, neg_sub, sub_eq_add_neg, add_comm]

theorem sig_map_sigop_apply_psi (t s r q : ℝ) (A : ℍ →ₗ[ℂ] ℍ) :
    (TensorProduct.map (hφ.elim.sig t).toLinearMap (sigop hφ.elim s)) (hφ.elim.psi r q A) =
      hφ.elim.psi (r + t) (q - s) A :=
  by
  have := @sig_map_sigop_comp_psi n _ _ φ _ t s r q
  simp_rw [Function.funext_iff, Function.comp_apply] at this
  exact this _

-- :TODO:
-- lemma qam.is_qam_iff_Psi_orthogonal_projection_and_swap (A : ℍ →ₗ[ℂ] ℍ) :
--   (qam.refl_idempotent hφ.elim A A = A ∧ A.is_real ∧ qam.symm hφ.elim A = A)
--     ↔ (is_idempotent_elem (hφ.elim.Psi 0 (1/2) A)
--     ∧ star (hφ.elim.Psi 0 (1/2) A) = hφ.elim.Psi 0 (1/2) A
--       ∧ hφ.elim.Psi 0 (1/2) A = ten_swap (hφ.elim.Psi (1/2) 0 A)) :=
-- begin
--   rw [← and_assoc, qam.is_real_and_idempotent_iff_Psi_orthogonal_projection,
--     list.tfae.out (qam.self_adjoint_symm_real_tfae hφ A) 0 2,
--     and_rotate, and_comm A.is_real],
--   -- have : ∀ t, sigop hφ t = op ∘ₗ sig hφ.matrix_is_pos_def t ∘ₗ unop := λ _, rfl,
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
