/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Mul''
import Monlib.LinearAlgebra.Matrix.PosDefRpow
import Monlib.LinearAlgebra.InnerAut
import Monlib.LinearAlgebra.Matrix.Reshape
import Monlib.LinearAlgebra.ToMatrixOfEquiv
import Monlib.LinearAlgebra.Ips.TensorHilbert
import Monlib.LinearAlgebra.Ips.Functional
import Monlib.LinearAlgebra.Ips.MatIps
import Monlib.LinearAlgebra.Ips.MulOp
import Monlib.LinearAlgebra.Matrix.IncludeBlock
import Monlib.LinearAlgebra.Ips.OpUnop
import Monlib.LinearAlgebra.PiDirectSum
import Monlib.LinearAlgebra.TensorProduct.BasicLemmas

#align_import linear_algebra.my_ips.nontracial

/-!

# Some results on the Hilbert space on finite-dimensional C*-algebras

This file contains some results on the Hilbert space on finite-dimensional C*-algebras
  (so just a direct sum of matrix algebras over ℂ).

-/


variable {n : Type _} [Fintype n]

local notation "ℍ" => Matrix n n ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "L(" x ")" => x →L[ℂ] x

local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

open scoped Matrix

open Matrix

variable [DecidableEq n] {φ : Module.Dual ℂ (Matrix n n ℂ)}
  {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
  [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}

open scoped Kronecker Matrix BigOperators TensorProduct Functional

open Module.Dual

section SingleBlock

/-! # Section single_block -/

-- set_option trace.Meta.synthInstance true
-- set_option pp.all true
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.isLevelDefEq true

-- /- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x_5 x_6) -/
-- /- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
-- set_option synthInstance.maxHeartbeats 300000 in
-- set_option maxHeartbeats 900000 in
-- /-- we can expres the nontracial adjoint of `linear_map.mul'` by

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

-- set_option synthInstance.maxHeartbeats 60000 in
-- theorem Module.Dual.IsFaithfulPosMap.psi_0_0_eq [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
--     hφ.psi 0 0 x = (TensorProduct.map x op) (LinearMap.adjoint (LinearMap.mul' ℂ ℍ) (1 : ℍ)) :=
--   by
--   suffices
--     ∀ a b : ℍ,
--       hφ.psi 0 0 |a⟩⟨b| =
--         (TensorProduct.map (↑|a⟩⟨b|) op) (LinearMap.adjoint (LinearMap.mul' ℂ ℍ) (1 : ℍ))
--     by
--     obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
--     simp_rw [map_sum, this, TensorProduct.sum_map, LinearMap.sum_apply]
--   intro a b
--   simp_rw [LinearMap.mul'_adjoint, one_apply, ite_mul, one_mul, MulZeroClass.zero_mul, ite_smul,
--     zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, _root_.map_smul,
--     TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, rankOne_apply, ← inner_conj_symm b,
--     inner_stdBasisMatrix_left, starRingEnd_apply, ← conjTranspose_apply, conjTranspose_mul, ←
--     TensorProduct.smul_tmul', smul_smul]
--   rw [Finset.sum_rotate]
--   simp_rw [← Finset.sum_smul, ← mul_apply, hφ.matrixIsPosDef.1.eq,
--     @inv_mul_cancel_left_of_invertible n n ℂ _ _ _ φ.matrix bᴴ hφ.matrixIsPosDef.invertible,
--     ← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum, ← _root_.map_smul, ← map_sum, ←
--     smul_stdBasisMatrix']
--   rw [← matrix_eq_sum_std_basis bᴴ, Module.Dual.IsFaithfulPosMap.psi_apply,
--     Module.Dual.IsFaithfulPosMap.psiToFun'_apply]
--   simp_rw [Module.Dual.IsFaithfulPosMap.sig_zero]

-- theorem Module.Dual.IsFaithfulPosMap.psi_eq [hφ : φ.IsFaithfulPosMap]
--   (t s : ℝ) (x : l(ℍ)) :
--   hφ.psi t s x =
--     (TensorProduct.map (hφ.sig t).toLinearMap (op ∘ₗ (hφ.sig (-s)).toLinearMap ∘ₗ unop))
--       ((TensorProduct.map x op) (LinearMap.adjoint (LinearMap.mul' ℂ ℍ) (1 : ℍ))) :=
--   by
--   simp_rw [← Module.Dual.IsFaithfulPosMap.psi_0_0_eq, Module.Dual.IsFaithfulPosMap.psi_apply, ←
--     LinearMap.comp_apply]
--   revert x
--   rw [← LinearMap.ext_iff]
--   apply LinearMap.ext_of_rank_one'
--   intro a b
--   simp_rw [LinearMap.comp_apply, Module.Dual.IsFaithfulPosMap.psiToFun'_apply,
--     TensorProduct.map_tmul, Module.Dual.IsFaithfulPosMap.sig_zero, LinearMap.comp_apply, unop_op,
--     Module.Dual.IsFaithfulPosMap.sig_conjTranspose]
--   rfl

-- theorem Module.Dual.IsFaithfulPosMap.sig_adjoint [hφ : φ.IsFaithfulPosMap] {t : ℝ} :
--     LinearMap.adjoint (hφ.sig t).toLinearMap = (hφ.sig t).toLinearMap :=
--   by
--   rw [LinearMap.ext_iff_inner_map]
--   intro x
--   simp_rw [LinearMap.adjoint_inner_left, Module.Dual.IsFaithfulPosMap.inner_eq',
--     AlgEquiv.toLinearMap_apply, Module.Dual.IsFaithfulPosMap.sig_conjTranspose,
--     Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg]
--   let hQ := hφ.matrixIsPosDef
--   let Q := φ.matrix
--   calc
--     (Q * xᴴ * (hQ.rpow (-t) * x * hQ.rpow t)).trace =
--         (hQ.rpow t * Q * xᴴ * hQ.rpow (-t) * x).trace :=
--       ?_
--     _ = (hQ.rpow t * hQ.rpow 1 * xᴴ * hQ.rpow (-t) * x).trace := by rw [PosDef.rpow_one_eq_self]
--     _ = (hQ.rpow 1 * hQ.rpow t * xᴴ * hQ.rpow (-t) * x).trace := ?_
--     _ = (Q * (hQ.rpow t * xᴴ * hQ.rpow (-t)) * x).trace := by
--       simp_rw [PosDef.rpow_one_eq_self, Matrix.mul_assoc]
--   · rw [← Matrix.mul_assoc, trace_mul_cycle]
--     simp_rw [Matrix.mul_assoc]
--   · simp_rw [PosDef.rpow_mul_rpow, add_comm]

-- theorem Nontracial.inner_symm' [hφ : φ.IsFaithfulPosMap] (x y : ℍ) :
--     ⟪x, y⟫_ℂ = ⟪hφ.sig (-(1 / 2 : ℝ)) yᴴ, hφ.sig (-(1 / 2 : ℝ)) xᴴ⟫_ℂ :=
--   by
--   simp_rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_left,
--     Module.Dual.IsFaithfulPosMap.sig_adjoint, AlgEquiv.toLinearMap_apply,
--     Module.Dual.IsFaithfulPosMap.sig_apply_sig]
--   rw [Nontracial.inner_symm]
--   norm_num

theorem Module.Dual.IsFaithfulPosMap.basis_apply' [hφ : Module.Dual.IsFaithfulPosMap φ]
    (i j : n) :
    hφ.basis (i, j) = stdBasisMatrix i j 1 * hφ.matrixIsPosDef.rpow (-(1 / 2)) :=
  Module.Dual.IsFaithfulPosMap.basis_apply _ (i, j)

theorem sig_apply_pos_def_matrix [hφ : Module.Dual.IsFaithfulPosMap φ] (t s : ℝ) :
    hφ.sig t (hφ.matrixIsPosDef.rpow s) = hφ.matrixIsPosDef.rpow s := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, PosDef.rpow_mul_rpow, neg_add_cancel_comm]

theorem sig_apply_pos_def_matrix' [hφ : Module.Dual.IsFaithfulPosMap φ] (t : ℝ) : hφ.sig t φ.matrix = φ.matrix :=
  by
  nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  rw [← sig_apply_pos_def_matrix t (1 : ℝ), PosDef.rpow_one_eq_self]

end SingleBlock

section DirectSum

open Module.Dual

/-! # Section direct_sum -/

open scoped ComplexOrder

-- instance
--   Pi.tensorProduct_finiteDimensional :
--       FiniteDimensional ℂ (PiMat ℂ k s ⊗[ℂ] PiMat ℂ k s) :=
--   by infer_instance
  -- FiniteDimensional.of_finite_basis (Basis.ofVectorSpace ℂ _)
    -- (Basis.ofVectorSpaceIndex ℂ _).toFinite

open scoped Functional

theorem Module.Dual.pi.IsFaithfulPosMap.inner_coord' [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    (ij : s i × s i) (x : PiMat ℂ k s) :
    ⟪Module.Dual.pi.IsFaithfulPosMap.basis (fun i => (hψ i)) ⟨i, ij⟩, x⟫_ℂ =
      (x * fun j => (hψ j).matrixIsPosDef.rpow (1 / 2)) i ij.1 ij.2 :=
  by
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.basis_apply, ←
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, Pi.mul_apply,
    Module.Dual.pi.IsFaithfulPosMap.includeBlock_left_inner,
    Module.Dual.IsFaithfulPosMap.inner_coord]

theorem Module.Dual.pi.IsFaithfulPosMap.map_star (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (x : PiMat ℂ k s) :
    pi ψ (star x) = star (pi ψ x) :=
  pi.IsPosMap.isReal (fun i => (hψ i).1) x

theorem Nontracial.Pi.unit_adjoint_eq [hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
    LinearMap.adjoint (Algebra.linearMap ℂ (PiMat ℂ k s) : ℂ →ₗ[ℂ] PiMat ℂ k s) = pi ψ := by
  rw [← pi.IsFaithfulPosMap.adjoint_eq, LinearMap.adjoint_adjoint]

def Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef {k : Type _} {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    (hψ : ∀ i, (ψ i).IsFaithfulPosMap) := fun i => (hψ i).matrixIsPosDef

noncomputable def Pi.PosDef.rpow {k : Type _} {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] {a : PiMat ℂ k s} (ha : ∀ i, (a i).PosDef) (r : ℝ) :=
  fun i => (ha i).rpow r

theorem Pi.PosDef.rpow_hMul_rpow {a : PiMat ℂ k s} (ha : ∀ i, (a i).PosDef) (r₁ r₂ : ℝ) :
    Pi.PosDef.rpow ha r₁ * Pi.PosDef.rpow ha r₂ = Pi.PosDef.rpow ha (r₁ + r₂) :=
  by
  ext1 i
  simp only [Pi.mul_apply, Pi.PosDef.rpow, PosDef.rpow_mul_rpow]

theorem Pi.PosDef.rpow_zero {a : PiMat ℂ k s} (ha : ∀ i, (a i).PosDef) : Pi.PosDef.rpow ha 0 = 1 :=
  by
  ext x i j
  simp only [Pi.PosDef.rpow, Matrix.PosDef.rpow_zero, Pi.one_apply]

theorem basis_repr_apply' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x : PiMat ℂ k s) (ijk : Σ i, s i × s i) :
    let hQ := Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ
    (Module.Dual.pi.IsFaithfulPosMap.basis hψ).repr x ijk
      = (x * (Pi.PosDef.rpow hQ (1/2))) ijk.1 ijk.2.1 ijk.2.2 :=
by
  rw [Module.Dual.pi.IsFaithfulPosMap.basis_repr_apply]
  simp_rw [Pi.mul_apply, Pi.PosDef.rpow, Module.Dual.IsFaithfulPosMap.basis_apply,
    ← Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply]
  rw [Module.Dual.IsFaithfulPosMap.inner_coord]

theorem Module.Dual.pi.IsFaithfulPosMap.includeBlock_right_inner {k : Type _} [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
    {ψ : ∀ i : k, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i : k, (ψ i).IsFaithfulPosMap]
    {i : k} (y : ∀ j : k, Matrix (s j) (s j) ℂ) (x : Matrix (s i) (s i) ℂ) :
    ⟪y, includeBlock x⟫_ℂ = ⟪y i, x⟫_ℂ := by
  rw [← inner_conj_symm, pi.IsFaithfulPosMap.includeBlock_left_inner, inner_conj_symm]

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

variable {k₂ : Type _} [Fintype k₂] [DecidableEq k₂] {s₂ : k₂ → Type _} [∀ i, Fintype (s₂ i)]
  [∀ i, DecidableEq (s₂ i)] {ψ₂ : ∀ i, Module.Dual ℂ (Matrix (s₂ i) (s₂ i) ℂ)}

theorem pi_includeBlock_right_rankOne [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (a : PiMat ℂ k₂ s₂) {i : k}
    (b : ℍ_ i) (c : PiMat ℂ k s) (j : k₂) : |a⟩⟨includeBlock b| c j = ⟪b, c i⟫_ℂ • a j := by
  simp only [rankOne_apply, pi.IsFaithfulPosMap.includeBlock_left_inner, Pi.smul_apply]

theorem pi_includeBlock_left_rankOne [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap] (b : PiMat ℂ k s) {i : k₂}
    (a : Matrix (s₂ i) (s₂ i) ℂ) (c : PiMat ℂ k s) (j : k₂) :
    |includeBlock a⟩⟨b| c j =
      ⟪b, c⟫_ℂ • dite (i = j) (fun h => by rw [← h]; exact a) fun h => 0 :=
  by
  simp only [rankOne_apply, pi.IsFaithfulPosMap.includeBlock_left_inner, Pi.smul_apply,
    includeBlock_apply, smul_dite, smul_zero]
  rfl

noncomputable def Module.Dual.pi.IsFaithfulPosMap.sig (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) : PiMat ℂ k s ≃ₐ[ℂ] PiMat ℂ k s :=
  let hQ := Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ
  { toFun := fun x => Pi.PosDef.rpow hQ (-z) * x * Pi.PosDef.rpow hQ z
    invFun := fun x => Pi.PosDef.rpow hQ z * x * Pi.PosDef.rpow hQ (-z)
    left_inv := fun x => by
      simp only [← mul_assoc, Pi.PosDef.rpow_hMul_rpow]
      simp only [mul_assoc, Pi.PosDef.rpow_hMul_rpow]
      simp only [add_neg_self, Pi.PosDef.rpow_zero, one_mul, mul_one, neg_add_self]
    right_inv := fun x => by
      simp only [← mul_assoc, Pi.PosDef.rpow_hMul_rpow]
      simp only [mul_assoc, Pi.PosDef.rpow_hMul_rpow]
      simp only [add_neg_self, Pi.PosDef.rpow_zero, one_mul, mul_one, neg_add_self]
    map_add' := fun x y => by simp only [mul_add, add_mul]
    map_mul' := fun x y => by
      simp_rw [mul_assoc]
      simp only [← mul_assoc (Pi.PosDef.rpow hQ z) (Pi.PosDef.rpow hQ (-z)),
        Pi.PosDef.rpow_hMul_rpow, add_neg_self, Pi.PosDef.rpow_zero, one_mul]
    -- map_smul' := fun r x => by
    --   simp only [MulAction.mul_smul, smul_mul, RingHom.id_apply]
    --   simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
        Pi.PosDef.rpow_hMul_rpow, neg_add_self, Pi.PosDef.rpow_zero]
        }

@[simp]
theorem Module.Dual.pi.IsFaithfulPosMap.sig_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (z : ℝ)
    (x : PiMat ℂ k s) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ z) x =
      Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) (-z) * x *
        Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) z :=
  rfl

@[simp]
theorem Module.Dual.pi.IsFaithfulPosMap.sig_symm_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (z : ℝ) (x : PiMat ℂ k s) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ z).symm x =
      Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) z * x *
        Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) (-z) :=
  rfl

@[simp]
theorem Module.Dual.pi.IsFaithfulPosMap.sig_symm_eq (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ z).symm = Module.Dual.pi.IsFaithfulPosMap.sig hψ (-z) :=
  by
  ext1
  simp only [Module.Dual.pi.IsFaithfulPosMap.sig_apply,
    Module.Dual.pi.IsFaithfulPosMap.sig_symm_apply, neg_neg]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_apply_single_block
    (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (z : ℝ) {i : k} (x : ℍ_ i) :
    Module.Dual.pi.IsFaithfulPosMap.sig hψ z (includeBlock x) =
      includeBlock ((hψ i).sig z x) :=
  by
  simp only [Module.Dual.pi.IsFaithfulPosMap.sig_apply, Module.Dual.IsFaithfulPosMap.sig_apply,
    Pi.mul_apply]
  simp_rw [hMul_includeBlock, includeBlock_hMul, includeBlock_inj, Pi.PosDef.rpow]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (z : ℝ) (x : PiMat ℂ k s) {i : k} :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ z x) i = (hψ i).sig z (x i) :=
  rfl

theorem Pi.PosDef.rpow.isPosDef {a : PiMat ℂ k s} (ha : ∀ i, (a i).PosDef) (r : ℝ) :
    ∀ i, ((Pi.PosDef.rpow ha r) i).PosDef := by
  intro i
  simp only [Pi.PosDef.rpow]
  exact Matrix.PosDef.rpow.isPosDef _ _

theorem Pi.PosDef.rpow.is_self_adjoint {a : PiMat ℂ k s} (ha : ∀ i, (a i).PosDef) (r : ℝ) :
    star (Pi.PosDef.rpow ha r) = Pi.PosDef.rpow ha r :=
  by
  ext1 i
  simp only [Pi.PosDef.rpow, star_apply, Pi.star_apply]
  exact Matrix.PosDef.rpow.isHermitian _ _

theorem Module.Dual.pi.IsFaithfulPosMap.sig_star (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (z : ℝ)
    (x : PiMat ℂ k s) :
    star (Module.Dual.pi.IsFaithfulPosMap.sig hψ z x) =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ (-z) (star x) :=
  by
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.sig_apply, StarMul.star_mul,
    Pi.PosDef.rpow.is_self_adjoint, mul_assoc, neg_neg]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (t r : ℝ) (x : PiMat ℂ k s) :
    Module.Dual.pi.IsFaithfulPosMap.sig hψ t (Module.Dual.pi.IsFaithfulPosMap.sig hψ r x) =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ (t + r) x :=
  by
  simp only [Module.Dual.pi.IsFaithfulPosMap.sig_apply, Pi.PosDef.rpow_hMul_rpow]
  simp_rw [← mul_assoc, Pi.PosDef.rpow_hMul_rpow, mul_assoc, Pi.PosDef.rpow_hMul_rpow, neg_add,
    add_comm]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_zero (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (x : PiMat ℂ k s) :
    Module.Dual.pi.IsFaithfulPosMap.sig hψ 0 x = x := by
  simp only [Module.Dual.pi.IsFaithfulPosMap.sig_apply, Pi.PosDef.rpow_zero, one_mul, mul_one,
    neg_zero]

theorem Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv_apply'' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (f : (PiMat ℂ k s) →ₗ[ℂ] PiMat ℂ k₂ s₂) (r : Σ r, s₂ r × s₂ r) (l : Σ r, s r × s r) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv hψ hψ₂) f r l =
      (f (includeBlock ((hψ l.1).basis l.2)) *
          Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ₂) (1 / 2 : ℝ))
        r.1 r.2.1 r.2.2 :=
  by
  rw [Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv_apply']
  rfl
theorem Module.Dual.pi.IsFaithfulPosMap.toMatrix_apply'' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (f : (PiMat ℂ k s) →ₗ[ℂ] PiMat ℂ k s) (r l : Σ r, s r × s r) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix hψ) f r l =
      (f (includeBlock ((hψ l.1).basis l.2)) *
          Pi.PosDef.rpow (Module.Dual.pi.IsFaithfulPosMap.matrixIsPosDef hψ) (1 / 2 : ℝ))
        r.1 r.2.1 r.2.2 :=
toMatrixLinEquiv_apply'' _ _ _

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 600000 in
theorem Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv_symm_apply' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (x : Matrix (Σ i, s₂ i × s₂ i) (Σ i, s i × s i) ℂ) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv hψ hψ₂).symm x =
      ∑ a, ∑ i, ∑ j, ∑ b, ∑ c, ∑ d,
        x ⟨a, (i, j)⟩ ⟨b, (c, d)⟩ •
          |Module.Dual.pi.IsFaithfulPosMap.basis hψ₂
              ⟨a,
                (i,
                  j)⟩⟩⟨Module.Dual.pi.IsFaithfulPosMap.basis hψ ⟨b, (c, d)⟩| :=
  by
  rw [LinearMap.ext_iff]
  intro y
  rw [Function.funext_iff]
  intro a
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv, LinearMap.toMatrix_symm,
    toLin_apply, mulVec, dotProduct, pi.IsFaithfulPosMap.basis_repr_apply,
    pi.IsFaithfulPosMap.basis_apply, ← Module.Dual.IsFaithfulPosMap.basis_apply',
    Finset.sum_sigma_univ, ContinuousLinearMap.coe_sum,
    ContinuousLinearMap.coe_smul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply,
    pi.IsFaithfulPosMap.includeBlock_left_inner, Finset.sum_product_univ, Finset.sum_smul,
    smul_smul]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a i j b c d) -/
set_option synthInstance.maxHeartbeats 400000 in
theorem Module.Dual.pi.IsFaithfulPosMap.toMatrix_symm_apply' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x : Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix hψ).symm x =
      ∑ a, ∑ i, ∑ j, ∑ b, ∑ c, ∑ d,
        x ⟨a, (i, j)⟩ ⟨b, (c, d)⟩ •
          |Module.Dual.pi.IsFaithfulPosMap.basis hψ
              ⟨a,
                (i,
                  j)⟩⟩⟨Module.Dual.pi.IsFaithfulPosMap.basis hψ ⟨b, (c, d)⟩| :=
toMatrixLinEquiv_symm_apply' _

theorem Module.Dual.pi.IsFaithfulPosMap.toMatrix_eq_orthonormalBasis_toMatrix
    [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : l(PiMat ℂ k s)) :
    (pi.IsFaithfulPosMap.toMatrix fun i => (hψ i)) x =
      (pi.IsFaithfulPosMap.orthonormalBasis hψ).toMatrix x :=
  by
  ext
  simp_rw [pi.IsFaithfulPosMap.toMatrix_apply', OrthonormalBasis.toMatrix_apply,
    pi.IsFaithfulPosMap.orthonormalBasis_apply, pi.IsFaithfulPosMap.includeBlock_left_inner,
    ← Module.Dual.IsFaithfulPosMap.basis_apply, (hψ _).inner_coord']

lemma _root_.Matrix.toLin_apply_rankOne {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
  [_root_.NormedAddCommGroup H₁] [_root_.NormedAddCommGroup H₂] [_root_.InnerProductSpace 𝕜 H₁]
  [_root_.InnerProductSpace 𝕜 H₂] {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
  [DecidableEq ι₂]
  (b₁ : OrthonormalBasis ι₁ 𝕜 H₁) (b₂ : OrthonormalBasis ι₂ 𝕜 H₂) (x : Matrix ι₂ ι₁ 𝕜) :
  Matrix.toLin b₁.toBasis b₂.toBasis x = ∑ i, ∑ j, x i j • (rankOne 𝕜 (b₂ i) (b₁ j)) :=
by
  ext1
  simp_rw [toLin_apply, mulVec, dotProduct, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, ContinuousLinearMap.coe_sum,
    ContinuousLinearMap.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, smul_smul, Finset.sum_smul]
  rfl

@[simp]
lemma Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis_eq_toBasis
  (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
  (IsFaithfulPosMap.orthonormalBasis hψ).toBasis = IsFaithfulPosMap.basis hψ :=
by
  ext
  simp_rw [OrthonormalBasis.coe_toBasis, pi.IsFaithfulPosMap.orthonormalBasis_apply,
    pi.IsFaithfulPosMap.basis_apply]

set_option synthInstance.maxHeartbeats 400000 in
theorem Module.Dual.pi.IsFaithfulPosMap.linearMap_eq [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (x : (PiMat ℂ k s) →ₗ[ℂ] PiMat ℂ k₂ s₂) :
    x =
      ∑ a, ∑ b,
        (Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv hψ hψ₂) x a b •
          |(Module.Dual.pi.IsFaithfulPosMap.basis hψ₂)
              a⟩⟨(Module.Dual.pi.IsFaithfulPosMap.basis hψ) b| :=
  by
  simp_rw [pi.IsFaithfulPosMap.basis_apply, ← pi.IsFaithfulPosMap.orthonormalBasis_apply]
  rw [← _root_.Matrix.toLin_apply_rankOne, ← LinearMap.toMatrix_symm]
  simp only [orthonormalBasis_eq_toBasis, toMatrixLinEquiv,
    LinearMap.toMatrix_symm, toLin_toMatrix]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
set_option synthInstance.maxHeartbeats 0 in
noncomputable def Module.Dual.pi.IsFaithfulPosMap.psiToFun' (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
  (hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap)
    (t r : ℝ) : (PiMat ℂ k s →ₗ[ℂ] PiMat ℂ k₂ s₂) →ₗ[ℂ] PiMat ℂ k₂ s₂ ⊗[ℂ] (PiMat ℂ k s)ᵐᵒᵖ
    where
  toFun x :=
    ∑ a, ∑ b,
      (Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv hψ hψ₂ x) a b •
        Module.Dual.pi.IsFaithfulPosMap.sig hψ₂ t
            ((Module.Dual.pi.IsFaithfulPosMap.basis hψ₂) a) ⊗ₜ[ℂ]
          (op : PiMat ℂ k s →ₗ[ℂ] (PiMat ℂ k s)ᵐᵒᵖ)
            (star
              (Module.Dual.pi.IsFaithfulPosMap.sig hψ r
                ((Module.Dual.pi.IsFaithfulPosMap.basis hψ) b)))
  map_add' x y := by simp_rw [map_add, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [_root_.map_smul, Matrix.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

theorem Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv_rankOne_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (x : PiMat ℂ k₂ s₂) (y : PiMat ℂ k s) :
    pi.IsFaithfulPosMap.toMatrixLinEquiv hψ hψ₂ |x⟩⟨y| =
    fun (i : Σ i, s₂ i × s₂ i) (j : Σ i, s i × s i) =>
      (col (reshape (x i.fst * (hψ₂ i.1).matrixIsPosDef.rpow (1 / 2))) *
          (col (reshape (y j.fst * (hψ j.1).matrixIsPosDef.rpow (1 / 2))))ᴴ)
        i.2 j.2 :=
by
  ext
  simp_rw [pi.IsFaithfulPosMap.toMatrixLinEquiv_apply', ContinuousLinearMap.coe_coe, _root_.rankOne_apply,
    Pi.smul_apply, Matrix.smul_mul, Matrix.smul_apply,
    Module.Dual.pi.IsFaithfulPosMap.includeBlock_right_inner, ← inner_conj_symm (y _),
    Module.Dual.IsFaithfulPosMap.inner_coord', smul_eq_mul, mul_comm, ← reshape_apply (x _ * _), ←
    reshape_apply (y _ * _), starRingEnd_apply, conjTranspose_col, ← vecMulVec_eq,
    vecMulVec_apply, Pi.star_apply]

theorem Pi.IsFaithfulPosMap.ToMatrix.rankOne_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x y : PiMat ℂ k s) :
    pi.IsFaithfulPosMap.toMatrix hψ |x⟩⟨y| = fun i j : Σ i, s i × s i =>
      (col (reshape (x i.fst * (hψ i.1).matrixIsPosDef.rpow (1 / 2))) *
          (col (reshape (y j.fst * (hψ j.1).matrixIsPosDef.rpow (1 / 2))))ᴴ)
        i.2 j.2 :=
Module.Dual.pi.IsFaithfulPosMap.toMatrixLinEquiv_rankOne_apply _ _

theorem Module.Dual.pi.IsFaithfulPosMap.basis_repr_apply_apply
    [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (a : PiMat ℂ k s) (x : Σ i, s i × s i) :
    (Module.Dual.pi.IsFaithfulPosMap.basis hψ).repr a x =
      ((hψ x.1).basis.repr (a x.fst)) x.snd :=
  rfl

theorem Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (t r : ℝ) (b : PiMat ℂ k s) (a : PiMat ℂ k₂ s₂) :
    Module.Dual.pi.IsFaithfulPosMap.psiToFun' hψ hψ₂ t r |a⟩⟨b| =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ₂ t a ⊗ₜ[ℂ]
        (op : PiMat ℂ k s →ₗ[ℂ] (PiMat ℂ k s)ᵐᵒᵖ) (star (Module.Dual.pi.IsFaithfulPosMap.sig hψ r b)) :=
  by
  letI : ∀ i, StarModule ℂ (Matrix ((fun i : k => s i) i) ((fun i : k => s i) i) ℂ) :=
    by
    intro i
    infer_instance
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.psiToFun', LinearMap.coe_mk,
    AddHom.coe_mk,
    toMatrixLinEquiv_rankOne_apply, conjTranspose_col, ← vecMulVec_eq,
    vecMulVec_apply, ← TensorProduct.smul_tmul_smul, ← _root_.map_smul, Pi.star_apply, ←
    star_smul, ← _root_.map_smul, ← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ←
    map_sum, reshape_apply, ← star_sum, ← map_sum, ← Module.Dual.IsFaithfulPosMap.inner_coord', ←
    IsFaithfulPosMap.basis_repr_apply,
    -- ← Module.Dual.pi.IsFaithfulPosMap.basis_repr_apply_apply,
    Basis.sum_repr]

-- @[instance]
-- private def pi_matrix_tensor_is_semiring :
--     Semiring (∀ i : k × k, Matrix (s i.1) (s i.1) ℂ ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ) :=
--   by
--   apply @Pi.semiring _ _ _
--   intro i
--   infer_instance

-- @[instance]
-- private def pi_matrix_tensor_is_algebra :
--     Algebra ℂ (∀ i : k × k, Matrix (s i.1) (s i.1) ℂ ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ) :=
--   by
--   apply @Pi.algebra _ _ _ _ _ _
--   intro i
--   infer_instance

@[simps]
def Pi.transposeAlgEquiv (p : Type _) (n : p → Type _)
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] :
    (PiMat ℂ p n) ≃ₐ[ℂ] (PiMat ℂ p n)ᵐᵒᵖ
    where
  toFun A := MulOpposite.op fun i => (A i)ᵀ
  invFun A i := (MulOpposite.unop A i)ᵀ
  left_inv A := by simp only [MulOpposite.unop_op, transpose_transpose]
  right_inv A := by simp only [MulOpposite.op_unop, transpose_transpose]
  map_add' A B := by
    simp only [Pi.add_apply, transpose_add]
    rfl
  map_mul' A B :=
    by
    simp only [Pi.mul_apply, transpose_mul, ← MulOpposite.op_mul]
    rfl
  commutes' c :=
    by
    simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply, transpose_smul,
      transpose_one]
    rfl

theorem Pi.transposeAlgEquiv_symm_op_apply (A : PiMat ℂ k s) :
    (Pi.transposeAlgEquiv k s).symm (MulOpposite.op A) = fun i => (A i)ᵀ :=
  rfl

private noncomputable def f₂_equiv :
    (PiMat ℂ k s) ⊗[ℂ] (PiMat ℂ k s) ≃ₐ[ℂ] (Π i : k × k, Matrix (s i.1) (s i.1) ℂ ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ) :=
  by
  let this :=
    @directSumTensorAlgEquiv ℂ _ _ _ _ _ _ _ (fun i => Matrix (s i) (s i) ℂ)
      (fun i => Matrix (s i) (s i) ℂ) (fun i => Matrix.instRing) (fun i => Matrix.instRing)
      (fun i => Matrix.instAlgebra) fun i => Matrix.instAlgebra
  exact this

private noncomputable def f₃_equiv :
    (Π i : k × k, Matrix (s i.1) (s i.1) ℂ ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ) ≃ₐ[ℂ]
      (Π i : k × k, Matrix (s i.1 × s i.2) (s i.1 × s i.2) ℂ) :=
  by
  apply AlgEquiv.piCongrRight
  intro i
  exact kroneckerToTensor.symm

private def f₄_equiv :
    (Π i : k × k, Matrix (s i.1 × s i.2) (s i.1 × s i.2) ℂ) ≃ₐ[ℂ]
      { x : Matrix (Σ i : k × k, s i.1 × s i.2) (Σ i : k × k, s i.1 × s i.2) ℂ //
        x.IsBlockDiagonal } :=
  isBlockDiagonalPiAlgEquiv.symm

noncomputable def tensorProductMulOpEquiv :
    ((PiMat ℂ k s) ⊗[ℂ] (PiMat ℂ k s)ᵐᵒᵖ) ≃ₐ[ℂ] (Π i : k × k, Matrix (s i.1 × s i.2) (s i.1 × s i.2) ℂ) :=
  (AlgEquiv.TensorProduct.map (1 : PiMat ℂ k s ≃ₐ[ℂ] PiMat ℂ k s)
        (Pi.transposeAlgEquiv k s : PiMat ℂ k s ≃ₐ[ℂ] (PiMat ℂ k s)ᵐᵒᵖ).symm).trans
    (f₂_equiv.trans f₃_equiv)

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
noncomputable def Module.Dual.pi.IsFaithfulPosMap.psiInvFun'
  (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap)
    (t r : ℝ) : PiMat ℂ k s ⊗[ℂ] (PiMat ℂ k₂ s₂)ᵐᵒᵖ →ₗ[ℂ] (PiMat ℂ k₂ s₂ →ₗ[ℂ] PiMat ℂ k s)
    where
  toFun x :=
    ∑ a : Σ i, s i × s i, ∑ b : Σ i, s₂ i × s₂ i,
      (Basis.tensorProduct (pi.IsFaithfulPosMap.basis hψ)
              (pi.IsFaithfulPosMap.basis hψ₂).mulOpposite).repr
          x (a, b) •
        (↑|Module.Dual.pi.IsFaithfulPosMap.sig hψ (-t)
              (pi.IsFaithfulPosMap.basis hψ
                a)⟩⟨Module.Dual.pi.IsFaithfulPosMap.sig hψ₂ (-r)
              (star (pi.IsFaithfulPosMap.basis hψ₂ b))|)
  map_add' x y := by simp_rw [_root_.map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp_rw [_root_.map_smul, Finsupp.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum,
      RingHom.id_apply]

theorem Module.Dual.pi.IsFaithfulPosMap.psiInvFun'_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (t r : ℝ) (x : PiMat ℂ k s) (y : (PiMat ℂ k₂ s₂)ᵐᵒᵖ) :
    Module.Dual.pi.IsFaithfulPosMap.psiInvFun' hψ hψ₂ t r (x ⊗ₜ[ℂ] y) =
      |Module.Dual.pi.IsFaithfulPosMap.sig hψ (-t)
          x⟩⟨Module.Dual.pi.IsFaithfulPosMap.sig hψ₂ (-r) (star (MulOpposite.unop y))| :=
  by
  -- letI : ∀ i, StarModule ℂ (Matrix ((fun i : k => s i) i) ((fun i : k => s i) i) ℂ) :=
  --   by
  --   intro i
  --   infer_instance
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.psiInvFun', LinearMap.coe_mk,
    AddHom.coe_mk,
    Basis.tensorProduct_repr_tmul_apply, ← rankOne_lm_smul_smul, ← rankOne_lm_sum_sum, ←
    _root_.map_smul, ← star_smul, Basis.mulOpposite_repr_apply, ← map_sum, ← star_sum,
    Basis.sum_repr]

theorem Module.Dual.pi.IsFaithfulPosMap.Psi_left_inv [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (t r : ℝ) (x : PiMat ℂ k s) (y : PiMat ℂ k₂ s₂) :
    Module.Dual.pi.IsFaithfulPosMap.psiInvFun' hψ hψ₂ t r
        (Module.Dual.pi.IsFaithfulPosMap.psiToFun' hψ₂ hψ t r |x⟩⟨y|) =
      |x⟩⟨y| :=
  by
  rw [Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply,
    Module.Dual.pi.IsFaithfulPosMap.psiInvFun'_apply, op_apply, MulOpposite.unop_op, star_star]
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig, neg_add_self,
    Module.Dual.pi.IsFaithfulPosMap.sig_zero]

theorem Module.Dual.pi.IsFaithfulPosMap.Psi_right_inv [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap]
    (t r : ℝ) (x : PiMat ℂ k s) (y : (PiMat ℂ k₂ s₂)ᵐᵒᵖ) :
    Module.Dual.pi.IsFaithfulPosMap.psiToFun' hψ₂ hψ t r
        (Module.Dual.pi.IsFaithfulPosMap.psiInvFun' hψ hψ₂ t r (x ⊗ₜ[ℂ] y)) =
      x ⊗ₜ[ℂ] y :=
  by
  rw [Module.Dual.pi.IsFaithfulPosMap.psiInvFun'_apply,
    Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply]
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig, add_neg_self,
    Module.Dual.pi.IsFaithfulPosMap.sig_zero, star_star, op_apply, MulOpposite.op_unop]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
@[simps]
noncomputable def Module.Dual.pi.IsFaithfulPosMap.psi (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
  (hψ₂ : ∀ i, (ψ₂ i).IsFaithfulPosMap)
    (t r : ℝ) : (PiMat ℂ k s →ₗ[ℂ] PiMat ℂ k₂ s₂) ≃ₗ[ℂ] ((PiMat ℂ k₂ s₂) ⊗[ℂ] (PiMat ℂ k s)ᵐᵒᵖ) :=
  letI := hψ
  { toFun := fun x => Module.Dual.pi.IsFaithfulPosMap.psiToFun' hψ hψ₂ t r x
    invFun := fun x => Module.Dual.pi.IsFaithfulPosMap.psiInvFun' hψ₂ hψ t r x
    left_inv := fun x => by
      obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
      simp only [map_sum, Module.Dual.pi.IsFaithfulPosMap.Psi_left_inv]
    right_inv := fun x => by
      obtain ⟨α, β, rfl⟩ := x.eq_span
      simp only [Module.Dual.pi.IsFaithfulPosMap.Psi_right_inv, map_sum]
    map_add' := fun x y => by simp_rw [map_add]
    map_smul' := fun r x => by
      simp_rw [_root_.map_smul]
      rfl }

theorem Pi.inner_symm [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x y : PiMat ℂ k s) :
    ⟪x, y⟫_ℂ = ⟪Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star y), star x⟫_ℂ :=
  by
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq', ← Module.Dual.IsFaithfulPosMap.inner_eq',
    Nontracial.inner_symm (x _)]
  rfl

theorem Module.Dual.pi.IsFaithfulPosMap.sig_adjoint [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    {t : ℝ} :
    LinearMap.adjoint (Module.Dual.pi.IsFaithfulPosMap.sig hψ t : PiMat ℂ k s ≃ₐ[ℂ] PiMat ℂ k s).toLinearMap =
      (Module.Dual.pi.IsFaithfulPosMap.sig hψ t).toLinearMap :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro x
  simp_rw [LinearMap.adjoint_inner_left, AlgEquiv.toLinearMap_apply,
    Module.Dual.pi.IsFaithfulPosMap.inner_eq', ← Module.Dual.IsFaithfulPosMap.inner_eq',
    Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks, ← AlgEquiv.toLinearMap_apply, ←
    LinearMap.adjoint_inner_left, Module.Dual.IsFaithfulPosMap.sig_adjoint]

theorem Module.Dual.IsFaithfulPosMap.norm_eq {ψ : Module.Dual ℂ (Matrix n n ℂ)}
    [hψ : ψ.IsFaithfulPosMap] (x : Matrix n n ℂ) : ‖x‖ = Real.sqrt (RCLike.re (ψ (xᴴ * x))) :=
  by simp_rw [InnerProductSpace.Core.norm_eq_sqrt_inner, ← Module.Dual.IsFaithfulPosMap.inner_eq]

theorem Module.Dual.pi.IsFaithfulPosMap.norm_eq {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : Π i, (ψ i).IsFaithfulPosMap] (x : Π i, Matrix (s i) (s i) ℂ) :
    ‖x‖ = Real.sqrt (RCLike.re (pi ψ (star x * x))) := by
  simp_rw [← Module.Dual.pi.IsFaithfulPosMap.inner_eq]
  exact norm_eq_sqrt_inner _

-- instance Matrix.is_fd : FiniteDimensional ℂ (Matrix n n ℂ) := by infer_instance

-- instance Matrix.is_starModule {n : Type _} [Fintype n] [DecidableEq n] :
    -- StarModule ℂ (Matrix n n ℂ) := by infer_instance

-- instance Pi.matrix.is_fd : FiniteDimensional ℂ PiMat ℂ k s := by infer_instance

-- instance Pi.matrix.is_starModule : StarModule ℂ PiMat ℂ k s := by infer_instance

-- instance Pi.matrix.is_topologicalAddGroup : TopologicalAddGroup (∀ i : k, Matrix (s i) (s i) ℂ) :=
--   by
--   apply @Pi.topologicalAddGroup _ _ _ _ _
  -- intro b
  -- infer_instance

-- instance Pi.matrix.continuousSMul : ContinuousSMul ℂ PiMat ℂ k s := by infer_instance

theorem Pi.rankOneLm_real_apply {k₂ : Type*} [Fintype k₂] [DecidableEq k₂]
  {s₂ : k₂ → Type*} [Π i, Fintype (s₂ i)] [Π i, DecidableEq (s₂ i)]
  {φ : Π i, Module.Dual ℂ (Matrix (s₂ i) (s₂ i) ℂ)}
  [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  [hφ : ∀ i, (φ i).IsFaithfulPosMap]
  (x : PiMat ℂ k s) (y : PiMat ℂ k₂ s₂) :
    LinearMap.real (rankOne ℂ x y : (PiMat ℂ k₂ s₂) →ₗ[ℂ] (PiMat ℂ k s)) =
      rankOne ℂ (star x) (Module.Dual.pi.IsFaithfulPosMap.sig hφ (-1) (star y)) :=
  by
  rw [LinearMap.ext_iff]
  intro x_1
  simp only [LinearMap.real_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    star_smul, ← starRingEnd_apply]
  have := @Pi.inner_symm _ _ _ _ _ _ hφ (star x_1) y
  rw [star_star] at this
  rw [← this, inner_conj_symm]

theorem Pi.PosDef.rpow_one_eq_self {Q : PiMat ℂ k s} (hQ : ∀ i, (Q i).PosDef) : Pi.PosDef.rpow hQ 1 = Q :=
  by
  ext i
  simp only [Pi.PosDef.rpow, Matrix.PosDef.rpow_one_eq_self]

theorem Pi.PosDef.rpow_neg_one_eq_inv_self {Q : PiMat ℂ k s} (hQ : ∀ i, (Q i).PosDef) :
    Pi.PosDef.rpow hQ (-1) = Q⁻¹ := by
  ext i
  simp_rw [Pi.PosDef.rpow, Matrix.PosDef.rpow_neg_one_eq_inv_self (hQ _), Pi.inv_apply]

theorem Module.Dual.pi.IsFaithfulPosMap.inner_left_conj'
    {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (a b c : PiMat ℂ k s) :
    ⟪a, b * c⟫_ℂ = ⟪a * Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star c), b⟫_ℂ := by
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.sig_apply, neg_neg, Pi.PosDef.rpow_one_eq_self,
    Pi.PosDef.rpow_neg_one_eq_inv_self, ← Module.Dual.pi.matrixBlock_apply, ←
    Module.Dual.pi.IsFaithfulPosMap.inner_left_conj]

theorem Module.Dual.pi.IsFaithfulPosMap.inner_right_conj'
    {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (a b c : PiMat ℂ k s) :
    ⟪a * c, b⟫_ℂ = ⟪a, b * Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star c)⟫_ℂ := by
  rw [← inner_conj_symm, Module.Dual.pi.IsFaithfulPosMap.inner_left_conj', inner_conj_symm]

theorem Moudle.Dual.Pi.IsFaithfulPosMap.sig_trans_sig [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x y : ℝ) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ y).trans (Module.Dual.pi.IsFaithfulPosMap.sig hψ x) =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ (x + y) :=
  by
  ext1
  simp_rw [AlgEquiv.trans_apply, Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_comp_sig [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x y : ℝ) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ x).toLinearMap.comp
        (Module.Dual.pi.IsFaithfulPosMap.sig hψ y).toLinearMap =
      (Module.Dual.pi.IsFaithfulPosMap.sig hψ (x + y)).toLinearMap :=
  by
  rw [LinearMap.ext_iff]
  intro x_1
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_zero' [hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
    Module.Dual.pi.IsFaithfulPosMap.sig hψ 0 = 1 :=
  by
  rw [AlgEquiv.ext_iff]
  intros
  rw [Module.Dual.pi.IsFaithfulPosMap.sig_zero]
  rfl

theorem Pi.comp_sig_eq_iff
  {A : Type*} [AddCommMonoid A] [Module ℂ A]
  [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  (t : ℝ) (f g : PiMat ℂ k s →ₗ[ℂ] A) :
    f ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ t).toLinearMap = g ↔
      f = g ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-t)).toLinearMap :=
  by
  constructor <;> rintro rfl
  all_goals rw [LinearMap.comp_assoc, Module.Dual.pi.IsFaithfulPosMap.sig_comp_sig]
  on_goal 1 => rw [add_neg_self]
  on_goal 2 => rw [neg_add_self]
  all_goals
    rw [Module.Dual.pi.IsFaithfulPosMap.sig_zero', AlgEquiv.one_toLinearMap, LinearMap.comp_one]

theorem Pi.sig_comp_eq_iff {A : Type*} [AddCommMonoid A] [Module ℂ A]
  [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (t : ℝ) (f g : A →ₗ[ℂ] PiMat ℂ k s) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ t).toLinearMap ∘ₗ f = g ↔
      f = (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-t)).toLinearMap ∘ₗ g :=
  by
  constructor <;> rintro rfl
  all_goals rw [← LinearMap.comp_assoc, Module.Dual.pi.IsFaithfulPosMap.sig_comp_sig]
  on_goal 1 => rw [neg_add_self]
  on_goal 2 => rw [add_neg_self]
  all_goals
    rw [Module.Dual.pi.IsFaithfulPosMap.sig_zero', AlgEquiv.one_toLinearMap, LinearMap.one_comp]

theorem LinearMap.pi.adjoint_real_eq {k₂ : Type*} [Fintype k₂] [DecidableEq k₂]
  {s₂ : k₂ → Type*} [Π i, Fintype (s₂ i)] [Π i, DecidableEq (s₂ i)]
  {φ : Π i, Module.Dual ℂ (Matrix (s₂ i) (s₂ i) ℂ)}
  {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    [hφ : ∀ i, (φ i).IsFaithfulPosMap] (f : PiMat ℂ k s →ₗ[ℂ] PiMat ℂ k₂ s₂) :
    (LinearMap.adjoint f).real =
      (Module.Dual.pi.IsFaithfulPosMap.sig hψ 1).toLinearMap ∘ₗ
        (LinearMap.adjoint f.real) ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hφ (-1)).toLinearMap :=
  by
  rw [LinearMap.ext_iff]
  intro x
  apply ext_inner_right ℂ
  intro u
  nth_rw 1 [Pi.inner_symm]
  simp_rw [LinearMap.real_apply, star_star, LinearMap.adjoint_inner_right]
  nth_rw 1 [Pi.inner_symm]
  simp_rw [star_star, ← Module.Dual.pi.IsFaithfulPosMap.sig_star, ← LinearMap.real_apply f,
    LinearMap.comp_apply, ← LinearMap.adjoint_inner_left f.real, ← AlgEquiv.toLinearMap_apply, ←
    LinearMap.adjoint_inner_left (Module.Dual.pi.IsFaithfulPosMap.sig hψ 1).toLinearMap,
    Module.Dual.pi.IsFaithfulPosMap.sig_adjoint]

theorem Module.Dual.pi.IsFaithfulPosMap.basis.apply_cast_eq_mp
    [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    {i j : k} (h : i = j) (p : s i × s i) :
    (by rw [h] : Matrix (s i) (s i) ℂ = Matrix (s j) (s j) ℂ).mp ((hψ i).basis p) =
      (hψ j).basis (by rw [← h]; exact p) :=
  by aesop

lemma Matrix.includeBlock_apply' (x : PiMat ℂ k s) (i j : k) :
  (includeBlock (x i)) j = ite (i = j) (x j) 0 :=
by simp [includeBlock_apply]; aesop

theorem pi_lmul_toMatrix [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : PiMat ℂ k s) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix hψ (lmul x) :
        Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) =
      blockDiagonal' fun i => (x i ⊗ₖ 1) :=
  by
  ext r l
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.toMatrix_apply', lmul_apply, hMul_includeBlock]
  rw [blockDiagonal'_apply]
  let x' : PiMat ℂ k s := fun a =>
    if h : a = l.fst then (x a * ((hψ a).basis) (by rw [h]; exact l.snd)) else 0
  have hx' : x' l.fst = x l.fst * (hψ l.fst).basis l.snd := by aesop
  rw [← hx', includeBlock_apply', ite_mul, zero_mul]
  rw [ite_apply, Pi.zero_apply, ite_apply, Pi.zero_apply]
  simp_rw [kroneckerMap_apply, one_apply, mul_boole, @eq_comm _ r.fst]
  simp_rw [x', Module.Dual.IsFaithfulPosMap.basis_apply, dite_hMul,
    zero_mul, Matrix.mul_assoc, PosDef.rpow_mul_rpow, neg_add_self,
    PosDef.rpow_zero, Matrix.mul_one, stdBasisMatrix_eq]
  split_ifs with h hh hhh
  . simp only [mul_apply, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one, ← h, ite_and, hh]
    split_ifs with hhhh; rfl; rw [eq_comm] at hhh; contradiction
  . rw [eq_comm] at h
    simp [h, hh, hhh, ite_and, mul_apply]
    intro ha
    rw [eq_comm] at ha
    contradiction
  . rw [eq_comm] at h; contradiction
  . rfl
  . rfl

example [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : PiMat ℂ k s) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix hψ (lmul x) :
        Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) =
      blockDiagonal' fun i => (hψ i).toMatrix (lmul (x i)) :=
  by simp_rw [pi_lmul_toMatrix, lmul_eq_mul, LinearMap.mulLeft_toMatrix]

theorem pi_rmul_toMatrix [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : PiMat ℂ k s) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix hψ (rmul x) :
        Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) =
      blockDiagonal' fun i => (1 ⊗ₖ ((hψ i).sig (1 / 2) (x i))ᵀ) :=
  by
  ext r l
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.toMatrix_apply', rmul_apply, includeBlock_hMul]
  rw [blockDiagonal'_apply]
  let x' : PiMat ℂ k s := fun a =>
    if h : a = l.fst then (((hψ a).basis) (by rw [h]; exact l.snd) * x a) else 0
  have hx' : x' l.fst = (hψ l.fst).basis l.snd * x l.fst := by aesop
  rw [← hx', includeBlock_apply', ite_mul, zero_mul]
  rw [ite_apply, Pi.zero_apply, ite_apply, Pi.zero_apply]
  simp_rw [kroneckerMap_apply, one_apply, boole_mul, @eq_comm _ r.fst]
  simp_rw [x', Module.Dual.IsFaithfulPosMap.basis_apply, dite_hMul,
    zero_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (PosDef.rpow _ (- (1 / 2))),
    ← Module.Dual.IsFaithfulPosMap.sig_apply, stdBasisMatrix_eq, Matrix.transpose_apply]
  split_ifs with h hh hhh
  . simp only [mul_apply, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one, ← h, ite_and, hh, one_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
    split_ifs with hhhh; rfl; rw [eq_comm] at hhh; contradiction
  . rw [eq_comm] at h
    simp [h, hh, hhh, ite_and, mul_apply]
    intro ha
    rw [eq_comm] at ha
    contradiction
  . rw [eq_comm] at h; contradiction
  . rfl
  . rfl

theorem unitary.coe_pi (U : ∀ i, unitaryGroup (s i) ℂ) :
    (unitary.pi U : PiMat ℂ k s) = ↑U :=
  rfl

theorem unitary.coe_pi_apply (U : ∀ i, unitaryGroup (s i) ℂ) (i : k) :
    (↑U : PiMat ℂ k s) i = U i :=
  rfl

theorem pi_inner_aut_toMatrix
    [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (U : ∀ i, unitaryGroup (s i) ℂ) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix hψ
          ((unitary.innerAutStarAlg ℂ (unitary.pi U)).toLinearMap) :
        Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) =
      blockDiagonal' fun i =>
        U i ⊗ₖ ((hψ i).sig (-(1 / 2 : ℝ)) (U i : Matrix (s i) (s i) ℂ))ᴴᵀ :=
  by
  have :
    ((unitary.innerAutStarAlg ℂ (unitary.pi U)).toLinearMap) =
      (lmul (↑U : PiMat ℂ k s)) * (rmul (star (↑U : PiMat ℂ k s))) :=
    by
    rw [LinearMap.ext_iff]
    intro x
    simp only [StarAlgEquiv.toLinearMap_apply, LinearMap.mul_apply,
      lmul_apply, rmul_apply, unitary.innerAutStarAlg_apply, mul_assoc, unitary.coe_star,
      unitary.coe_pi]
  rw [this, _root_.map_mul, pi_lmul_toMatrix, pi_rmul_toMatrix, ← blockDiagonal'_mul]
  simp_rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Pi.star_apply,
    star_eq_conjTranspose, blockDiagonal'_inj]
  nth_rw 1 [← neg_neg (1 / 2 : ℝ)]
  simp_rw [← Module.Dual.IsFaithfulPosMap.sig_conjTranspose]
  rfl


end DirectSum
