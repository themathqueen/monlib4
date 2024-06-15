import Monlib.LinearAlgebra.QuantumSet.Basic
import Monlib.LinearAlgebra.Ips.Nontracial
import Monlib.LinearAlgebra.Ips.Frob

variable {n : Type*} [Fintype n] [DecidableEq n] {φ : Module.Dual ℂ (Matrix n n ℂ)}

open Matrix

lemma Module.Dual.IsFaithfulPosMap.sig_map_one (hφ : φ.IsFaithfulPosMap) (r : ℝ) :
  hφ.sig r 1 = 1 :=
by simp only [sig_apply, mul_one, PosDef.rpow_mul_rpow, neg_add_self, PosDef.rpow_zero]

open scoped Functional

theorem Module.Dual.IsFaithfulPosMap.sig_trans_sig [hφ : φ.IsFaithfulPosMap] (x y : ℝ) :
    (hφ.sig x).trans (hφ.sig y) = hφ.sig (x + y) :=
  by
  ext1
  simp_rw [LinearEquiv.trans_apply, Module.Dual.IsFaithfulPosMap.sig_apply_sig, add_comm]

theorem Module.Dual.IsFaithfulPosMap.sig_comp_sig  [hφ : φ.IsFaithfulPosMap] (x y : ℝ) :
    (hφ.sig x).toLinearMap.comp (hφ.sig y).toLinearMap =
      (hφ.sig (x + y)).toLinearMap :=
  by
  ext1
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig]

theorem Module.Dual.IsFaithfulPosMap.sig_isCoalgHom
  (hφ : φ.IsFaithfulPosMap)
  (r : ℝ) :
  (sig hφ r).toLinearMap.IsCoalgHom :=
by
  constructor
  . rw [← sig_adjoint, Coalgebra.counit_eq_unit_adjoint, ← LinearMap.adjoint_comp]
    congr 1
    ext1
    simp_rw [LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      one_smul, LinearEquiv.coe_toLinearMap, sig_map_one]
  . rw [← sig_adjoint, Coalgebra.comul_eq_mul_adjoint]
    rw [LinearMap.adjoint_commutes_with_mul_adjoint_iff]
    intro x y
    simp_rw [LinearEquiv.coe_toLinearMap]
    exact sig.map_mul' x y

-- attribute [instance 10] Algebra.ofIsScalarTowerSmulCommClass
set_option synthInstance.checkSynthOrder false in
-- set_option maxHeartbeats 0 in
noncomputable instance Module.Dual.IsFaithfulPosMap.quantumSet [hφ : φ.IsFaithfulPosMap] :
    QuantumSet (Matrix n n ℂ) where
  -- toNormedAddCommGroupOfRing := φ.isNormedAddCommGroupOfRing
  -- toInnerProductSpace := φ.InnerProductSpace
  modAut r := hφ.sig r
  modAut_map_mul r := Module.Dual.IsFaithfulPosMap.sig.map_mul'
  modAut_map_one r := sig_map_one _ _
  modAut_trans r s := sig_trans_sig _ _
  modAut_zero := by
    ext1
    exact Module.Dual.IsFaithfulPosMap.sig_zero _ _
  modAut_star r x := sig_conjTranspose _ _ _
  modAut_isSymmetric r x y := by
    simp_rw [← LinearEquiv.coe_toLinearMap]
    nth_rw 1 [← sig_adjoint]
    simp_rw [LinearMap.adjoint_inner_left]
  modAut_isCoalgHom r := Module.Dual.IsFaithfulPosMap.sig_isCoalgHom _ _
  inner_star_left x y z := by simp_rw [inner_left_hMul]; rfl
  inner_conj_left x y z := by
    simp_rw [Module.Dual.IsFaithfulPosMap.inner_right_conj, sig_apply, neg_neg,
      PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self]
    rfl
  n := n × n
  n_isFintype := by infer_instance
  n_isDecidableEq := by infer_instance
  onb := hφ.orthonormalBasis

example [hφ : φ.IsFaithfulPosMap] :
  (QuantumSet.toAlgebra : Algebra ℂ (Matrix n n ℂ)) = Matrix.instAlgebra :=
-- rfl
by
  apply IsScalarTower.Algebra.ext
  exact (fun r x ↦ rfl)

theorem Module.Dual.pi.IsFaithfulPosMap.sig_isCoalgHom {k : Type*} [Fintype k] [DecidableEq k] {s : k → Type*} [Π i, Fintype (s i)]
  [Π i, DecidableEq (s i)] {ψ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} (hψ : Π i, (ψ i).IsFaithfulPosMap)
  (r : ℝ) :
  (sig hψ r).toLinearMap.IsCoalgHom :=
by
  constructor
  . rw [← sig_adjoint, Coalgebra.counit_eq_unit_adjoint, ← LinearMap.adjoint_comp]
    congr 1
    ext1
    simp_rw [LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      one_smul, LinearEquiv.coe_toLinearMap, sig_map_one]
  . rw [← sig_adjoint, Coalgebra.comul_eq_mul_adjoint]
    rw [LinearMap.adjoint_commutes_with_mul_adjoint_iff]
    intro x y
    simp_rw [LinearEquiv.coe_toLinearMap]
    exact sig_map_mul _ x y

set_option synthInstance.checkSynthOrder false in
set_option maxHeartbeats 0 in
noncomputable instance Module.Dual.pi.IsFaithfulPosMap.quantumSet
  {k : Type*} [Fintype k] [DecidableEq k] {s : k → Type*} [Π i, Fintype (s i)]
  [Π i, DecidableEq (s i)] {ψ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : Π i, (ψ i).IsFaithfulPosMap] :
    QuantumSet (PiMat ℂ k s) where
  modAut r := pi.IsFaithfulPosMap.sig hψ r
  modAut_map_mul r := sig_map_mul _
  modAut_map_one r := sig_map_one _
  modAut_trans r s :=
    by simp_rw [Moudle.Dual.Pi.IsFaithfulPosMap.sig_trans_sig, add_comm]
  modAut_zero := Module.Dual.pi.IsFaithfulPosMap.sig_zero'
  modAut_star r x := Module.Dual.pi.IsFaithfulPosMap.sig_star _ _ _
  modAut_isSymmetric r x y := by
    simp_rw [← LinearEquiv.coe_toLinearMap]
    nth_rw 1 [← sig_adjoint]
    simp_rw [LinearMap.adjoint_inner_left]
  modAut_isCoalgHom r :=
    by simp only; exact Module.Dual.pi.IsFaithfulPosMap.sig_isCoalgHom hψ r
  inner_star_left x y z := by
    simp_rw [inner_left_hMul]
  inner_conj_left x y z := by
    simp_rw [Module.Dual.pi.IsFaithfulPosMap.inner_right_conj']
  n := Σ i, (s i) × (s i)
  n_isFintype := by infer_instance
  n_isDecidableEq := by infer_instance
  onb := Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hψ
