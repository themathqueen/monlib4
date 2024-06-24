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
  simp_rw [AlgEquiv.trans_apply, Module.Dual.IsFaithfulPosMap.sig_apply_sig, add_comm]

theorem Module.Dual.IsFaithfulPosMap.sig_comp_sig  [hφ : φ.IsFaithfulPosMap] (x y : ℝ) :
    (hφ.sig x).toLinearMap.comp (hφ.sig y).toLinearMap =
      (hφ.sig (x + y)).toLinearMap :=
  by
  ext1
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
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
      one_smul, AlgEquiv.toLinearMap_apply, sig_map_one]
  . rw [← sig_adjoint, Coalgebra.comul_eq_mul_adjoint]
    rw [LinearMap.adjoint_commutes_with_mul_adjoint_iff]
    intro x y
    simp_rw [AlgEquiv.toLinearMap_apply, _root_.map_mul]

set_option synthInstance.checkSynthOrder false in
noncomputable instance Module.Dual.IsFaithfulPosMap.quantumSet [hφ : φ.IsFaithfulPosMap] :
    QuantumSet (Matrix n n ℂ) where
  modAut r := hφ.sig r
  modAut_trans r s := sig_trans_sig _ _
  modAut_zero := by
    ext1
    exact Module.Dual.IsFaithfulPosMap.sig_zero _ _
  modAut_star r x := sig_conjTranspose _ _ _
  modAut_isSymmetric r x y := by
    simp_rw [← AlgEquiv.toLinearMap_apply]
    nth_rw 1 [← sig_adjoint]
    simp_rw [LinearMap.adjoint_inner_left]
  -- modAut_isCoalgHom r := Module.Dual.IsFaithfulPosMap.sig_isCoalgHom _ _
  inner_star_left x y z := by simp_rw [inner_left_hMul]; rfl
  inner_conj_left x y z := by
    simp_rw [Module.Dual.IsFaithfulPosMap.inner_right_conj, sig_apply, neg_neg,
      PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self]
    rfl
  n := n × n
  n_isFintype := by infer_instance
  n_isDecidableEq := by infer_instance
  onb := hφ.orthonormalBasis
  map_one' := rfl
  map_mul' x y := _root_.map_mul _ _ _
  map_zero' := _root_.map_zero _
  map_add' := _root_.map_add _
  commutes' := Algebra.commutes
  smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]

-- ay! `rfl`!
example [φ.IsFaithfulPosMap] :
  (QuantumSet.toInnerProductStarAlgebra.toInnerProductAlgebra.toAlgebra : Algebra ℂ (Matrix n n ℂ)) = Matrix.instAlgebra :=
rfl
-- by
--   apply IsScalarTower.Algebra.ext
--   exact (fun r x ↦ rfl)

variable {k : Type*} [Fintype k] [DecidableEq k] {s : k → Type*} [Π i, Fintype (s i)]
  [Π i, DecidableEq (s i)] {ψ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}

theorem Module.Dual.pi.IsFaithfulPosMap.sig_isCoalgHom (hψ : Π i, (ψ i).IsFaithfulPosMap)
  (r : ℝ) :
  (sig hψ r).toLinearMap.IsCoalgHom :=
by
  constructor
  . rw [← sig_adjoint, Coalgebra.counit_eq_unit_adjoint, ← LinearMap.adjoint_comp]
    congr 1
    ext1
    simp_rw [LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      one_smul, AlgEquiv.toLinearMap_apply, _root_.map_one]
  . rw [← sig_adjoint, Coalgebra.comul_eq_mul_adjoint]
    rw [LinearMap.adjoint_commutes_with_mul_adjoint_iff]
    intro x y
    simp_rw [AlgEquiv.toLinearMap_apply, _root_.map_mul]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_trans_sig (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (x y : ℝ) :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ x).trans (Module.Dual.pi.IsFaithfulPosMap.sig hψ y) =
      Module.Dual.pi.IsFaithfulPosMap.sig hψ (x + y) :=
by rw [Moudle.Dual.Pi.IsFaithfulPosMap.sig_trans_sig, add_comm]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_isSymmetric (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    (r : ℝ) (x y : PiMat ℂ k s) :
  ⟪sig hψ r x, y⟫_ℂ = ⟪x, sig hψ r y⟫_ℂ :=
by rw [← AlgEquiv.toLinearMap_apply, ← sig_adjoint, LinearMap.adjoint_inner_left,
  AlgEquiv.toLinearMap_apply]

noncomputable
instance Module.Dual.pi.IsFaithfulPosMap.innerProductAlgebra [hψ : Π i, (ψ i).IsFaithfulPosMap] :
    InnerProductAlgebra (PiMat ℂ k s) :=
{ (Pi.ringHom fun i => algebraMap ℂ (Matrix (s i) (s i) ℂ) : _ →+* ∀ i : _, Matrix (s i) (s i) ℂ) with
    commutes' := fun a f => by ext1; simp [Algebra.commutes]
    smul_def' := fun a f => by ext1; simp [Algebra.smul_def] }

-- set_option synthInstance.checkSynthOrder false in
set_option maxHeartbeats 500000 in
noncomputable instance Module.Dual.pi.IsFaithfulPosMap.quantumSet
  [hψ : Π i, (ψ i).IsFaithfulPosMap] :
    QuantumSet (PiMat ℂ k s) where
  modAut r := (Module.Dual.pi.IsFaithfulPosMap.sig hψ r : PiMat ℂ k s ≃ₐ[ℂ] PiMat ℂ k s)
  modAut_trans r s := Module.Dual.pi.IsFaithfulPosMap.sig_trans_sig hψ _ _
  modAut_zero := Module.Dual.pi.IsFaithfulPosMap.sig_zero'
  modAut_star r x := Module.Dual.pi.IsFaithfulPosMap.sig_star _ _ _
  modAut_isSymmetric r x y :=
    by simp only; exact Module.Dual.pi.IsFaithfulPosMap.sig_isSymmetric hψ _ _ _
  -- modAut_isCoalgHom r :=
  --   by simp only; exact Module.Dual.pi.IsFaithfulPosMap.sig_isCoalgHom hψ r
  inner_star_left x y z := by
    simp_rw [inner_left_hMul]
  inner_conj_left x y z := by
    simp_rw [Module.Dual.pi.IsFaithfulPosMap.inner_right_conj']
  n := Σ i, (s i) × (s i)
  n_isFintype := by infer_instance
  n_isDecidableEq := by infer_instance
  onb := Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hψ
  -- commutes' a f := by ext1; simp only [RingHom.coe_mk, MonoidHom.coe_mk, Pi.mul_apply]
  -- smul_def' a f := by ext1; simp only [Pi.smul_apply, RingHom.coe_mk, MonoidHom.coe_mk,
  --   Pi.mul_apply]
