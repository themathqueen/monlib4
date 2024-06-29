import Monlib.LinearAlgebra.QuantumSet.Basic
import Monlib.LinearAlgebra.Ips.MatIps
import Monlib.LinearAlgebra.QuantumSet.Pi
-- import Monlib.LinearAlgebra.Ips.Frob

variable {n : Type*} [Fintype n] [DecidableEq n] {φ : Module.Dual ℂ (Matrix n n ℂ)}

open Matrix

open scoped Functional

@[simps]
noncomputable def sig (hφ : φ.IsFaithfulPosMap) (z : ℝ) :
    Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ where
  toFun a := hφ.matrixIsPosDef.rpow (-z) * a * hφ.matrixIsPosDef.rpow z
  invFun a := hφ.matrixIsPosDef.rpow z * a * hφ.matrixIsPosDef.rpow (-z)
  left_inv a := by
    simp_rw [Matrix.mul_assoc, PosDef.rpow_mul_rpow, ← Matrix.mul_assoc, PosDef.rpow_mul_rpow,
      add_neg_self, PosDef.rpow_zero, Matrix.one_mul, Matrix.mul_one]
  right_inv a := by
    simp_rw [Matrix.mul_assoc, PosDef.rpow_mul_rpow, ← Matrix.mul_assoc, PosDef.rpow_mul_rpow,
      neg_add_self, PosDef.rpow_zero, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by simp_rw [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    simp_rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      PosDef.rpow_mul_rpow, neg_add_self, PosDef.rpow_zero]
  map_mul' x y := by
    simp_rw [Matrix.mul_assoc, ← Matrix.mul_assoc (hφ.matrixIsPosDef.rpow _),
      PosDef.rpow_mul_rpow, add_neg_self, PosDef.rpow_zero, Matrix.one_mul]

theorem Module.Dual.IsFaithfulPosMap.sig_trans_sig [hφ : φ.IsFaithfulPosMap] (x y : ℝ) :
    (sig hφ x).trans (sig hφ y) = sig hφ (x + y) :=
  by
  ext1
  simp_rw [AlgEquiv.trans_apply,
    sig_apply, ← mul_assoc, PosDef.rpow_mul_rpow,
    mul_assoc, PosDef.rpow_mul_rpow, neg_add, add_comm]

set_option synthInstance.checkSynthOrder false in
@[default_instance] noncomputable instance Matrix.isStarAlgebra [hφ : φ.IsFaithfulPosMap] :
    starAlgebra (Matrix n n ℂ) where
  modAut := sig hφ
  modAut_trans := Module.Dual.IsFaithfulPosMap.sig_trans_sig
  modAut_zero := by
    ext1
    simp only [sig_apply, neg_zero, PosDef.rpow_zero, one_mul, mul_one,
      AlgEquiv.one_apply]
  modAut_star r x := by
    simp_rw [sig_apply, star_mul, star_eq_conjTranspose,
      neg_neg, (Matrix.PosDef.rpow.isPosDef _ _).1.eq,
      mul_assoc]

set_option synthInstance.checkSynthOrder false in
@[instance]
noncomputable def Module.Dual.IsFaithfulPosMap.innerProductAlgebra [hφ : φ.IsFaithfulPosMap] :
    InnerProductAlgebra (Matrix n n ℂ) where
  -- norm_smul_le _ _ := by rw [← norm_smul]
  norm_sq_eq_inner := norm_sq_eq_inner (𝕜 := ℂ)
  conj_symm := inner_conj_symm
  add_left := inner_add_left
  smul_left := inner_smul_left

set_option synthInstance.checkSynthOrder false in
@[instance]
noncomputable
def Module.Dual.IsFaithfulPosMap.quantumSet [hφ : φ.IsFaithfulPosMap] :
    QuantumSet (Matrix n n ℂ) where
  -- modAut r := hφ.sig r
  -- modAut_trans r s := sig_trans_sig _ _
  -- modAut_zero := by
    -- ext1
    -- exact Module.Dual.IsFaithfulPosMap.sig_zero _ _
  -- modAut_star r x := sig_conjTranspose _ _ _
  modAut_isSymmetric r x y := by
    simp_rw [← AlgEquiv.toLinearMap_apply, modAut, AlgEquiv.toLinearMap_apply, sig_apply,
      mul_assoc]
    rw [inner_left_hMul, inner_right_conj]
    simp_rw [(PosDef.rpow.isPosDef _ _).1.eq]
    nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
    nth_rw 1 [← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef]
    simp_rw [PosDef.rpow_mul_rpow, mul_assoc]
    ring_nf
  k := 0
  -- modAut_isCoalgHom r := Module.Dual.IsFaithfulPosMap.sig_isCoalgHom _ _
  inner_star_left x y z := by simp_rw [neg_zero,
    inner_left_hMul, star_eq_conjTranspose,
    modAut, sig_apply, neg_zero, PosDef.rpow_zero, one_mul, mul_one]
  inner_conj_left x y z := by
    simp_rw [neg_zero, zero_sub,
      Module.Dual.IsFaithfulPosMap.inner_right_conj,
      modAut, sig_apply, neg_neg,
      PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self]
    rfl
  n := n × n
  n_isFintype := by infer_instance
  n_isDecidableEq := by infer_instance
  onb := hφ.orthonormalBasis
  -- map_one' := rfl
  -- map_mul' x y := _root_.map_mul _ _ _
  -- map_zero' := _root_.map_zero _
  -- map_add' := _root_.map_add _
  -- commutes' := Algebra.commutes
  -- smul_def' r x := by ext; simp [Matrix.scalar, Algebra.smul_def r]

variable {k : Type*} [Fintype k] [DecidableEq k] {s : k → Type*} [Π i, Fintype (s i)]
  [Π i, DecidableEq (s i)] {ψ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}

-- theorem Module.Dual.pi.IsFaithfulPosMap.sig_trans_sig (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
--     (x y : ℝ) :
--     (Module.Dual.pi.IsFaithfulPosMap.sig hψ x).trans (Module.Dual.pi.IsFaithfulPosMap.sig hψ y) =
--       Module.Dual.pi.IsFaithfulPosMap.sig hψ (x + y) :=
-- by rw [Moudle.Dual.Pi.IsFaithfulPosMap.sig_trans_sig, add_comm]

-- theorem Module.Dual.pi.IsFaithfulPosMap.sig_isSymmetric (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
--     (r : ℝ) (x y : PiMat ℂ k s) :
--   ⟪sig hψ r x, y⟫_ℂ = ⟪x, sig hψ r y⟫_ℂ :=
-- by rw [← AlgEquiv.toLinearMap_apply, ← sig_adjoint, LinearMap.adjoint_inner_left,
  -- AlgEquiv.toLinearMap_apply]

set_option synthInstance.checkSynthOrder false in
noncomputable instance PiMat.isStarAlgebra [∀ i, (ψ i).IsFaithfulPosMap] :
  starAlgebra (PiMat ℂ k s) :=
piStarAlgebra


-- attribute [-instance] Pi.module.Dual.isNormedAddCommGroupOfRing
set_option synthInstance.checkSynthOrder false in
noncomputable
instance Module.Dual.pi.IsFaithfulPosMap.innerProductAlgebra
[∀ i, (ψ i).IsFaithfulPosMap] :
  InnerProductAlgebra (PiMat ℂ k s) :=
piInnerProductAlgebra
-- letI : _root_.NormedAddCommGroup (PiMat ℂ k s) := by infer_instance
-- letI : _root_.NormedSpace ℂ (PiMat ℂ k s) := by infer_instance
-- letI : _root_.InnerProductSpace ℂ (PiMat ℂ k s) := by infer_instance
-- { norm_smul_le := λ r x => by
--     rw [← norm_smul_le]
    -- exact @norm_smul_le ℂ (PiMat ℂ k s) _ _ _ _ r x
    -- rw [norm_eq_sqrt_inner (𝕜 := ℂ), inner_smul_left, inner_smul_right]
    -- simp only [RCLike.re_to_complex, Complex.norm_eq_abs, ← mul_assoc,
    --   Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    -- rw [Real.sqrt_mul (pow_two_nonneg _), Real.sqrt_sq, norm_eq_sqrt_inner (𝕜 := ℂ)]
    -- rfl
    -- simp only [apply_nonneg]
  -- norm_sq_eq_inner := norm_sq_eq_inner (𝕜 := ℂ)
  -- conj_symm := inner_conj_symm
  -- add_left := inner_add_left
  -- smul_left := inner_smul_left }

-- set_option synthInstance.checkSynthOrder false in
set_option maxHeartbeats 500000 in
noncomputable instance Module.Dual.pi.IsFaithfulPosMap.quantumSet
  [hψ : Π i, (ψ i).IsFaithfulPosMap] :
    QuantumSet (PiMat ℂ k s) :=
  letI : Fact (∀ (i : k), QuantumSet.k (Matrix (s i) (s i) ℂ) = 0) :=
  by apply Fact.mk; intro; rfl
  Pi.quantumSet
  -- modAut r := (Module.Dual.pi.IsFaithfulPosMap.sig hψ r : PiMat ℂ k s ≃ₐ[ℂ] PiMat ℂ k s)
  -- modAut_trans r s := Module.Dual.pi.IsFaithfulPosMap.sig_trans_sig hψ _ _
  -- modAut_zero := Module.Dual.pi.IsFaithfulPosMap.sig_zero'
  -- modAut_star r x := Module.Dual.pi.IsFaithfulPosMap.sig_star _ _ _
  -- modAut_isSymmetric r x y :=
  --   by simp only; exact Module.Dual.pi.IsFaithfulPosMap.sig_isSymmetric hψ _ _ _
  -- -- modAut_isCoalgHom r :=
  -- --   by simp only; exact Module.Dual.pi.IsFaithfulPosMap.sig_isCoalgHom hψ r
  -- k := 0
  -- inner_star_left x y z := by
  --   simp_rw [neg_zero, sig_zero, inner_left_hMul]
  -- inner_conj_left x y z := by
  --   simp_rw [neg_zero, zero_sub, Module.Dual.pi.IsFaithfulPosMap.inner_right_conj']
  -- n := Σ i, (s i) × (s i)
  -- n_isFintype := by infer_instance
  -- n_isDecidableEq := by infer_instance
  -- onb := Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hψ
  -- commutes' a f := by ext1; simp only [RingHom.coe_mk, MonoidHom.coe_mk, Pi.mul_apply]
  -- smul_def' a f := by ext1; simp only [Pi.smul_apply, RingHom.coe_mk, MonoidHom.coe_mk,
  --   Pi.mul_apply]
