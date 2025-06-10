import Monlib.LinearAlgebra.QuantumSet.Basic
import Monlib.LinearAlgebra.Ips.MatIps
import Monlib.LinearAlgebra.QuantumSet.Pi
import Monlib.LinearAlgebra.QuantumSet.DeltaForm
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
      add_neg_cancel, PosDef.rpow_zero, Matrix.one_mul, Matrix.mul_one]
  right_inv a := by
    simp_rw [Matrix.mul_assoc, PosDef.rpow_mul_rpow, ← Matrix.mul_assoc, PosDef.rpow_mul_rpow,
      neg_add_cancel, PosDef.rpow_zero, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by simp_rw [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    simp_rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      PosDef.rpow_mul_rpow, neg_add_cancel, PosDef.rpow_zero]
  map_mul' x y := by
    simp_rw [Matrix.mul_assoc, ← Matrix.mul_assoc (hφ.matrixIsPosDef.rpow _),
      PosDef.rpow_mul_rpow, add_neg_cancel, PosDef.rpow_zero, Matrix.one_mul]

theorem Module.Dual.IsFaithfulPosMap.sig_trans_sig [hφ : φ.IsFaithfulPosMap] (x y : ℝ) :
    (sig hφ x).trans (sig hφ y) = sig hφ (x + y) :=
  by
  ext1
  simp_rw [AlgEquiv.trans_apply,
    sig_apply, ← mul_assoc, PosDef.rpow_mul_rpow,
    mul_assoc, PosDef.rpow_mul_rpow, neg_add, add_comm]

open scoped ComplexOrder

omit [DecidableEq n] in
theorem PosDef.smul {𝕜 : Type*} [RCLike 𝕜]
  {x : Matrix n n 𝕜} (hx : x.PosDef) (α : NNRealˣ) :
  ((((α : NNReal) : ℝ) : 𝕜) • x).PosDef := by
  constructor
  · calc
      ((((α : NNReal) : ℝ) : 𝕜) • x)ᴴ = star (((α : NNReal) : ℝ) : 𝕜) • xᴴ := by rw [conjTranspose_smul]
      _ = (((α : NNReal) : ℝ) : 𝕜) • x := by rw [RCLike.star_def, RCLike.conj_ofReal, hx.1.eq]
  . intro y hy
    simp_rw [smul_mulVec_assoc, dotProduct_smul]
    exact mul_pos (RCLike.zero_lt_real.mpr (NNReal.coe_pos.mpr (Units.zero_lt α))) (hx.2 y hy)

theorem posSemidefOne_smul_rpow {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] (α : NNReal) (r : ℝ) :
    (PosSemidef.smul PosSemidef.one α :
      PosSemidef ((((α : NNReal) : ℝ) : 𝕜) • 1 : Matrix n n 𝕜)).rpow r
        = ((((α : NNReal) : ℝ) ^ r : ℝ) : 𝕜) • 1 :=
by
  rw [PosSemidef.rpow, IsHermitian.rpow, innerAut_eq_iff, _root_.map_smul, innerAut_apply_one]
  symm
  nth_rw 1 [← diagonal_one]
  rw [← diagonal_smul]
  rw [diagonal_eq_diagonal_iff]
  intro i
  simp_rw [Pi.smul_apply, Function.comp_apply, Pi.pow_apply]
  rw [← RCLike.ofReal_one, smul_eq_mul, ← RCLike.ofReal_mul,
    RCLike.ofReal_inj, IsHermitian.eigenvalues_eq',
    smul_mulVec_assoc, one_mulVec, dotProduct_smul,
    ← RCLike.real_smul_eq_coe_smul, RCLike.smul_re,
    Real.mul_rpow (NNReal.coe_nonneg _) _]
  all_goals
    simp_rw [dotProduct, Pi.star_apply, transpose_apply, ← conjTranspose_apply,
      ← mul_apply, IsHermitian.eigenvectorMatrix_conjTranspose_mul, one_apply_eq,
      RCLike.one_re]
  . simp only [mul_one, Real.one_rpow]
  . simp only [zero_le_one]

theorem posDefOne_smul_rpow {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] (α : NNRealˣ) (r : ℝ) :
    (PosDef.smul posDefOne α :
      PosDef ((((α : NNReal) : ℝ) : 𝕜) • 1 : Matrix n n 𝕜)).rpow r
        = ((((α : NNReal) : ℝ) ^ r : ℝ) : 𝕜) • 1 :=
by
  rw [PosDef.rpow_eq, innerAut_eq_iff, _root_.map_smul, innerAut_apply_one]
  symm
  nth_rw 1 [← diagonal_one]
  rw [← diagonal_smul]
  rw [diagonal_eq_diagonal_iff]
  intro i
  simp_rw [Pi.smul_apply, Function.comp_apply, Pi.pow_apply]
  rw [← RCLike.ofReal_one, smul_eq_mul, ← RCLike.ofReal_mul,
    RCLike.ofReal_inj, IsHermitian.eigenvalues_eq',
    smul_mulVec_assoc, one_mulVec, dotProduct_smul,
    ← RCLike.real_smul_eq_coe_smul, RCLike.smul_re,
    Real.mul_rpow (NNReal.coe_nonneg _) _]
  all_goals
    simp_rw [dotProduct, Pi.star_apply, transpose_apply, ← conjTranspose_apply,
      ← mul_apply, IsHermitian.eigenvectorMatrix_conjTranspose_mul, one_apply_eq,
      RCLike.one_re]
  . simp only [mul_one, Real.one_rpow]
  . simp only [zero_le_one]

theorem Module.Dual.IsFaithfulPosMap.sig_zero [hφ : φ.IsFaithfulPosMap] :
  sig hφ 0 = 1 :=
by
  ext1
  simp only [sig_apply, neg_zero, PosDef.rpow_zero, one_mul, mul_one,
    AlgEquiv.one_apply]

lemma AlgEquiv.apply_eq_id {R M : Type*} [CommSemiring R]
  [Semiring M] [Algebra R M] {f : M ≃ₐ[R] M} :
  (∀ (x : M), f x = x) ↔ f = 1 :=
by simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply]

theorem Matrix.PosDef.rpow_neg_eq_inv_rpow {𝕜 : Type*} [RCLike 𝕜] {n : Type _} [Fintype n] [DecidableEq n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) :
  hQ.rpow (-r) = (hQ.rpow r)⁻¹ :=
by
  haveI := (PosDef.rpow.isPosDef hQ r).invertible
  letI :=  Matrix.PosDef.eigenvaluesInvertible' hQ
  simp_rw [rpow_eq, innerAut.map_inv]
  haveI : Invertible (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ r) : n → 𝕜) :=
  { invOf := (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ (-r)) : n → 𝕜)
    invOf_mul_self := by
      ext
      simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply, Pi.one_apply]
      simp only [← RCLike.ofReal_mul]
      rw [← Real.rpow_add (eigenvalues_pos hQ _), neg_add_cancel, Real.rpow_zero,
        RCLike.ofReal_one]
    mul_invOf_self := by
      ext
      simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply, Pi.one_apply]
      simp only [← RCLike.ofReal_mul]
      rw [← Real.rpow_add (eigenvalues_pos hQ _), add_neg_cancel, Real.rpow_zero,
        RCLike.ofReal_one] }
  rw [Matrix.inv_diagonal']
  congr
  simp only [diagonal_eq_diagonal_iff, Function.comp_apply, Pi.pow_apply, Pi.inv_apply]
  simp only [← RCLike.ofReal_inv, Real.rpow_neg (le_of_lt (eigenvalues_pos hQ _)), implies_true]

theorem _root_.RCLike.pos_toNNReal_units {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) :
  0 < r ↔ ∃ s : NNRealˣ, r = (((s : NNReal) : ℝ) : 𝕜) :=
by
  refine ⟨λ h => ?_, λ ⟨s, hs⟩ => by
    simp only [hs, RCLike.ofReal_pos, NNReal.coe_pos,
      Units.zero_lt]⟩
  use Units.mk0 ⟨RCLike.re r, le_of_lt (RCLike.pos_def.mp h).1⟩
    (ne_of_gt (RCLike.pos_def.mp h).1)
  rw [Units.val_mk0, NNReal.coe_mk,
    RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.pos_def.mp h).2)]
theorem _root_.RCLike.nonneg_toNNReal {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) :
  0 ≤ r ↔ ∃ s : NNReal, r = (((s : NNReal) : ℝ) : 𝕜) :=
by
  refine ⟨λ h => ?_, λ ⟨s, hs⟩ => by
    simp only [hs, RCLike.ofReal_nonneg, NNReal.zero_le_coe]⟩
  use Real.toNNReal (RCLike.re r)
  nth_rw 1 [← (RCLike.nonneg_def'.mp h).1]
  simp only [algebraMap.coe_inj]
  rw [Real.toNNReal_of_nonneg ((RCLike.nonneg_def.mp h).1)]
  rfl

theorem _root_.Matrix.smulPosDef_isPosDef_iff {𝕜 : Type*} [RCLike 𝕜] {n : Type _} [Fintype n] [DecidableEq n]
  [H : Nonempty n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : 𝕜) :
  (r • Q).PosDef ↔ 0 < r :=
by
  have : ∃ a : n → 𝕜, ‖(WithLp.equiv 2 (n → 𝕜)).symm a‖ = 1 := by
    let j : n := H.some
    let a := λ i => if (i = j) then (1 : 𝕜) else 0
    use a
    calc ‖(WithLp.equiv 2 (n → 𝕜)).symm a‖
      = √(∑ i, ‖if (i = j) then (1 : 𝕜) else 0‖ ^ 2) :=
        by
          simp only [a, ← PiLp.norm_eq_of_L2]
          rfl
      _ = √(∑ i : n, if i = j then ‖(1 : 𝕜)‖ ^ 2 else ‖(0 : 𝕜)‖ ^ 2) := by
        simp only [norm_ite, ite_pow]
      _ = 1 := by
        simp only [norm_one, norm_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte, zero_pow (two_ne_zero), one_pow, Real.sqrt_one]
  obtain ⟨a, ha⟩ := this
  have ha2 : a ≠ 0 := by
    have : ‖(WithLp.equiv 2 (n → 𝕜)).symm a‖ ≠ 0 :=
      by
        simp only [ha]; simp only [ne_eq, one_ne_zero, not_false_eq_true]
    simp only [norm_ne_zero_iff] at this
    exact this
  refine ⟨λ ⟨_, h2⟩ => ?_, λ h => ?_⟩
  . simp_rw [smul_mulVec_assoc,
      dotProduct_smul, smul_eq_mul] at h2
    specialize h2 a ha2
    obtain ⟨b, hb, hb2⟩ := RCLike.pos_iff_exists_ofReal.mp (hQ.2 a ha2)
    rw [← hb2] at h2
    rw [mul_comm, RCLike.pos_def, RCLike.re_ofReal_mul, RCLike.im_ofReal_mul,
      mul_pos_iff] at h2
    simp_rw [hb, true_and, not_lt_of_gt hb, false_and, or_false,
      mul_eq_zero, ne_of_gt hb, false_or] at h2
    exact RCLike.pos_def.mpr h2
  . obtain ⟨s, rfl⟩ := (RCLike.pos_toNNReal_units r).mp h
    exact PosDef.smul hQ _

theorem smul_onePosDef_rpow_eq {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] {α : 𝕜}
    (h : ((α : 𝕜) • (1 : Matrix n n 𝕜)).PosDef) (r : ℝ) :
    h.rpow r = ((RCLike.re α ^ r : ℝ) : 𝕜) • 1 :=
by
  by_cases H : IsEmpty n
  . simp only [Complex.coe_smul, AlgEquiv.ext_iff, sig_apply,
      ← Matrix.ext_iff]
    simp only [AlgEquiv.one_apply, IsEmpty.forall_iff, implies_true, smul_apply, Complex.real_smul,
      exists_const, or_true]
  . rw [not_isEmpty_iff] at H
    have := (smulPosDef_isPosDef_iff (@posDefOne n _ _ _ _) α).mp h
    let p : NNRealˣ := Units.mk0 ⟨RCLike.re α, le_of_lt (RCLike.pos_def.mp this).1⟩
        (ne_of_gt (RCLike.pos_def.mp this).1)
    have : α = (((p : NNReal) : ℝ) : 𝕜) := by
      rw [← RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.pos_def.mp this).2)]
      rfl
    -- rw [this] at h
    rw [PosDef.rpow_cast h _ (by rw [this]), posDefOne_smul_rpow]
    exact rfl

theorem _root_.Matrix.smulPosSemidef_isPosSemidef_iff {𝕜 : Type*} [RCLike 𝕜] {n : Type _} [Fintype n] [DecidableEq n]
  {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) (r : 𝕜) :
  (r • Q).PosSemidef ↔ 0 ≤ r ∨ Q = 0 :=
by
  by_cases hr : r = 0
  . simp only [hr, zero_smul, le_refl, true_or, iff_true, PosSemidef.zero]
  . by_cases hQQ : Q = 0
    . simp_rw [hQQ, smul_zero, or_true, PosSemidef.zero]
    . simp only [hQQ, or_false]
      rw [PosSemidef, IsHermitian, conjTranspose_smul, hQ.1.eq]
      rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero]
      simp_rw [smul_mulVec_assoc, dotProduct_smul,
        RCLike.nonneg_def (K := 𝕜), ← RCLike.conj_eq_iff_im,
        starRingEnd_apply, star_smul, smul_eq_mul, RCLike.mul_re,
        (RCLike.nonneg_def.mp (hQ.2 _)), mul_zero, sub_zero,
        mul_nonneg_iff, RCLike.nonneg_def.mp (hQ.2 _), and_true,
        ← star_dotProduct, star_mulVec, hQ.1.eq, ← dotProduct_mulVec]
      simp only [hQQ, or_false]
      refine' ⟨λ ⟨h, h2⟩ => _, _⟩
      . rw [← Matrix.IsHermitian.eigenvalues_eq_zero_iff hQ.1] at hQQ
        simp only [funext_iff, Function.comp_apply, Pi.zero_apply,
          algebraMap.lift_map_eq_zero_iff, not_forall] at hQQ
        obtain ⟨i, hi⟩ := hQQ
        specialize h2 (hQ.1.eigenvectorMatrixᵀ i)
        rw [← IsHermitian.eigenvalues_eq'] at h2
        nth_rw 3 [le_iff_eq_or_lt] at h2
        simp only [hi, false_or, not_lt_of_ge (hQ.eigenvalues_nonneg _),
          and_false, or_false, h, and_true] at h2
        exact ⟨h2, h⟩
      . simp only [RCLike.star_def, mul_eq_mul_right_iff, and_imp]
        intro h hi
        refine ⟨hi, ?_⟩
        simp only [h, true_or, true_and, hi, implies_true]

theorem smul_onePosSemidef_rpow_eq {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] {α : 𝕜}
    (h : ((α : 𝕜) • (1 : Matrix n n 𝕜)).PosSemidef) (r : ℝ) :
    h.rpow r = ((RCLike.re α ^ r : ℝ) : 𝕜) • 1 :=
by
  by_cases H : IsEmpty n
  . simp only [Complex.coe_smul, AlgEquiv.ext_iff, sig_apply,
      ← Matrix.ext_iff]
    simp only [AlgEquiv.one_apply, IsEmpty.forall_iff, implies_true, smul_apply, Complex.real_smul,
      exists_const, or_true]
  . rw [not_isEmpty_iff] at H
    have := (smulPosSemidef_isPosSemidef_iff (@PosSemidef.one n _ _ _ _ _ _ _) α).mp h
    simp only [one_ne_zero, or_false] at this
    obtain ⟨s, rfl⟩ := (RCLike.nonneg_toNNReal α).mp this
    rw [posSemidefOne_smul_rpow]
    simp only [RCLike.ofReal_re]

theorem _root_.Matrix.smul_one_inv {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] {s : NNRealˣ} :
    ((((s : NNReal) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜))⁻¹
      = (((s⁻¹ : NNReal) : ℝ) : 𝕜) • 1 :=
by
  simp only [NNReal.coe_inv, RCLike.ofReal_inv]
  letI : Invertible (((s : NNReal) : ℝ) : 𝕜) := by
    use (((s⁻¹ : NNReal) : ℝ) : 𝕜) <;> aesop
  rw [Matrix.inv_smul]
  simp only [invOf_eq_inv, inv_one]
  simp only [det_one, isUnit_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]

theorem _root_.Matrix.PosDef.commutes_iff_rpow_commutes {𝕜 : Type*} [RCLike 𝕜]
  {n : Type _} [Fintype n] [DecidableEq n] {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝˣ) :
  (∀ x, Commute x (hQ.rpow (r : ℝ))) ↔ ∀ x, Commute x Q :=
by
  by_cases H : IsEmpty n
  . simp only [commute_iff_eq, ← Matrix.ext_iff]
    simp only [IsEmpty.forall_iff, implies_true]
  . rw [not_isEmpty_iff] at H
    simp_rw [commutes_with_all_iff]
    constructor
    . rintro ⟨α, hα⟩
      have hα' := hα
      obtain ⟨s, rfl⟩ := (RCLike.pos_toNNReal_units α).mp ((smulPosDef_isPosDef_iff posDefOne α).mp
        (by rw [← hα']; exact PosDef.rpow.isPosDef _ _))
      rw [PosDef.rpow_eq, innerAut_eq_iff, _root_.map_smul,
        innerAut_apply_one, smul_one_eq_diagonal, diagonal_eq_diagonal_iff] at hα
      simp_rw [Function.comp_apply, Pi.pow_apply] at hα
      simp only [algebraMap.coe_inj] at hα
      use ((RCLike.re (((s : NNReal) : ℝ) : 𝕜) ^ ((1 / r) : ℝ) : ℝ) : 𝕜)
      have : ∀ i, hQ.1.eigenvalues i = ((s : NNReal) : ℝ) ^ (1/r : ℝ) :=
      by
        intro i
        rw [← hα i, one_div, Real.rpow_rpow_inv (le_of_lt (PosDef.eigenvalues_pos hQ _))
          (Units.ne_zero r)]
      rw [IsHermitian.spectral_theorem'' hQ.1]
      rw [innerAut_eq_iff, _root_.map_smul, innerAut_apply_one, smul_one_eq_diagonal,
        diagonal_eq_diagonal_iff]
      simp only [Function.comp_apply, RCLike.ofReal_re, one_div, algebraMap.coe_inj]
      simp only [this, one_div, implies_true]
    . rintro ⟨α, hα⟩
      use ((RCLike.re α ^ (r : ℝ) : ℝ) : 𝕜)
      rw [PosDef.rpow_cast hQ _ hα, smul_onePosDef_rpow_eq]

theorem Module.Dual.IsPosMap.isTracial_iff
  {n : Type _} [Fintype n] [DecidableEq n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} (hφ : φ.IsPosMap) :
    φ.IsTracial ↔ ∃ α : ℂ, φ.matrix = α • 1 :=
by
  have := isTracial_pos_map_iff_of_matrix φ
  simp only [hφ, true_and] at this
  rw [this]
  constructor
  . rintro ⟨α, h⟩
    exact ⟨((α : ℝ) : ℂ), h⟩
  . rintro ⟨α, h⟩
    by_cases H : (1 : Matrix n n ℂ) = 0
    . use 0
      simp only [NNReal.coe_zero, Complex.ofReal_zero, zero_smul, h, H, smul_zero]
    . use Real.toNNReal (RCLike.re α)
      rw [h]
      congr
      have := smulPosSemidef_isPosSemidef_iff (@PosSemidef.one n _ _ _ _ _ _ _) α
      simp_rw [H, or_false, ← h, (isPosMap_iff_of_matrix _).mp hφ, true_iff] at this
      simp_rw [Real.toNNReal_of_nonneg (RCLike.nonneg_def.mp this).1]
      simp only [NNReal.coe_mk]
      exact (RCLike.nonneg_def'.mp this).1.symm

/-- `σ_k = 1` iff either `k = 0` or `φ` is tracial -/
theorem sig_eq_id_iff [hφ : φ.IsFaithfulPosMap] (k : ℝ) :
  sig hφ k = 1 ↔ k = 0 ∨ φ.IsTracial :=
by
  by_cases hk : k = 0
  . simp_rw [hk, true_or, iff_true, Module.Dual.IsFaithfulPosMap.sig_zero]
  . by_cases H : IsEmpty n
    . simp only [Module.Dual.IsTracial, Module.Dual.apply,
        trace_iff, Complex.coe_smul, AlgEquiv.ext_iff, sig_apply,
        ← Matrix.ext_iff]
      simp only [AlgEquiv.one_apply, IsEmpty.forall_iff, implies_true, Finset.univ_eq_empty,
        Finset.sum_empty, or_true]
    . rw [not_isEmpty_iff] at H
      let nk : ℝˣ := Units.mk0 k hk
      have nk2 : k = (nk : ℝ) := rfl
      simp_rw [hk, false_or, nk2]
      rw [(Module.Dual.IsPosMap.isTracial_iff hφ.1)]
      refine ⟨λ h => ?_, ?_⟩
      on_goal 2 =>
        rintro ⟨α, hα⟩
        ext1
        rw [sig_apply]
        simp_rw [PosDef.rpow_cast hφ.matrixIsPosDef _ hα]
        simp_rw [smul_onePosDef_rpow_eq]
        have := (smulPosDef_isPosDef_iff (posDefOne : PosDef (1 : Matrix n n ℂ)) α).mp
          (by rw [← hα]; exact hφ.matrixIsPosDef)
        simp_rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
          smul_smul, ← RCLike.ofReal_mul]
        rw [← Real.rpow_add (RCLike.pos_def.mp this).1, neg_add_cancel,
          Real.rpow_zero]
        simp_rw [algebraMap.coe_one, one_smul, AlgEquiv.one_apply]
      by_cases Hy : ∃ α : ℂ, hφ.matrixIsPosDef.rpow k = α • 1
      . rw [← commutes_with_all_iff,
          ← Matrix.PosDef.commutes_iff_rpow_commutes hφ.matrixIsPosDef nk, commutes_with_all_iff]
        exact Hy
      . have this1 := calc (∀ x, Commute x (hφ.matrixIsPosDef.rpow k))
          ↔ (∀ x, x * hφ.matrixIsPosDef.rpow k = hφ.matrixIsPosDef.rpow k * x) := Iff.rfl
          _ ↔ (∀ x, hφ.matrixIsPosDef.rpow (-k) * x * hφ.matrixIsPosDef.rpow k = x) := by
            haveI := (PosDef.rpow.isPosDef hφ.matrixIsPosDef k).invertible
            simp_rw [PosDef.rpow_neg_eq_inv_rpow,
              ← Matrix.inv_mul_eq_iff_eq_mul_of_invertible, mul_assoc]
          _ ↔ (∀ x, sig hφ k x = x) := Iff.rfl
          _ ↔ sig hφ k = 1 := AlgEquiv.apply_eq_id
        rw [← commutes_with_all_iff, this1] at Hy
        contradiction

theorem Module.Dual.pi_isTracial_iff {k : Type*} [Fintype k] [DecidableEq k]
  {s : k → Type*}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} :
    (Module.Dual.pi φ).IsTracial ↔ ∀ i, (φ i).IsTracial :=
by
  constructor
  . intro h i x y
    specialize h (includeBlock x) (includeBlock y)
    simp [Module.Dual.pi_apply, includeBlock_hMul_includeBlock] at h
    simpa only [← Module.Dual.pi_apply, Module.Dual.pi.apply_single_block'] using h
  . intro h x y
    simp [h _ _]

set_option synthInstance.checkSynthOrder false in
@[default_instance] noncomputable instance Matrix.isStarAlgebra [hφ : φ.IsFaithfulPosMap] :
    starAlgebra (Matrix n n ℂ) where
  modAut := sig hφ
  modAut_trans := Module.Dual.IsFaithfulPosMap.sig_trans_sig
  modAut_star r x := by
    simp_rw [sig_apply, star_mul, star_eq_conjTranspose,
      neg_neg, (Matrix.PosDef.rpow.isPosDef _ _).1.eq,
      mul_assoc]

set_option synthInstance.checkSynthOrder false in
@[instance]
noncomputable def Module.Dual.IsFaithfulPosMap.innerProductAlgebra [hφ : φ.IsFaithfulPosMap] :
    InnerProductAlgebra (Matrix n n ℂ) where
  -- norm_smul_le _ _ := by rw [← norm_smul]
  norm_sq_eq_inner := norm_sq_eq_re_inner (𝕜 := ℂ)
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
noncomputable instance PiMat.isStarAlgebra [_hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
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
  letI : starAlgebra (PiQ fun i ↦ (fun j ↦ Matrix (s j) (s j) ℂ) i) := PiMat.isStarAlgebra (_hψ := hψ)
  { k := 0
    inner_star_left := Pi.quantumSet.inner_star_left
    modAut_isSymmetric := Pi.quantumSet.modAut_isSymmetric
    inner_conj_left := Pi.quantumSet.inner_conj_left
    n := Σ i, (s i) × (s i)
    n_isFintype := by infer_instance
    n_isDecidableEq := by infer_instance
    onb := Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hψ }
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
  -- commutes' a f := by ext1; simp only [RingHom.coe_mk, MonoidHom.coe_mk, Pi.mul_apply]
  -- smul_def' a f := by ext1; simp only [Pi.smul_apply, RingHom.coe_mk, MonoidHom.coe_mk,
  --   Pi.mul_apply]

open scoped TensorProduct BigOperators Kronecker Matrix Functional

theorem LinearMap.mul'_comp_mul'_adjoint_of_delta_form {φ : Module.Dual ℂ (Matrix n n ℂ)}
    [hφ : φ.IsFaithfulPosMap] :
  LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ Coalgebra.comul = φ.matrix⁻¹.trace • 1 :=
by rw [Coalgebra.comul_eq_mul_adjoint, Qam.Nontracial.mul_comp_mul_adjoint]

theorem LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form [∀ i, Nontrivial (s i)] {δ : ℂ}
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  LinearMap.mul' ℂ (PiMat ℂ k s) ∘ₗ Coalgebra.comul = δ • 1 :=
by
  rw [Coalgebra.comul_eq_mul_adjoint, LinearMap.pi_mul'_comp_mul'_adjoint_eq_smul_id_iff δ]
  exact hφ₂

theorem Qam.Nontracial.delta_pos [Nonempty n] {φ : Module.Dual ℂ (Matrix n n ℂ)}
    [hφ : φ.IsFaithfulPosMap] : 0 < φ.matrix⁻¹.trace :=
by
  rw [Matrix.IsHermitian.trace_eq (Matrix.PosDef.inv hφ.matrixIsPosDef).1, RCLike.pos_def]
  simp only [RCLike.ofReal_im, and_true]
  rw [← Matrix.IsHermitian.trace_eq]
  exact Matrix.PosDef.pos_trace (Matrix.PosDef.inv hφ.matrixIsPosDef)

omit [Fintype k] [DecidableEq k] in
theorem Pi.Qam.Nontracial.delta_ne_zero [Nonempty k] [∀ i, Nontrivial (s i)] {δ : ℂ}
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap] (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) : 0 < δ :=
by
  let j : k := Classical.arbitrary k
  rw [← hφ₂ j]
  exact Qam.Nontracial.delta_pos

noncomputable
instance Matrix.quantumSetDeltaForm [Nonempty n] {φ : Module.Dual ℂ (Matrix n n ℂ)}
    [hφ : φ.IsFaithfulPosMap] :
    QuantumSetDeltaForm (Matrix n n ℂ) where
  delta := φ.matrix⁻¹.trace
  delta_pos := Qam.Nontracial.delta_pos
  mul_comp_comul_eq := by rw [LinearMap.mul'_comp_mul'_adjoint_of_delta_form]

set_option synthInstance.checkSynthOrder false in
noncomputable instance PiMat.quantumSetDeltaForm [Nonempty k] [∀ i, Nontrivial (s i)] {d : ℂ}
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap] [hφ₂ : Fact (∀ i, (φ i).matrix⁻¹.trace = d)] :
    QuantumSetDeltaForm (PiMat ℂ k s) where
  delta := d
  delta_pos := Pi.Qam.Nontracial.delta_ne_zero hφ₂.out
  mul_comp_comul_eq := by
    rw [LinearMap.pi_mul'_comp_mul'_adjoint_of_delta_form]
    exact hφ₂.out
