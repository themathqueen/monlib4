/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.MySpec
import Monlib.LinearAlgebra.Matrix.Basic
import Monlib.LinearAlgebra.Matrix.IsAlmostHermitian
import Monlib.LinearAlgebra.Matrix.PosEqLinearMapIsPositive
import Monlib.LinearAlgebra.TensorProduct.BasicLemmas
import Monlib.RepTheory.AutMat
import Monlib.Preq.StarAlgEquiv
-- import Mathlib.Tactic.Explode

#align_import linear_algebra.innerAut

/-!

# Inner automorphisms

This file defines the inner automorphism of a unitary matrix `U` as `U x U⁻¹` and proves that any star-algebraic automorphism on `Mₙ(ℂ)` is an inner automorphism.

-/
alias RCLike.pos_ofReal := RCLike.zero_le_real

open scoped ComplexOrder
lemma RCLike.neg_ofReal {𝕜 : Type*} [RCLike 𝕜] (a : ℝ) :
  (a : 𝕜) < 0 ↔ a < 0 :=
by
simp_rw [@RCLike.lt_def 𝕜, ofReal_re, map_zero, ofReal_im, and_true]

section

variable {n 𝕜 : Type _} [Fintype n] [Field 𝕜] [StarRing 𝕜]

@[simp]
theorem StarAlgEquiv.trace_preserving [DecidableEq n] (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜)
    (x : Matrix n n 𝕜) : (f x).trace = x.trace :=
  aut_mat_inner_trace_preserving f.toAlgEquiv x

end

def unitary.innerAutStarAlg (K : Type _) {R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (a : unitary R) : R ≃⋆ₐ[K] R :=
  by
  letI : Invertible (a : R) :=
    ⟨star (a : R), unitary.coe_star_mul_self a, unitary.coe_mul_star_self a⟩
  apply StarAlgEquiv.ofAlgEquiv (Algebra.autInner (a : R))
  intro x
  simp only [Algebra.autInner_apply, star_mul, star_star, mul_assoc,
    Invertible.invOf]

theorem unitary.innerAutStarAlg_apply {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    unitary.innerAutStarAlg K U x = U * x * (star U : unitary R) :=
  rfl

@[simp]
theorem unitary.innerAutStarAlg_apply' {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    unitary.innerAutStarAlg K U x = U * x * (U⁻¹ : unitary R) :=
  rfl

theorem unitary.innerAutStarAlg_apply'' {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    unitary.innerAutStarAlg K U x = U * x * star (U : R) :=
  rfl

theorem unitary.innerAutStarAlg_symm_apply {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    (unitary.innerAutStarAlg K U).symm x = (star U : unitary R) * x * U :=
  rfl

@[simp]
theorem unitary.innerAutStarAlg_symm_apply' {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    (unitary.innerAutStarAlg K U).symm x = (U⁻¹ : unitary R) * x * U :=
  rfl

theorem unitary.innerAutStarAlg_symm_apply'' {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    (unitary.innerAutStarAlg K U).symm x = star (U : R) * x * U :=
  rfl

theorem unitary.innerAutStarAlg_symm {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) :
    (unitary.innerAutStarAlg K U).symm = unitary.innerAutStarAlg K U⁻¹ :=
  by
  ext1
  simp only [unitary.innerAutStarAlg_symm_apply', unitary.innerAutStarAlg_apply', inv_inv]

theorem unitary.innerAutStarAlg_symm' {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) :
    (unitary.innerAutStarAlg K U).symm = unitary.innerAutStarAlg K (star U) :=
by
  ext1
  simp only [unitary.innerAutStarAlg_symm_apply, unitary.innerAutStarAlg_apply, star_star]

instance Pi.coe {k : Type _} {s r : k → Type _} [∀ i, CoeTC (s i) (r i)] :
    CoeTC (Π i, s i) (Π i, r i) :=
⟨fun U i => U i⟩

lemma Pi.coe_eq {k : Type _} {s r : k → Type _} [∀ i, CoeTC (s i) (r i)] (U : Π i, s i) :
  (fun i => ↑(U i : r i)) = CoeTC.coe U :=
rfl

theorem unitary.pi_mem {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)] [∀ i, StarMul (s i)]
  (U : Π i, unitary (s i)) :
  ↑U ∈ unitary (∀ i, s i) :=
  by
  rw [unitary.mem_iff]
  simp only [Pi.mul_def, Pi.star_apply, unitary.coe_star_mul_self]
  simp only [← unitary.coe_star, unitary.coe_mul_star_self, and_self]
  rfl

@[inline]
abbrev unitary.pi {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)] [∀ i, StarMul (s i)]
  (U : ∀ i, unitary (s i)) :
  unitary (∀ i, s i) :=
⟨↑U, unitary.pi_mem U⟩

theorem unitary.pi_apply {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)] [∀ i, StarMul (s i)]
    (U : ∀ i, unitary (s i)) {i : k} : (unitary.pi U : ∀ i, s i) i = U i :=
  rfl

namespace Matrix

variable {n 𝕜 : Type _} [Fintype n]

section
variable [Field 𝕜] [StarRing 𝕜]

@[simp]
theorem unitaryGroup.coe_hMul_star_self [DecidableEq n] (a : Matrix.unitaryGroup n 𝕜) :
    (HMul.hMul a (star a) : Matrix n n 𝕜) = (1 : Matrix n n 𝕜) :=
  by
  simp only [SetLike.coe_sort_coe, unitary.mul_star_self]
  rfl

@[simp]
theorem unitaryGroup.star_coe_eq_coe_star [DecidableEq n] (U : unitaryGroup n 𝕜) :
    (star (U : unitaryGroup n 𝕜) : Matrix n n 𝕜) = (star U : unitaryGroup n 𝕜) :=
  rfl

/-- given a unitary $U$, we have the inner algebraic automorphism, given by
  $x \mapsto UxU^*$ with its inverse given by $x \mapsto U^* x U$ -/
@[inline]
abbrev innerAutStarAlg [DecidableEq n] (a : unitaryGroup n 𝕜) : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜 :=
  unitary.innerAutStarAlg 𝕜 a

open scoped Matrix

theorem innerAutStarAlg_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAutStarAlg U x = U * x * (star U : unitaryGroup n 𝕜) :=
  rfl

theorem innerAutStarAlg_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAutStarAlg U x = U * x * (U⁻¹ : unitaryGroup n 𝕜) :=
  rfl

theorem innerAutStarAlg_symm_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAutStarAlg U).symm x = (star U : unitaryGroup n 𝕜) * x * U :=
  rfl

theorem innerAutStarAlg_symm_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAutStarAlg U).symm x = (U⁻¹ : unitaryGroup n 𝕜) * x * U :=
  rfl

@[simp]
theorem innerAutStarAlg_symm [DecidableEq n] (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).symm = innerAutStarAlg U⁻¹ :=
  unitary.innerAutStarAlg_symm U

/-- inner automorphism (`matrix.innerAut_star_alg`), but as a linear map -/
abbrev innerAut [DecidableEq n] (U : unitaryGroup n 𝕜) : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜 :=
  (innerAutStarAlg U).toLinearMap

@[simp]
theorem innerAut_coe [DecidableEq n] (U : unitaryGroup n 𝕜) : ⇑(innerAut U) = innerAutStarAlg U :=
  rfl

@[simp]
theorem innerAut_inv_coe [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(innerAut U⁻¹) = (innerAutStarAlg U).symm := by simp_rw [innerAutStarAlg_symm]; rfl

theorem innerAut_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U x = U * x * (U⁻¹ : unitaryGroup n 𝕜) :=
  rfl

theorem innerAut_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U x = U * x * (star U : unitaryGroup n 𝕜) :=
  rfl

theorem innerAut_inv_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U⁻¹ x = (U⁻¹ : unitaryGroup n 𝕜) * x * U := by simp only [innerAut_apply, inv_inv _]

theorem innerAut_star_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut (star U) x = (star U : unitaryGroup n 𝕜) * x * U := by
  simp_rw [innerAut_apply', star_star]

theorem innerAut_conjTranspose [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAut U x)ᴴ = innerAut U xᴴ :=
by simp_rw [innerAut_coe]; exact (StarAlgEquiv.map_star' _ _).symm

theorem innerAut_comp_innerAut [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜) :
    innerAut U₁ ∘ₗ innerAut U₂ = innerAut (U₁ * U₂) := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, innerAut_apply, UnitaryGroup.inv_apply,
    UnitaryGroup.mul_apply, Matrix.star_mul, Matrix.mul_assoc, forall_true_iff]

theorem innerAut_apply_innerAut [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U₁ (innerAut U₂ x) = innerAut (U₁ * U₂) x := by
  rw [← innerAut_comp_innerAut, LinearMap.comp_apply]

theorem innerAut_eq_iff [DecidableEq n] (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) :
    innerAut U x = y ↔ x = innerAut U⁻¹ y := by
  rw [innerAut_coe, innerAut_inv_coe, ← StarAlgEquiv.symm_apply_eq, StarAlgEquiv.symm_symm]

theorem unitaryGroup.toLinearEquiv_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : n → 𝕜) :
    (UnitaryGroup.toLinearEquiv U) x = (↑(U : unitaryGroup n 𝕜) : Matrix n n 𝕜).mulVec x :=
  rfl

theorem unitaryGroup.toLinearEquiv_eq [DecidableEq n] (U : unitaryGroup n 𝕜) (x : n → 𝕜) :
    (UnitaryGroup.toLinearEquiv U) x = (UnitaryGroup.toLin' U) x :=
  rfl

theorem unitaryGroup.toLin'_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : n → 𝕜) :
    (UnitaryGroup.toLin' U) x = (↑(U : unitaryGroup n 𝕜) : Matrix n n 𝕜).mulVec x :=
  rfl

theorem unitaryGroup.toLin'_eq [DecidableEq n] (U : unitaryGroup n 𝕜) (x : n → 𝕜) :
    (UnitaryGroup.toLin' U) x = (toLin' U) x :=
  rfl

theorem toLinAlgEquiv'_apply' [DecidableEq n] (x : Matrix n n 𝕜) :
  toLinAlgEquiv' x = (toLin' : (Matrix n n 𝕜 ≃ₗ[𝕜] (n → 𝕜) →ₗ[𝕜] (n → 𝕜))) x :=
rfl

/-- the spectrum of $U x U^*$ for any unitary $U$ is equal to the spectrum of $x$ -/
theorem innerAut.spectrum_eq [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    spectrum 𝕜 (toLin' (innerAut U x)) = spectrum 𝕜 (toLin' x) := by
  simp_rw [← toLinAlgEquiv'_apply', AlgEquiv.spectrum_eq, innerAut_coe,
    AlgEquiv.spectrum_eq]

theorem innerAut_one [DecidableEq n] : innerAut (1 : unitaryGroup n 𝕜) = 1 := by
  simp_rw [LinearMap.ext_iff, innerAut_apply, UnitaryGroup.inv_apply, UnitaryGroup.one_apply,
    star_one, Matrix.mul_one, Matrix.one_mul, LinearMap.one_apply,
    forall_true_iff]

theorem innerAut_comp_innerAut_inv [DecidableEq n] (U : unitaryGroup n 𝕜) :
    innerAut U ∘ₗ innerAut U⁻¹ = 1 := by
  rw [LinearMap.ext_iff]
  intro x
  rw [LinearMap.comp_apply, innerAut_coe, innerAut_inv_coe, StarAlgEquiv.apply_symm_apply]
  rfl

theorem innerAut_apply_innerAut_inv [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U₁ (innerAut U₂⁻¹ x) = innerAut (U₁ * U₂⁻¹) x := by rw [innerAut_apply_innerAut]

theorem innerAut_apply_innerAut_inv_self [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U (innerAut U⁻¹ x) = x := by
  rw [innerAut_apply_innerAut_inv, mul_inv_self, innerAut_one, LinearMap.one_apply]

theorem innerAut_inv_apply_innerAut_self [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U⁻¹ (innerAut U x) = x :=
  by
  rw [innerAut_inv_coe, innerAut_coe]
  exact StarAlgEquiv.symm_apply_apply _ _

theorem innerAut_apply_zero [DecidableEq n] (U : unitaryGroup n 𝕜) : innerAut U 0 = 0 :=
  map_zero _

/-- the spectrum of a linear map $x$ equals the spectrum of
  $f_U^{-1} x f_U$ for some unitary $U$ and $f_U$ is
  the inner automorphism (`matrix.innerAut`) -/
theorem innerAut_conj_spectrum_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    spectrum 𝕜 (innerAut U⁻¹ ∘ₗ x ∘ₗ innerAut U) = spectrum 𝕜 x := by
  rw [spectrum.comm, LinearMap.comp_assoc, innerAut_comp_innerAut_inv, LinearMap.comp_one]

/-- the inner automorphism is unital -/
theorem innerAut_apply_one [DecidableEq n] (U : unitaryGroup n 𝕜) : innerAut U 1 = 1 :=
by rw [innerAut_coe, _root_.map_one]

theorem innerAutStarAlg_apply_eq_innerAut_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) : innerAutStarAlg U x = innerAut U x :=
  rfl

theorem innerAut.map_mul [DecidableEq n] (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) :
    innerAut U (x * y) = innerAut U x * innerAut U y :=
by rw [innerAut_coe, _root_.map_mul (innerAutStarAlg U)]

theorem innerAut.map_star [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    star (innerAut U x) = innerAut U (star x) :=
  innerAut_conjTranspose _ _

theorem innerAut_inv_eq_star [DecidableEq n] {x : unitaryGroup n 𝕜} :
    innerAut x⁻¹ = innerAut (star x) :=
  rfl

theorem unitaryGroup.coe_inv [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(U⁻¹ : unitaryGroup n 𝕜) = ((U : Matrix n n 𝕜)⁻¹ : Matrix n n 𝕜) :=
  by
  symm
  apply inv_eq_left_inv
  simp_rw [UnitaryGroup.inv_apply, UnitaryGroup.star_mul_self]

theorem innerAut.map_inv [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAut U x)⁻¹ = innerAut U x⁻¹ := by
  simp_rw [innerAut_apply, Matrix.mul_inv_rev, ← unitaryGroup.coe_inv, inv_inv, Matrix.mul_assoc]

/-- the trace of $f_U(x)$ is equal to the trace of $x$ -/
theorem innerAut_apply_trace_eq [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
  (innerAut U x).trace = x.trace :=
by rw [innerAut_coe, StarAlgEquiv.trace_preserving]

variable [DecidableEq n]

theorem exists_innerAut_iff_exists_innerAut_inv {P : Matrix n n 𝕜 → Prop} (x : Matrix n n 𝕜) :
    (∃ U : unitaryGroup n 𝕜, P (innerAut U x)) ↔ ∃ U : unitaryGroup n 𝕜, P (innerAut U⁻¹ x) :=
  by
  constructor <;> rintro ⟨U, hU⟩ <;> use U⁻¹
  simp_rw [inv_inv]
  exact hU

theorem innerAut.is_injective (U : unitaryGroup n 𝕜) : Function.Injective (innerAut U) :=
  by
  intro u v huv
  rw [← innerAut_inv_apply_innerAut_self U u, huv, innerAut_inv_apply_innerAut_self]

/-- $x$ is Hermitian if and only if $f_U(x)$ is Hermitian -/
theorem innerAut_isHermitian_iff (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    x.IsHermitian ↔ (innerAut U x).IsHermitian := by
  simp_rw [IsHermitian, innerAut_conjTranspose,
    Function.Injective.eq_iff (innerAut.is_injective U)]

end

variable [RCLike 𝕜] [DecidableEq n]
open scoped ComplexOrder

theorem innerAut_posSemidef_iff (U : unitaryGroup n 𝕜) {a : Matrix n n 𝕜} :
    (innerAut U a).PosSemidef ↔ a.PosSemidef :=
  by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (posSemidef_iff _).mp h
    rw [innerAut_eq_iff, innerAut.map_mul, ← innerAut_conjTranspose] at hy
    rw [hy]
    exact posSemidef_star_mul_self _
  · intro h
    obtain ⟨y, hy⟩ := (posSemidef_iff _).mp h
    rw [hy, innerAut.map_mul, ← innerAut_conjTranspose]
    exact posSemidef_star_mul_self _

theorem PosSemidef.innerAut {a : Matrix n n 𝕜}
  (ha : PosSemidef a) (U : unitaryGroup n 𝕜) :
  PosSemidef (innerAut U a) :=
(innerAut_posSemidef_iff U).mpr ha

lemma unitaryGroup_conjTranspose (U : unitaryGroup n 𝕜) :
  (↑U)ᴴ = (↑(U⁻¹ : unitaryGroup n 𝕜) : Matrix n n 𝕜) :=
rfl

/-- $f_U(x)$ is positive definite if and only if $x$ is positive definite -/
theorem innerAut_posDef_iff (U : unitaryGroup n 𝕜) {x : Matrix n n 𝕜} :
    (innerAut U x).PosDef ↔ x.PosDef :=
  by
  let D := innerAut U x
  have hD : innerAut U x = D := rfl
  have hD' := hD
  rw [innerAut_eq_iff] at hD'
  rw [hD', innerAut_inv_apply_innerAut_self]
  simp_rw [PosDef, ← innerAut_isHermitian_iff U]
  have ugh' : ∀ (hi : unitaryGroup n 𝕜) (u : n → 𝕜), mulVec (hi : Matrix n n 𝕜) u ≠ 0 ↔ u ≠ 0 :=
    by
    intro hi u
    rw [ne_eq, ← toLin'_apply, ← unitaryGroup.toLin'_eq, ← unitaryGroup.toLinearEquiv_eq,
      (injective_iff_map_eq_zero' _).mp (LinearEquiv.injective (UnitaryGroup.toLinearEquiv hi))]
  refine' ⟨fun ⟨h1, h2⟩ => ⟨h1, fun u hu => ?_⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun u hu => ?_⟩⟩
  .
    specialize h2 (U *ᵥ u) ((ugh' U _).mpr hu)
    simp_rw [mulVec_mulVec, innerAut_apply, UnitaryGroup.inv_apply,
      mul_assoc, UnitaryGroup.star_mul_self, mul_one, star_mulVec,
      dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose,
      ← mul_assoc, UnitaryGroup.star_mul_self, one_mul,
      ← dotProduct_mulVec] at h2
    exact h2
  . specialize h2 ((U⁻¹ : unitaryGroup n 𝕜) *ᵥ u) ((ugh' U⁻¹ _).mpr hu)
    simp_rw [star_mulVec, unitaryGroup_conjTranspose, inv_inv,
      mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← mul_assoc,
      ← innerAut_apply] at h2
    exact h2

theorem PosDef.innerAut {a : Matrix n n 𝕜}
  (ha : PosDef a) (U : unitaryGroup n 𝕜) :
  PosDef (innerAut U a) :=
(innerAut_posDef_iff U).mpr ha

/-- Schur decomposition, but only for almost Hermitian matrices:
  given an almost Hermitian matrix $A$, there exists a diagonal matrix $D$ and
  a unitary matrix $U$ such that $UDU^*=A$ -/
theorem IsAlmostHermitian.schur_decomp {𝕜 : Type _} [RCLike 𝕜] [DecidableEq 𝕜] {A : Matrix n n 𝕜}
    (hA : A.IsAlmostHermitian) :
    ∃ (D : n → 𝕜) (U : unitaryGroup n 𝕜), innerAut U (diagonal D) = A :=
  by
  rcases hA with ⟨α, B, ⟨rfl, hB⟩⟩
  use α • RCLike.ofReal ∘ hB.eigenvalues, hB.eigenvectorUnitary
  simp_rw [diagonal_smul, _root_.map_smul, innerAut_apply,
    UnitaryGroup.inv_apply]
  rw [← IsHermitian.spectral_theorem]

lemma _root_.toEuclideanLin_one :
  toEuclideanLin (1 : Matrix n n 𝕜) = 1 :=
by simp_rw [toEuclideanLin_eq_piLp_linearEquiv, toLin'_one]; rfl

open scoped  BigOperators
/-- any $^*$-isomorphism on $M_n$ is an inner automorphism -/
theorem _root_.StarAlgEquiv.of_matrix_is_inner
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) : ∃ U : unitaryGroup n 𝕜, innerAutStarAlg U = f :=
  by
  by_cases h : IsEmpty n
  · haveI := h
    use 1
    ext a
    have : a = 0 := by simp only [eq_iff_true_of_subsingleton]
    simp_rw [this, map_zero]
  rw [not_isEmpty_iff] at h
  haveI := h
  let f' := f.toAlgEquiv
  obtain ⟨y', hy⟩ := aut_mat_inner f'
  let y := LinearMap.toMatrix' (y'.toLinearMap)
  let yinv := LinearMap.toMatrix' y'.symm.toLinearMap
  have Hy : y * yinv = 1 ∧ yinv * y = 1 := by
    simp_rw [y, yinv, ← LinearMap.toMatrix'_comp,
      LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id, and_self_iff]
  have H : y⁻¹ = yinv := inv_eq_left_inv Hy.2
  have hf' : ∀ x : Matrix n n 𝕜, f' x = y * x * y⁻¹ :=
    by
    intro x
    simp_rw [hy, Algebra.autInner_apply, H]
    rfl
  have hf : ∀ x : Matrix n n 𝕜, f x = y * x * y⁻¹ :=
    by
    intro x
    rw [← hf']
    rfl
  have : ∀ x : Matrix n n 𝕜, (f x)ᴴ = f xᴴ := fun _ => (StarAlgEquiv.map_star' _ _).symm
  simp_rw [hf, conjTranspose_mul, conjTranspose_nonsing_inv] at this
  have this3 : ∀ x : Matrix n n 𝕜, yᴴ * y * xᴴ * y⁻¹ = xᴴ * yᴴ :=
    by
    intro x
    simp_rw [Matrix.mul_assoc, ← Matrix.mul_assoc y, ← this, ← Matrix.mul_assoc, ←
      conjTranspose_nonsing_inv, ← conjTranspose_mul, H, Hy.2, Matrix.mul_one]
  have this2 : ∀ x : Matrix n n 𝕜, Commute xᴴ (yᴴ * y) :=
    by
    intro x
    simp_rw [Commute, SemiconjBy, ← Matrix.mul_assoc, ← this3, Matrix.mul_assoc, H,
      Hy.2, Matrix.mul_one]
  have this4 : ∀ x : Matrix n n 𝕜, Commute x (yᴴ * y) :=
    by
    intro x
    specialize this2 xᴴ
    simp_rw [conjTranspose_conjTranspose] at this2
    exact this2
  obtain ⟨α, hα⟩ := commutes_with_all_iff.mp this4
  -- have this6 : toEuclideanLin (1 : Matrix n n 𝕜) = 1 := toEuclideanLin_one
  have this7 : Function.Bijective (toLin' (yᴴ * y)) :=
    by
    rw [Function.bijective_iff_has_inverse]
    use toLin' (y⁻¹ * y⁻¹ᴴ)
    simp_rw [Function.LeftInverse, Function.RightInverse, Function.LeftInverse, ← toLin'_mul_apply,
      Matrix.mul_assoc, ← Matrix.mul_assoc y⁻¹ᴴ, ← conjTranspose_mul, H, ← Matrix.mul_assoc y]
    simp only [Hy.2, Hy.1, conjTranspose_one, Matrix.mul_one, Matrix.one_mul, toLin'_one,
      LinearMap.id_apply, eq_self_iff_true, forall_true_iff]
    simp_rw [← conjTranspose_mul, Hy.2, conjTranspose_one, toLin'_one, LinearMap.id_apply,
      forall_true_iff, true_and_iff]
  have this8 : (yᴴ * y).PosSemidef := posSemidef_star_mul_self _
  have this9 := (PosSemidef.invertible_iff_posDef this8).mp this7
  have this12 : (1 : n → 𝕜) ≠ 0 :=
    by
    simp_rw [ne_eq, Function.funext_iff, Pi.one_apply, Pi.zero_apply, one_ne_zero]
    simp only [Classical.not_forall, not_false_iff, exists_const]
  have this10 : α = RCLike.re α :=
    by
    have this10 := IsHermitian.coe_re_diag this8.1
    simp_rw [hα, diag_smul, diag_one, Pi.smul_apply, Pi.one_apply, Algebra.id.smul_eq_mul,
      mul_one] at this10
    have this11 : (RCLike.re α : 𝕜) • (1 : n → 𝕜) = α • 1 :=
      by
      rw [← this10]
      ext1
      simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [(smul_left_injective _ this12).eq_iff] at this11
    rw [this11]
  have this13 : star (1 : n → 𝕜) ⬝ᵥ (1 : n → 𝕜) = (Fintype.card n : ℝ) :=
    by
    simp only [dotProduct, Pi.star_apply, Pi.one_apply, star_one, one_mul, Finset.sum_const]
    simp only [Nat.smul_one_eq_cast, Nat.cast_inj,
      RCLike.ofReal_natCast]
    rfl
  simp_rw [hα, PosDef, smul_mulVec_assoc, dotProduct_smul, one_mulVec, smul_eq_mul] at this9
  cases' this9 with this9l this9
  specialize this9 1 this12
  rw [this10, this13, ← RCLike.ofReal_mul, RCLike.zero_lt_real,
    mul_pos_iff] at this9
  simp only [Nat.cast_pos, Fintype.card_pos] at this9
  have this14 : ¬(Fintype.card n : ℝ) < 0 := by simp only [not_lt, Nat.cast_nonneg]
  simp_rw [this14, and_false_iff, and_true_iff, or_false_iff] at this9
  have fin : (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y ∈ unitaryGroup n 𝕜 :=
    by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    simp_rw [conjTranspose_smul, RCLike.star_def, Matrix.smul_mul, Matrix.mul_smul,
      RCLike.conj_ofReal, smul_smul, ← RCLike.ofReal_mul]
    rw [← Real.rpow_add this9, hα, this10, smul_smul, ← RCLike.ofReal_mul, RCLike.ofReal_re, ←
      Real.rpow_add_one (NeZero.of_pos this9).out]
    norm_num
  let U : unitaryGroup n 𝕜 := ⟨_, fin⟩
  have hU : (U : Matrix n n 𝕜) = (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y := rfl
  have hU2 : ((((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y)⁻¹ = ((U⁻¹ : _) : Matrix n n 𝕜) :=
    by
    apply inv_eq_left_inv
    rw [← hU, UnitaryGroup.inv_apply, UnitaryGroup.star_mul_self]
  have hU3 :
    ((((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y)⁻¹ =
      (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜)⁻¹ • y⁻¹ :=
    by
    apply inv_eq_left_inv
    simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [inv_mul_cancel, one_smul, H, Hy.2]
    · simp_rw [ne_eq, RCLike.ofReal_eq_zero, Real.rpow_eq_zero_iff_of_nonneg (le_of_lt this9),
        (NeZero.of_pos this9).out, false_and_iff]
      exact not_false
  use U
  ext1 x
  simp_rw [innerAutStarAlg_apply_eq_innerAut_apply, innerAut_apply, ← hU2, hU3, hf,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← RCLike.ofReal_inv, ← RCLike.ofReal_mul, ←
    Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt this9), ← Real.rpow_add this9]
  norm_num

noncomputable def _root_.StarAlgEquiv.of_matrix_unitary
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) : unitaryGroup n 𝕜 :=
  by
  choose U _ using f.of_matrix_is_inner
  exact U

lemma _root_.StarAlgEquiv.eq_innerAut (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) :
    innerAutStarAlg f.of_matrix_unitary = f :=
StarAlgEquiv.of_matrix_unitary.proof_1 _

theorem IsHermitian.spectral_theorem'' {𝕜 : Type _} [RCLike 𝕜] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    x = innerAut hx.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hx.eigenvalues)) :=
  by
  rw [innerAut_apply, UnitaryGroup.inv_apply, Matrix.unitaryGroup.coe_mk]
  simp_rw [← IsHermitian.spectral_theorem hx]

theorem coe_diagonal_eq_diagonal_coe {n 𝕜 : Type _} [RCLike 𝕜] [DecidableEq n] (x : n → ℝ) :
    (diagonal (RCLike.ofReal ∘ x) : Matrix n n 𝕜) = CoeTC.coe ∘ diagonal x :=
  by
  simp only [← Matrix.ext_iff, diagonal, Function.comp_apply,
    CoeTC.coe, of_apply, coe_ite]
  intro i j
  split_ifs
  . rfl
  . simp only [algebraMap.coe_zero]

theorem diagonal.spectrum {𝕜 n : Type _} [Field 𝕜] [Fintype n] [DecidableEq n] (A : n → 𝕜) :
    spectrum 𝕜 (toLin' (diagonal A : Matrix n n 𝕜)) = {x : 𝕜 | ∃ i : n, A i = x} :=
  by
  simp_rw [Set.ext_iff, ← Module.End.hasEigenvalue_iff_mem_spectrum, ←
    Module.End.has_eigenvector_iff_hasEigenvalue, toLin'_apply, Function.funext_iff, mulVec,
    diagonal_dotProduct, Pi.smul_apply, Algebra.id.smul_eq_mul, mul_eq_mul_right_iff, ne_eq,
    Set.mem_setOf_eq, Function.funext_iff, Pi.zero_apply, Classical.not_forall]
  intro x
  constructor
  · rintro ⟨v, ⟨h, ⟨j, hj⟩⟩⟩
    specialize h j
    rcases h with (h | h)
    · exact ⟨j, h⟩
    · contradiction
  · rintro ⟨i, hi⟩
    let v : n → 𝕜 := fun j => ite (j = i) 1 0
    use v
    simp_rw [v, ite_eq_right_iff, one_ne_zero, imp_false, Classical.not_not]
    constructor
    · intro j
      by_cases h : j = i
      · left
        rw [h, hi]
      · right
        exact h
    · use i

theorem IsHermitian.spectrum {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) : spectrum 𝕜 (toLin' x) = {x : 𝕜 | ∃ i : n, (hx.eigenvalues i : 𝕜) = x} :=
  by
  nth_rw 1 [Matrix.IsHermitian.spectral_theorem'' hx]
  simp_rw [innerAut.spectrum_eq, diagonal.spectrum]
  rfl

theorem IsHermitian.hasEigenvalue_iff {𝕜 : Type _} [RCLike 𝕜] [DecidableEq 𝕜] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) (α : 𝕜) :
    Module.End.HasEigenvalue (toLin' x) α ↔ ∃ i, (hx.eigenvalues i : 𝕜) = α := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, hx.spectrum, Set.mem_setOf]

-- MOVE:
theorem innerAut_commutes_with_map_lid_symm (U : Matrix.unitaryGroup n 𝕜) :
    TensorProduct.map 1 (innerAut U) ∘ₗ (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).symm.toLinearMap =
      (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).symm.toLinearMap ∘ₗ innerAut U :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_symm_apply, TensorProduct.map_tmul, LinearMap.one_apply,
    forall_const]

-- MOVE:
theorem innerAut_commutes_with_lid_comm (U : Matrix.unitaryGroup n 𝕜) :
    (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).toLinearMap ∘ₗ
        (TensorProduct.comm 𝕜 (Matrix n n 𝕜) 𝕜).toLinearMap ∘ₗ TensorProduct.map (innerAut U) 1 =
      innerAut U ∘ₗ
        (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).toLinearMap ∘ₗ
          (TensorProduct.comm 𝕜 (Matrix n n 𝕜) 𝕜).toLinearMap :=
  by
  simp_rw [TensorProduct.ext_iff, LinearMap.comp_apply, TensorProduct.map_apply,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    TensorProduct.lid_tmul, LinearMap.one_apply, _root_.map_smul,
    forall₂_true_iff]

theorem unitaryGroup.conj_mem {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) : (U : Matrix n n 𝕜)ᴴᵀ ∈ unitaryGroup n 𝕜 :=
  by
  rw [mem_unitaryGroup_iff']
  calc
    star (U : Matrix n n 𝕜)ᴴᵀ * (U : Matrix n n 𝕜)ᴴᵀ = (U : _)ᴴᵀᴴ * (U : _)ᴴᵀ := rfl
    _ = ((U : Matrix n n 𝕜)ᴴ * (U : Matrix n n 𝕜))ᴴᵀ :=
    by simp_rw [Matrix.conj_mul]; rfl
    _ = 1ᴴᵀ := by rw [← star_eq_conjTranspose, UnitaryGroup.star_mul_self]
    _ = 1 := Matrix.conj_one

def unitaryGroup.conj {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] (U : unitaryGroup n 𝕜) :
    unitaryGroup n 𝕜 :=
  ⟨(U : _)ᴴᵀ, unitaryGroup.conj_mem U⟩

@[norm_cast]
theorem unitaryGroup.conj_coe {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) : (unitaryGroup.conj U : Matrix n n 𝕜) = Uᴴᵀ :=
  rfl

theorem innerAut.conj {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) : (innerAut U x)ᴴᵀ = innerAut (unitaryGroup.conj U) xᴴᵀ :=
  by
  simp_rw [innerAut_apply, Matrix.conj_mul, UnitaryGroup.inv_apply, unitaryGroup.conj_coe]
  rfl

theorem UnitaryGroup.mul_star_self {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) : U * star (U : Matrix n n 𝕜) = 1 :=
mem_unitaryGroup_iff.mp (SetLike.coe_mem U)

open scoped Kronecker

theorem kronecker_mem_unitaryGroup {p : Type _} [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜)
    (U₂ : unitaryGroup p 𝕜) : U₁ ⊗ₖ U₂ ∈ unitaryGroup (n × p) 𝕜 := by
  simp_rw [mem_unitaryGroup_iff, star_eq_conjTranspose, kronecker_conjTranspose, ←
    mul_kronecker_mul, ← star_eq_conjTranspose, UnitaryGroup.mul_star_self, one_kronecker_one]

def unitaryGroup.kronecker {p : Type _} [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜)
    (U₂ : unitaryGroup p 𝕜) : unitaryGroup (n × p) 𝕜 :=
by
  refine ⟨U₁ ⊗ₖ U₂, ?_⟩
  exact kronecker_mem_unitaryGroup U₁ U₂

theorem unitaryGroup.kronecker_coe {p : Type _} [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜)
    (U₂ : unitaryGroup p 𝕜) : (unitaryGroup.kronecker U₁ U₂ : Matrix (n × p) (n × p) 𝕜) = U₁ ⊗ₖ U₂ :=
  rfl

theorem innerAut_kronecker {p : Type _} [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜)
    (U₂ : unitaryGroup p 𝕜) (x : Matrix n n 𝕜) (y : Matrix p p 𝕜) :
    innerAut U₁ x ⊗ₖ innerAut U₂ y = innerAut (unitaryGroup.kronecker U₁ U₂) (x ⊗ₖ y) := by
  simp_rw [innerAut_apply, UnitaryGroup.inv_apply, unitaryGroup.kronecker_coe,
    star_eq_conjTranspose, kronecker_conjTranspose, ← mul_kronecker_mul]

theorem PosSemidef.kronecker {n p : Type _} [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] {x : Matrix n n 𝕜} {y : Matrix p p 𝕜} (hx : x.PosSemidef)
    (hy : y.PosSemidef) : (x ⊗ₖ y).PosSemidef :=
  by
  rw [Matrix.IsHermitian.spectral_theorem'' hx.1, Matrix.IsHermitian.spectral_theorem'' hy.1,
    innerAut_kronecker, diagonal_kronecker_diagonal, innerAut_posSemidef_iff,
    PosSemidef.diagonal]
  simp_rw [Function.comp_apply, ← RCLike.ofReal_mul, RCLike.pos_ofReal,
    mul_nonneg (IsHermitian.nonneg_eigenvalues_of_posSemidef hx _)
      (IsHermitian.nonneg_eigenvalues_of_posSemidef hy _),
    forall_true_iff]

theorem PosDef.kronecker {𝕜 n p : Type _} [RCLike 𝕜] [DecidableEq 𝕜] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] {x : Matrix n n 𝕜} {y : Matrix p p 𝕜} (hx : x.PosDef)
    (hy : y.PosDef) : (x ⊗ₖ y).PosDef :=
  by
  rw [Matrix.IsHermitian.spectral_theorem'' hx.1, Matrix.IsHermitian.spectral_theorem'' hy.1,
    innerAut_kronecker, innerAut_posDef_iff, diagonal_kronecker_diagonal, PosDef.diagonal]
  simp_rw [Function.comp_apply, ← RCLike.ofReal_mul,
    @RCLike.zero_lt_real 𝕜, mul_pos (hx.pos_eigenvalues _) (hy.pos_eigenvalues _), forall_true_iff]

theorem unitaryGroup.injective_hMul {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) : x = y ↔ x * U = y * U :=
  by
  refine' ⟨fun h => by rw [h], fun h => _⟩
  nth_rw 1 [← Matrix.mul_one y]
  rw [← UnitaryGroup.mul_star_self U, ← Matrix.mul_assoc, ← h, Matrix.mul_assoc,
    UnitaryGroup.mul_star_self, Matrix.mul_one]

theorem innerAutStarAlg_equiv_toLinearMap {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    [DecidableEq 𝕜] (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).toLinearMap = innerAut U :=
  rfl

theorem innerAutStarAlg_equiv_symm_toLinearMap {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (U : unitaryGroup n 𝕜) : (innerAutStarAlg U).symm.toLinearMap = innerAut U⁻¹ :=
  by
  ext1
  simp only [innerAutStarAlg_symm_apply, innerAut_apply, inv_inv]
  rw [UnitaryGroup.inv_apply]
  rfl

theorem innerAut.comp_inj {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (U : Matrix.unitaryGroup n 𝕜) (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ innerAut U ∘ₗ S = innerAut U ∘ₗ T := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, innerAut_eq_iff,
    innerAut_inv_apply_innerAut_self]

theorem innerAut.inj_comp {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (U : unitaryGroup n 𝕜) (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ S ∘ₗ innerAut U = T ∘ₗ innerAut U :=
  by
  refine' ⟨fun h => by rw [h], fun h => _⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply] at h ⊢
  intro x
  nth_rw 1 [← innerAut_apply_innerAut_inv_self U x]
  rw [h, innerAut_apply_innerAut_inv_self]

end Matrix
