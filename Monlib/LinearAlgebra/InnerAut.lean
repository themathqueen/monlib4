/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MySpec
import LinearAlgebra.MyMatrix.Basic
import LinearAlgebra.MyMatrix.IsAlmostHermitian
import LinearAlgebra.MyMatrix.PosEqLinearMapIsPositive
import LinearAlgebra.Matrix.PosDef
import LinearAlgebra.MyTensorProduct
import RepTheory.AutMat
import Preq.StarAlgEquiv

#align_import linear_algebra.inner_aut

/-!

# Inner automorphisms

This file defines the inner automorphism of a unitary matrix `U` as `U x U⁻¹` and proves that any star-algebraic automorphism on `Mₙ(ℂ)` is an inner automorphism.

-/


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
  simp only [Algebra.autInner_apply, star_mul, star_star, mul_assoc]

theorem unitary.innerAutStarAlg_apply {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    unitary.innerAutStarAlg K U x = U * x * (star U : unitary R) :=
  rfl

theorem unitary.innerAutStarAlg_apply' {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    unitary.innerAutStarAlg K U x = U * x * (U⁻¹ : unitary R) :=
  rfl

theorem unitary.innerAutStarAlg_symm_apply {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    (unitary.innerAutStarAlg K U).symm x = (star U : unitary R) * x * U :=
  rfl

theorem unitary.innerAutStarAlg_symm_apply' {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) (x : R) :
    (unitary.innerAutStarAlg K U).symm x = (U⁻¹ : unitary R) * x * U :=
  rfl

theorem unitary.innerAutStarAlg_symm {K R : Type _} [CommSemiring K] [Semiring R] [StarMul R]
    [Algebra K R] (U : unitary R) :
    (unitary.innerAutStarAlg K U).symm = unitary.innerAutStarAlg K U⁻¹ :=
  by
  ext1
  simp only [unitary.innerAutStarAlg_symm_apply', unitary.innerAutStarAlg_apply', inv_inv]

theorem unitary.pi_coe {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)] [∀ i, StarMul (s i)]
    (U : ∀ i, unitary (s i)) : (fun i => ↑(U i) : ∀ i, s i) = ↑U :=
  rfl

theorem unitary.pi_mem {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)] [∀ i, StarMul (s i)]
    (U : ∀ i, unitary (s i)) : ↑U ∈ @unitary (∀ i, s i) _ (@Pi.starSemigroup k s _ _inst_2) :=
  by
  rw [← unitary.pi_coe U, unitary.mem_iff]
  simp only [Function.funext_iff, Pi.mul_apply, Pi.star_apply, Pi.one_apply,
    unitary.coe_star_mul_self, unitary.coe_mul_star_self, eq_self_iff_true, and_self_iff,
    imp_true_iff]

def unitary.pi {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)] [∀ i, StarMul (s i)]
    (U : ∀ i, unitary (s i)) : @unitary (∀ i, s i) _ (@Pi.starSemigroup k s _ _inst_2) :=
  ⟨↑U, unitary.pi_mem U⟩

theorem unitary.pi_apply {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)] [∀ i, StarMul (s i)]
    (U : ∀ i, unitary (s i)) {i : k} : (unitary.pi U : ∀ i, s i) i = U i :=
  rfl

namespace Matrix

variable {n 𝕜 : Type _} [Fintype n] [Field 𝕜] [StarRing 𝕜]

@[simp]
theorem unitaryGroup.hMul_star_self [DecidableEq n] (a : Matrix.unitaryGroup n 𝕜) :
    (HMul.hMul a (star a) : Matrix n n 𝕜) = (1 : Matrix n n 𝕜) :=
  by
  rw [← Matrix.hMul_eq_hMul, unitary.mul_star_self_of_mem _]
  exact SetLike.coe_mem a

@[simp]
theorem unitaryGroup.star_coe_eq_coe_star [DecidableEq n] (U : unitaryGroup n 𝕜) :
    (star (U : unitaryGroup n 𝕜) : Matrix n n 𝕜) = (star U : unitaryGroup n 𝕜) :=
  rfl

/-- given a unitary $U$, we have the inner algebraic automorphism, given by
  $x \mapsto UxU^*$ with its inverse given by $x \mapsto U^* x U$ -/
def innerAutStarAlg [DecidableEq n] (a : unitaryGroup n 𝕜) : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜 :=
  unitary.innerAutStarAlg 𝕜 a

open scoped Matrix

theorem innerAutStarAlg_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAutStarAlg U x = U ⬝ x ⬝ (star U : unitaryGroup n 𝕜) :=
  rfl

theorem innerAutStarAlg_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAutStarAlg U x = U ⬝ x ⬝ (U⁻¹ : unitaryGroup n 𝕜) :=
  rfl

theorem innerAutStarAlg_symm_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAutStarAlg U).symm x = (star U : unitaryGroup n 𝕜) ⬝ x ⬝ U :=
  rfl

theorem innerAutStarAlg_symm_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAutStarAlg U).symm x = (U⁻¹ : unitaryGroup n 𝕜) ⬝ x ⬝ U :=
  rfl

@[simp]
theorem innerAutStarAlg_symm [DecidableEq n] (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).symm = innerAutStarAlg U⁻¹ :=
  unitary.innerAutStarAlg_symm U

/-- inner automorphism (`matrix.inner_aut_star_alg`), but as a linear map -/
def innerAut [DecidableEq n] (U : unitaryGroup n 𝕜) : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜 :=
  (innerAutStarAlg U).toAlgEquiv.toLinearMap

@[simp]
theorem innerAut_coe [DecidableEq n] (U : unitaryGroup n 𝕜) : ⇑(innerAut U) = innerAutStarAlg U :=
  rfl

@[simp]
theorem innerAut_inv_coe [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(innerAut U⁻¹) = (innerAutStarAlg U).symm := by simp_rw [inner_aut_star_alg_symm] <;> rfl

theorem innerAut_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U x = U ⬝ x ⬝ (U⁻¹ : unitaryGroup n 𝕜) :=
  rfl

theorem innerAut_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U x = U ⬝ x ⬝ (star U : unitaryGroup n 𝕜) :=
  rfl

theorem innerAut_inv_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U⁻¹ x = (U⁻¹ : unitaryGroup n 𝕜) ⬝ x ⬝ U := by simp only [inner_aut_apply, inv_inv _]

theorem innerAut_star_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut (star U) x = (star U : unitaryGroup n 𝕜) ⬝ x ⬝ U := by
  simp_rw [inner_aut_apply', star_star]

theorem innerAut_conjTranspose [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAut U x)ᴴ = innerAut U xᴴ :=
  (StarAlgEquiv.map_star' _ _).symm

theorem innerAut_comp_innerAut [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜) :
    innerAut U₁ ∘ₗ innerAut U₂ = innerAut (U₁ * U₂) := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, inner_aut_apply, unitary_group.inv_apply,
    unitary_group.mul_apply, Matrix.star_mul, Matrix.mul_assoc, eq_self_iff_true, forall_true_iff]

theorem innerAut_apply_innerAut [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U₁ (innerAut U₂ x) = innerAut (U₁ * U₂) x := by
  rw [← inner_aut_comp_inner_aut _ _, LinearMap.comp_apply]

theorem innerAut_eq_iff [DecidableEq n] (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) :
    innerAut U x = y ↔ x = innerAut U⁻¹ y := by
  rw [inner_aut_coe, inner_aut_inv_coe, ← StarAlgEquiv.symm_apply_eq, StarAlgEquiv.symm_symm]

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

/-- the spectrum of $U x U^*$ for any unitary $U$ is equal to the spectrum of $x$ -/
theorem innerAut.spectrum_eq [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    spectrum 𝕜 (innerAut U x).toLin' = spectrum 𝕜 x.toLin' := by
  rw [inner_aut_apply, to_lin'_mul, spectrum.comm, ← to_lin'_mul, ← Matrix.mul_assoc,
    unitary_group.inv_apply, unitary_group.star_mul_self, Matrix.one_mul]

theorem innerAut_one [DecidableEq n] : innerAut (1 : unitaryGroup n 𝕜) = 1 := by
  simp_rw [LinearMap.ext_iff, inner_aut_apply, unitary_group.inv_apply, unitary_group.one_apply,
    star_one, Matrix.mul_one, Matrix.one_mul, LinearMap.one_apply, eq_self_iff_true,
    forall_true_iff]

theorem innerAut_comp_innerAut_inv [DecidableEq n] (U : unitaryGroup n 𝕜) :
    innerAut U ∘ₗ innerAut U⁻¹ = 1 := by
  rw [LinearMap.ext_iff]
  intro x
  rw [LinearMap.comp_apply, inner_aut_coe, inner_aut_inv_coe, StarAlgEquiv.apply_symm_apply]
  rfl

theorem innerAut_apply_innerAut_inv [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U₁ (innerAut U₂⁻¹ x) = innerAut (U₁ * U₂⁻¹) x := by rw [inner_aut_apply_inner_aut]

theorem innerAut_apply_innerAut_inv_self [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U (innerAut U⁻¹ x) = x := by
  rw [inner_aut_apply_inner_aut_inv, mul_inv_self, inner_aut_one, LinearMap.one_apply]

theorem innerAut_inv_apply_innerAut_self [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U⁻¹ (innerAut U x) = x :=
  by
  rw [inner_aut_inv_coe, inner_aut_coe]
  exact StarAlgEquiv.symm_apply_apply _ _

theorem innerAut_apply_zero [DecidableEq n] (U : unitaryGroup n 𝕜) : innerAut U 0 = 0 :=
  map_zero _

/-- the spectrum of a linear map $x$ equals the spectrum of
  $f_U^{-1} x f_U$ for some unitary $U$ and $f_U$ is
  the inner automorphism (`matrix.inner_aut`) -/
theorem innerAut_conj_spectrum_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    spectrum 𝕜 (innerAut U⁻¹ ∘ₗ x ∘ₗ innerAut U) = spectrum 𝕜 x := by
  rw [spectrum.comm, LinearMap.comp_assoc, inner_aut_comp_inner_aut_inv, LinearMap.comp_one]

/-- the inner automorphism is unital -/
theorem innerAut_apply_one [DecidableEq n] (U : unitaryGroup n 𝕜) : innerAut U 1 = 1 :=
  map_one (innerAutStarAlg U)

theorem innerAutStarAlg_apply_eq_innerAut_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) : innerAutStarAlg U x = innerAut U x :=
  rfl

theorem innerAut.map_hMul [DecidableEq n] (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) :
    innerAut U (x ⬝ y) = innerAut U x ⬝ innerAut U y :=
  map_mul (innerAutStarAlg U) _ _

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
  simp_rw [unitary_group.inv_apply, unitary_group.star_mul_self]

theorem innerAut.map_inv [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAut U x)⁻¹ = innerAut U x⁻¹ := by
  simp_rw [inner_aut_apply, Matrix.mul_inv_rev, ← unitary_group.coe_inv, inv_inv, Matrix.mul_assoc]

/-- the trace of $f_U(x)$ is equal to the trace of $x$ -/
theorem innerAut_apply_trace_eq [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAut U x).trace = x.trace :=
  StarAlgEquiv.trace_preserving _ _

variable [DecidableEq n]

theorem exists_innerAut_iff_exists_innerAut_inv {P : Matrix n n 𝕜 → Prop} (x : Matrix n n 𝕜) :
    (∃ U : unitaryGroup n 𝕜, P (innerAut U x)) ↔ ∃ U : unitaryGroup n 𝕜, P (innerAut U⁻¹ x) :=
  by
  constructor <;> rintro ⟨U, hU⟩
  · use U⁻¹
    simp_rw [inv_inv]
    exact hU
  · use U⁻¹
    exact hU

theorem innerAut.is_injective (U : unitaryGroup n 𝕜) : Function.Injective (innerAut U) :=
  by
  intro u v huv
  rw [← inner_aut_inv_apply_inner_aut_self U u, huv, inner_aut_inv_apply_inner_aut_self]

/-- $x$ is Hermitian if and only if $f_U(x)$ is Hermitian -/
theorem IsHermitian.innerAut_iff (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    x.IsHermitian ↔ (innerAut U x).IsHermitian := by
  simp_rw [is_hermitian, inner_aut_conj_transpose,
    Function.Injective.eq_iff (inner_aut.is_injective U)]

theorem PosSemidef.innerAut {𝕜 : Type _} [IsROrC 𝕜] (U : unitaryGroup n 𝕜) {a : Matrix n n 𝕜} :
    (innerAut U a).PosSemidef ↔ a.PosSemidef :=
  by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (pos_semidef_iff _).mp h
    rw [inner_aut_eq_iff, inner_aut.map_mul, ← inner_aut_conj_transpose] at hy
    rw [hy]
    exact pos_semidef.star_mul_self _
  · intro h
    obtain ⟨y, hy⟩ := (pos_semidef_iff _).mp h
    rw [hy, inner_aut.map_mul, ← inner_aut_conj_transpose]
    exact pos_semidef.star_mul_self _

/-- $f_U(x)$ is positive definite if and only if $x$ is positive definite -/
theorem PosDef.innerAut {𝕜 : Type _} [IsROrC 𝕜] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    (innerAut U x).PosDef ↔ x.PosDef :=
  by
  let D := inner_aut U x
  have hD : inner_aut U x = D := rfl
  have hD' := hD
  rw [inner_aut_eq_iff] at hD'
  rw [hD', inner_aut_inv_apply_inner_aut_self]
  simp_rw [pos_def, ← is_hermitian.inner_aut_iff U, inner_aut_apply, ← mul_vec_mul_vec,
    dot_product_mul_vec _ U]
  have ugh : ∀ (u : n → 𝕜) (v : Matrix n n 𝕜), vec_mul (star u) v = star (mul_vec (star v) u) :=
    by
    intros
    ext1
    simp_rw [Pi.star_apply, vec_mul, mul_vec, dot_product, star_sum, star_mul', star_apply,
      star_star, Pi.star_apply, mul_comm]
  simp_rw [ugh, ← unitary_group.inv_apply]
  have ugh' : ∀ (hi : unitary_group n 𝕜) (u : n → 𝕜), mul_vec (hi : _) u ≠ 0 ↔ u ≠ 0 :=
    by
    intros
    rw [Ne.def, ← to_lin'_apply, ← unitary_group.to_lin'_eq, ← unitary_group.to_linear_equiv_eq,
      (injective_iff_map_eq_zero' _).mp (LinearEquiv.injective (unitary_group.to_linear_equiv hi))]
  refine' ⟨fun h => ⟨h.1, fun u hu => _⟩, fun h => ⟨h.1, fun u hu => h.2 _ ((ugh' _ _).mpr hu)⟩⟩
  · rcases h with ⟨h1, h2⟩
    specialize h2 (mul_vec U u) ((ugh' _ _).mpr hu)
    simp_rw [mul_vec_mul_vec, unitary_group.inv_apply, unitary_group.star_mul_self, one_mul_vec,
      Matrix.mul_one] at h2
    exact h2

/-- Schur decomposition, but only for almost Hermitian matrices:
  given an almost Hermitian matrix $A$, there exists a diagonal matrix $D$ and
  a unitary matrix $U$ such that $UDU^*=A$ -/
theorem IsAlmostHermitian.schur_decomp {𝕜 : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] {A : Matrix n n 𝕜}
    (hA : A.IsAlmostHermitian) :
    ∃ (D : n → 𝕜) (U : unitaryGroup n 𝕜), innerAut U (diagonal D) = A :=
  by
  rcases hA with ⟨α, B, ⟨rfl, hB⟩⟩
  have : hB.eigenvector_matrix ∈ unitary_group n 𝕜 := by
    rw [mem_unitary_group_iff, mul_eq_mul, star_eq_conj_transpose,
      is_hermitian.conj_transpose_eigenvector_matrix, is_hermitian.eigenvector_matrix_mul_inv]
  let U : unitary_group n 𝕜 := ⟨_, this⟩
  have hU : ⇑U = hB.eigenvector_matrix := rfl
  use α • coe ∘ hB.eigenvalues
  use U
  simp_rw [diagonal_smul, SMulHomClass.map_smul, inner_aut_apply, unitary_group.inv_apply,
    star_eq_conj_transpose, hU, is_hermitian.conj_transpose_eigenvector_matrix, Matrix.mul_assoc, ←
    is_hermitian.spectral_theorem, ← Matrix.mul_assoc, is_hermitian.eigenvector_matrix_mul_inv,
    Matrix.one_mul]

/-- any $^*$-isomorphism on $M_n$ is an inner automorphism -/
theorem StarAlgEquiv.of_matrix_is_inner {𝕜 : Type _} [IsROrC 𝕜]
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) : ∃ U : unitaryGroup n 𝕜, innerAutStarAlg U = f :=
  by
  by_cases IsEmpty n
  · haveI := h
    use 1
    ext
    have : a = 0 := by simp only [eq_iff_true_of_subsingleton]
    simp_rw [this, map_zero]
  rw [not_isEmpty_iff] at h
  haveI := h
  let f' := f.to_alg_equiv
  obtain ⟨y', hy⟩ := aut_mat_inner f'
  let y := y'.to_linear_map.to_matrix'
  let yinv := y'.symm.to_linear_map.to_matrix'
  have Hy : y ⬝ yinv = 1 ∧ yinv ⬝ y = 1 := by
    simp_rw [y, yinv, LinearEquiv.toLinearMap_eq_coe, ← LinearMap.toMatrix'_comp,
      LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id, and_self_iff]
  have H : y⁻¹ = yinv := inv_eq_left_inv Hy.2
  have hf' : ∀ x : Matrix n n 𝕜, f' x = y ⬝ x ⬝ y⁻¹ :=
    by
    intro x
    simp_rw [hy, Algebra.autInner_apply, H, mul_eq_mul]
    rfl
  have hf : ∀ x : Matrix n n 𝕜, f x = y ⬝ x ⬝ y⁻¹ :=
    by
    intro x
    rw [← hf']
    rfl
  have : ∀ x : Matrix n n 𝕜, (f x)ᴴ = f xᴴ := fun _ => (StarAlgEquiv.map_star' _ _).symm
  simp_rw [hf, conj_transpose_mul, conj_transpose_nonsing_inv] at this
  have this3 : ∀ x : Matrix n n 𝕜, yᴴ ⬝ y ⬝ xᴴ ⬝ y⁻¹ = xᴴ ⬝ yᴴ :=
    by
    intro x
    simp_rw [Matrix.mul_assoc, ← Matrix.mul_assoc y, ← this, ← Matrix.mul_assoc, ←
      conj_transpose_nonsing_inv, ← conj_transpose_mul, H, Hy.2, Matrix.mul_one]
  have this2 : ∀ x : Matrix n n 𝕜, Commute xᴴ (yᴴ ⬝ y) :=
    by
    intro x
    simp_rw [Commute, SemiconjBy, mul_eq_mul, ← Matrix.mul_assoc, ← this3, Matrix.mul_assoc, H,
      Hy.2, Matrix.mul_one]
  have this4 : ∀ x : Matrix n n 𝕜, Commute x (yᴴ ⬝ y) :=
    by
    intros
    specialize this2 xᴴ
    simp_rw [conj_transpose_conj_transpose] at this2
    exact this2
  obtain ⟨α, hα⟩ := commutes_with_all_iff.mp this4
  have this6 : to_euclidean_lin (1 : Matrix n n 𝕜) = 1 :=
    by
    ext1; ext1;
    simp only [LinearMap.one_apply, to_euclidean_lin_eq_to_lin, to_lin_apply, one_mul_vec,
      smul_eq_mul]
    simp only [PiLp.basisFun_repr, PiLp.basisFun_apply, WithLp.equiv_symm_single, Finset.sum_apply,
      Pi.smul_apply, EuclideanSpace.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [smul_eq_mul, mul_one]
  have this7 : Function.Bijective (yᴴ ⬝ y).toLin' :=
    by
    rw [Function.bijective_iff_has_inverse]
    use(y⁻¹ ⬝ y⁻¹ᴴ).toLin'
    simp_rw [Function.LeftInverse, Function.RightInverse, Function.LeftInverse, ← to_lin'_mul_apply,
      Matrix.mul_assoc, ← Matrix.mul_assoc y⁻¹ᴴ, ← conj_transpose_mul, H, ← Matrix.mul_assoc y]
    simp only [Hy.2, Hy.1, conj_transpose_one, Matrix.mul_one, Matrix.one_mul, to_lin'_one,
      LinearMap.id_apply, eq_self_iff_true, forall_true_iff]
    simp_rw [← conj_transpose_mul, Hy.2, conj_transpose_one, to_lin'_one, LinearMap.id_apply,
      eq_self_iff_true, forall_true_iff, true_and_iff]
  have this8 : (yᴴ ⬝ y).PosSemidef := pos_semidef.star_mul_self _
  have this9 := (pos_semidef.invertible_iff_pos_def this8).mp this7
  have this12 : (1 : n → 𝕜) ≠ 0 :=
    by
    simp_rw [Ne.def, Function.funext_iff, Pi.one_apply, Pi.zero_apply, one_ne_zero]
    simp only [Classical.not_forall, not_false_iff, exists_const]
  have this10 : α = IsROrC.re α :=
    by
    have this10 := is_hermitian.coe_re_diag this8.1
    simp_rw [hα, diag_smul, diag_one, Pi.smul_apply, Pi.one_apply, Algebra.id.smul_eq_mul,
      mul_one] at this10
    have this11 : (IsROrC.re α : 𝕜) • (1 : n → 𝕜) = α • 1 :=
      by
      rw [← this10]
      ext1
      simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [(smul_left_injective _ _).eq_iff] at this11
    rw [this11]
    · exact Module.Free.noZeroSMulDivisors 𝕜 (n → 𝕜)
    · exact this12
  have this13 : star (1 : n → 𝕜) ⬝ᵥ (1 : n → 𝕜) = Fintype.card n :=
    by
    simp only [dot_product, Pi.star_apply, Pi.one_apply, star_one, one_mul, Finset.sum_const]
    simp only [Nat.smul_one_eq_coe, Nat.cast_inj]
    rfl
  simp_rw [hα, pos_def, smul_mul_vec_assoc, dot_product_smul, one_mul_vec, smul_eq_mul] at this9
  cases' this9 with this9l this9
  specialize this9 1 this12
  rw [this10, this13, IsROrC.re_ofReal_mul, mul_pos_iff] at this9
  simp_rw [IsROrC.natCast_re, Nat.cast_pos, Fintype.card_pos] at this9
  have this14 : ¬(Fintype.card n : ℝ) < 0 := by simp only [not_lt, Nat.cast_nonneg]
  simp_rw [this14, and_false_iff, and_true_iff, or_false_iff] at this9
  have fin : (((IsROrC.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y ∈ unitary_group n 𝕜 :=
    by
    rw [mem_unitary_group_iff', star_eq_conj_transpose, mul_eq_mul]
    simp_rw [conj_transpose_smul, IsROrC.star_def, Matrix.smul_mul, Matrix.mul_smul,
      IsROrC.conj_ofReal, smul_smul, ← IsROrC.ofReal_mul]
    rw [← Real.rpow_add this9, hα, this10, smul_smul, ← IsROrC.ofReal_mul, IsROrC.ofReal_re, ←
      Real.rpow_add_one (NormNum.ne_zero_of_pos _ this9)]
    norm_num
  let U : unitary_group n 𝕜 := ⟨_, Fin⟩
  have hU : (U : Matrix n n 𝕜) = (((IsROrC.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y := rfl
  have hU2 : ((((IsROrC.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y)⁻¹ = ((U⁻¹ : _) : Matrix n n 𝕜) :=
    by
    apply inv_eq_left_inv
    rw [← hU, unitary_group.inv_apply, unitary_group.star_mul_self]
  have hU3 :
    ((((IsROrC.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y)⁻¹ =
      (((IsROrC.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜)⁻¹ • y⁻¹ :=
    by
    apply inv_eq_left_inv
    simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [inv_mul_cancel, one_smul, H, Hy.2]
    · simp_rw [Ne.def, IsROrC.ofReal_eq_zero, Real.rpow_eq_zero_iff_of_nonneg (le_of_lt this9),
        NormNum.ne_zero_of_pos _ this9, false_and_iff]
      exact not_false
  use U
  ext1 x
  simp_rw [inner_aut_star_alg_apply_eq_inner_aut_apply, inner_aut_apply, hf, hU, ← hU2, hU3,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← IsROrC.ofReal_inv, ← IsROrC.ofReal_mul, ←
    Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt this9), ← Real.rpow_add this9]
  norm_num

noncomputable def StarAlgEquiv.unitary {𝕜 : Type _} [IsROrC 𝕜]
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) : unitaryGroup n 𝕜 :=
  by
  choose U hU using f.of_matrix_is_inner
  exact U

def StarAlgEquiv.eq_inner_aut {𝕜 : Type _} [IsROrC 𝕜] (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) :
    innerAutStarAlg f.unitary = f :=
  StarAlgEquiv.Unitary._proof_2 f

#print Matrix.IsHermitian.spectral_theorem' /-
theorem IsHermitian.spectral_theorem' {𝕜 : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    x = innerAut ⟨_, hx.eigenvectorMatrix_mem_unitaryGroup⟩ (diagonal (coe ∘ hx.Eigenvalues)) :=
  by
  rw [inner_aut_apply, unitary_group.inv_apply, Matrix.unitaryGroup.coe_mk, star_eq_conj_transpose,
    is_hermitian.conj_transpose_eigenvector_matrix]
  simp_rw [Matrix.mul_assoc, ← is_hermitian.spectral_theorem hx, ← Matrix.mul_assoc,
    is_hermitian.eigenvector_matrix_mul_inv, Matrix.one_mul]
-/

theorem coe_diagonal_eq_diagonal_coe {n 𝕜 : Type _} [IsROrC 𝕜] [DecidableEq n] (x : n → ℝ) :
    (diagonal (coe ∘ x) : Matrix n n 𝕜) = coe ∘ diagonal x :=
  by
  simp_rw [← Matrix.ext_iff, diagonal, Function.comp_apply, of_apply]
  intros
  have :
    ((↑((of fun i j : n => ite (i = j) (x i) 0 : Matrix n n ℝ) i : n → ℝ) : n → 𝕜) j : 𝕜) =
      ↑(of (fun i j : n => ite (i = j) (x i) 0) i j) :=
    rfl
  simp_rw [this, of_apply, ite_cast, IsROrC.ofReal_zero]

theorem diagonal.spectrum {𝕜 n : Type _} [Field 𝕜] [Fintype n] [DecidableEq n] (A : n → 𝕜) :
    spectrum 𝕜 (diagonal A : Matrix n n 𝕜).toLin' = {x : 𝕜 | ∃ i : n, A i = x} :=
  by
  simp_rw [Set.ext_iff, ← Module.End.hasEigenvalue_iff_mem_spectrum, ←
    Module.End.has_eigenvector_iff_hasEigenvalue, to_lin'_apply, Function.funext_iff, mul_vec,
    diagonal_dot_product, Pi.smul_apply, Algebra.id.smul_eq_mul, mul_eq_mul_right_iff, Ne.def,
    Set.mem_setOf_eq, Function.funext_iff, Pi.zero_apply, Classical.not_forall]
  intro x
  constructor
  · rintro ⟨v, ⟨h, ⟨j, hj⟩⟩⟩
    specialize h j
    cases h
    · exact ⟨j, h⟩
    · contradiction
  · rintro ⟨i, hi⟩
    let v : n → 𝕜 := fun j => ite (j = i) 1 0
    use v
    simp_rw [v, ite_eq_right_iff, one_ne_zero, imp_false, Classical.not_not]
    constructor
    · intro j
      by_cases j = i
      · left
        rw [h, hi]
      · right
        exact h
    · use i

theorem IsHermitian.spectrum {𝕜 : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) : spectrum 𝕜 x.toLin' = {x : 𝕜 | ∃ i : n, (hx.Eigenvalues i : 𝕜) = x} :=
  by
  nth_rw_lhs 1 [Matrix.IsHermitian.spectral_theorem' hx]
  simp_rw [inner_aut.spectrum_eq, diagonal.spectrum]

theorem IsHermitian.hasEigenvalue_iff {𝕜 : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) (α : 𝕜) :
    Module.End.HasEigenvalue x.toLin' α ↔ ∃ i, (hx.Eigenvalues i : 𝕜) = α := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, hx.spectrum, Set.mem_setOf]

-- MOVE:
theorem innerAut_commutes_with_map_lid_symm (U : Matrix.unitaryGroup n 𝕜) :
    TensorProduct.map 1 (innerAut U) ∘ₗ (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).symm.toLinearMap =
      (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).symm.toLinearMap ∘ₗ innerAut U :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, LinearEquiv.toLinearMap_eq_coe,
    LinearEquiv.coe_coe, TensorProduct.lid_symm_apply, TensorProduct.map_tmul, LinearMap.one_apply,
    eq_self_iff_true, forall_const]

-- MOVE:
theorem innerAut_commutes_with_lid_comm (U : Matrix.unitaryGroup n 𝕜) :
    (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).toLinearMap ∘ₗ
        (TensorProduct.comm 𝕜 (Matrix n n 𝕜) 𝕜).toLinearMap ∘ₗ TensorProduct.map (innerAut U) 1 =
      innerAut U ∘ₗ
        (TensorProduct.lid 𝕜 (Matrix n n 𝕜)).toLinearMap ∘ₗ
          (TensorProduct.comm 𝕜 (Matrix n n 𝕜) 𝕜).toLinearMap :=
  by
  simp_rw [TensorProduct.ext_iff, LinearMap.comp_apply, TensorProduct.map_apply,
    LinearEquiv.toLinearMap_eq_coe, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    TensorProduct.lid_tmul, LinearMap.one_apply, SMulHomClass.map_smul, eq_self_iff_true,
    forall₂_true_iff]

theorem unitaryGroup.conj_mem {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) : (U : Matrix n n 𝕜)ᴴᵀ ∈ unitaryGroup n 𝕜 :=
  by
  rw [mem_unitary_group_iff']
  calc
    star (U : Matrix n n 𝕜)ᴴᵀ * (U : Matrix n n 𝕜)ᴴᵀ = (U : _)ᴴᵀᴴ * (U : _)ᴴᵀ := rfl
    _ = ((U : _)ᴴ * (U : _))ᴴᵀ := by simp_rw [mul_eq_mul, Matrix.conj_hMul] <;> rfl
    _ = 1ᴴᵀ := by rw [← star_eq_conj_transpose, mul_eq_mul, unitary_group.star_mul_self]
    _ = 1 := Matrix.conj_one

def unitaryGroup.conj {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n] [DecidableEq n] (U : unitaryGroup n 𝕜) :
    unitaryGroup n 𝕜 :=
  ⟨(U : _)ᴴᵀ, unitaryGroup.conj_mem U⟩

@[norm_cast]
theorem unitaryGroup.conj_coe {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) : (unitaryGroup.conj U : Matrix n n 𝕜) = Uᴴᵀ :=
  rfl

theorem innerAut.conj {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n] [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) : (innerAut U x)ᴴᵀ = innerAut (unitaryGroup.conj U) xᴴᵀ :=
  by
  simp_rw [inner_aut_apply, Matrix.conj_hMul, unitary_group.inv_apply, unitary_group.conj_coe]
  rfl

open scoped Kronecker

theorem kronecker_mem_unitaryGroup {p : Type _} [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜)
    (U₂ : unitaryGroup p 𝕜) : U₁ ⊗ₖ U₂ ∈ unitaryGroup (n × p) 𝕜 := by
  simp_rw [mem_unitary_group_iff, star_eq_conj_transpose, kronecker_conj_transpose, mul_eq_mul, ←
    mul_kronecker_mul, ← star_eq_conj_transpose, unitary_group.mul_star_self, one_kronecker_one]

def unitaryGroup.kronecker {p : Type _} [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜)
    (U₂ : unitaryGroup p 𝕜) : unitaryGroup (n × p) 𝕜 :=
  ⟨U₁ ⊗ₖ U₂, kronecker_mem_unitaryGroup _ _⟩

theorem unitaryGroup.kronecker_coe {p : Type _} [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜)
    (U₂ : unitaryGroup p 𝕜) : (unitaryGroup.kronecker U₁ U₂ : Matrix _ _ 𝕜) = U₁ ⊗ₖ U₂ :=
  rfl

theorem innerAut_kronecker {p : Type _} [Fintype p] [DecidableEq p] (U₁ : unitaryGroup n 𝕜)
    (U₂ : unitaryGroup p 𝕜) (x : Matrix n n 𝕜) (y : Matrix p p 𝕜) :
    innerAut U₁ x ⊗ₖ innerAut U₂ y = innerAut (unitaryGroup.kronecker U₁ U₂) (x ⊗ₖ y) := by
  simp_rw [inner_aut_apply, unitary_group.inv_apply, unitary_group.kronecker_coe,
    star_eq_conj_transpose, kronecker_conj_transpose, ← mul_kronecker_mul]

theorem PosSemidef.kronecker {𝕜 n p : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] {x : Matrix n n 𝕜} {y : Matrix p p 𝕜} (hx : x.PosSemidef)
    (hy : y.PosSemidef) : (x ⊗ₖ y).PosSemidef :=
  by
  rw [Matrix.IsHermitian.spectral_theorem' hx.1, Matrix.IsHermitian.spectral_theorem' hy.1,
    inner_aut_kronecker, diagonal_kronecker_diagonal, pos_semidef.inner_aut, pos_semidef.diagonal]
  simp_rw [Function.comp_apply, ← IsROrC.ofReal_mul, IsROrC.ofReal_re, eq_self_iff_true,
    and_true_iff,
    mul_nonneg (is_hermitian.nonneg_eigenvalues_of_pos_semidef hx _)
      (is_hermitian.nonneg_eigenvalues_of_pos_semidef hy _),
    forall_true_iff]

theorem PosDef.kronecker {𝕜 n p : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] {x : Matrix n n 𝕜} {y : Matrix p p 𝕜} (hx : x.PosDef)
    (hy : y.PosDef) : (x ⊗ₖ y).PosDef :=
  by
  rw [Matrix.IsHermitian.spectral_theorem' hx.1, Matrix.IsHermitian.spectral_theorem' hy.1,
    inner_aut_kronecker, pos_def.inner_aut, diagonal_kronecker_diagonal, pos_def.diagonal]
  simp_rw [Function.comp_apply, ← IsROrC.ofReal_mul, IsROrC.ofReal_re, eq_self_iff_true,
    and_true_iff, mul_pos (hx.pos_eigenvalues _) (hy.pos_eigenvalues _), forall_true_iff]

theorem unitaryGroup.injective_hMul {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [IsROrC 𝕜]
    (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) : x = y ↔ x ⬝ U = y ⬝ U :=
  by
  refine' ⟨fun h => by rw [h], fun h => _⟩
  nth_rw_rhs 1 [← Matrix.mul_one y]
  rw [← unitary_group.mul_star_self U, ← Matrix.mul_assoc, ← h, Matrix.mul_assoc,
    unitary_group.mul_star_self, Matrix.mul_one]

theorem innerAutStarAlg_equiv_toLinearMap {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [IsROrC 𝕜]
    [DecidableEq 𝕜] (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).toAlgEquiv.toLinearMap = innerAut U :=
  rfl

theorem innerAutStarAlg_equiv_symm_toLinearMap {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [IsROrC 𝕜]
    (U : unitaryGroup n 𝕜) : (innerAutStarAlg U).symm.toAlgEquiv.toLinearMap = innerAut U⁻¹ :=
  by
  ext1
  simp only [inner_aut_star_alg_symm_apply, inner_aut_apply, inv_inv, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv]
  rw [unitary_group.inv_apply]
  rfl

theorem innerAut.comp_inj {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [IsROrC 𝕜]
    (U : Matrix.unitaryGroup n 𝕜) (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ innerAut U ∘ₗ S = innerAut U ∘ₗ T := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, inner_aut_eq_iff,
    inner_aut_inv_apply_inner_aut_self]

theorem innerAut.inj_comp {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [IsROrC 𝕜]
    (U : unitaryGroup n 𝕜) (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ S ∘ₗ innerAut U = T ∘ₗ innerAut U :=
  by
  refine' ⟨fun h => by rw [h], fun h => _⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply] at h ⊢
  intro x
  nth_rw_lhs 1 [← inner_aut_apply_inner_aut_inv_self U x]
  rw [h, inner_aut_apply_inner_aut_inv_self]

end Matrix

