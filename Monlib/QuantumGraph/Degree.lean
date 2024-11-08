import Monlib.LinearAlgebra.QuantumSet.PhiMap
import Monlib.QuantumGraph.Basic

open scoped InnerProductSpace ComplexOrder
open Coalgebra in
theorem QuantumSet.counit_isReal {A : Type*} [starAlgebra A] [QuantumSet A] :
  LinearMap.IsReal (counit (R := ℂ) (A := A)) :=
by
  intro x
  calc counit (star x) = ⟪x, 1⟫_ℂ :=
      by simp only [QuantumSet.inner_eq_counit, map_one, mul_one]
    _ = star ⟪1, x⟫_ℂ := (inner_conj_symm _ _).symm
    _ = star (counit x) := by simp_rw [QuantumSet.inner_eq_counit']

theorem QuantumSet.innerOne_map_one_isReal_ofReal
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (hf : LinearMap.IsReal f) :
    ⟪1, f 1⟫_ℂ = Complex.re ⟪1, f 1⟫_ℂ :=
by
  rw [eq_comm, ← Complex.conj_eq_iff_re]
  simp_rw [Coalgebra.inner_eq_counit']
  nth_rw 1 [← star_one]
  rw [hf, QuantumSet.counit_isReal]
  simp

theorem QuantumGraph.Real.innerOne_map_one_nonneg
  {A : Type*} [starAlgebra A] [QuantumSet A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1) {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) :
    0 ≤ ⟪1, f 1⟫_ℂ :=
by
  have sP : schurProjection f := ⟨h.isIdempotentElem, h.isReal⟩
  have iPM := schurProjection.isPosMap h₁ hδ h₂ sP
  obtain ⟨x, hx⟩ := h₁.mp (@iPM 1 zero_le_one)
  rw [hx, ← inner_conj_symm, QuantumSet.inner_star_left, star_star, mul_one,
    inner_conj_symm, ← add_halves (-k A), ← QuantumSet.modAut_apply_modAut,
    ← AlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_right,
    QuantumSet.modAut_adjoint, AlgEquiv.toLinearMap_apply]
  exact inner_self_nonneg'

def QuantumGraph.IsRegular
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (_h : QuantumGraph A f) (d : ℂ) : Prop :=
f 1 = d • 1 ∧ LinearMap.adjoint f 1 = d • 1

lemma QuantumGraph.degree_is_real_of_real
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A] {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) (d : ℂ)
  (h2 : (h.toQuantumGraph).IsRegular d) :
    d = Complex.re d :=
by
  have := calc d • (1 : A) = f 1 := h2.1.symm
    _ = f.real 1 := by rw [LinearMap.real_of_isReal h.isReal]
    _ = star (f 1) := by rw [LinearMap.real_apply, star_one]
    _ = star d • (1 : A) := by rw [h2.1, star_smul, star_one]
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at this
  simp_rw [one_ne_zero, or_false, sub_eq_zero] at this
  exact (Complex.conj_eq_iff_re.mp this.symm).symm

open scoped TensorProduct
lemma PhiMap_apply_one_one
  {A B : Type*} [starAlgebra B] [starAlgebra A] [QuantumSet A] [QuantumSet B] :
  (PhiMap (rankOne ℂ (1 : B) (1 : A))).1 = (1 : A ⊗[ℂ] B →ₗ[ℂ] _) :=
by
  simp_rw [PhiMap_apply, Upsilon_apply_one_one]
  exact rmulMapLmul_one

open scoped InnerProductSpace

lemma ContinuousLinearMap.isPositive_iff_complex' {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [CompleteSpace E'] (T : E' →L[ℂ] E') :
  T.IsPositive ↔ ∀ (x : E'), 0 ≤ ⟪T x, x⟫_ℂ :=
by simp [isPositive_iff_complex, RCLike.nonneg_def' (𝕜 := ℂ)]
lemma ContinuousLinearMap.isPositive_iff_complex'' {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [CompleteSpace E'] (T : E' →L[ℂ] E') :
  T.IsPositive ↔ ∀ (x : E'), 0 ≤ ⟪x, T x⟫_ℂ :=
by
  simp_rw [isPositive_iff_complex', ← inner_conj_symm (T _),
    Complex.nonneg_iff, Complex.conj_re, Complex.conj_im, zero_eq_neg, eq_comm]

lemma ContinuousLinearMap.le_iff_complex_inner_le {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] {p q : E →L[ℂ] E} :
  p ≤ q ↔ ∀ (x : E), ⟪x, p x⟫_ℂ ≤ ⟪x, q x⟫_ℂ :=
by
  rw [ContinuousLinearMap.le_def, isPositive_iff_complex'']
  simp only [sub_apply, inner_sub_right, sub_nonneg]

theorem isOrthogonalProjection_iff_exists {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {p : E →L[ℂ] E} :
  p.IsOrthogonalProjection ↔ (∃ U, orthogonalProjection' U = p) :=
by
  rw [ContinuousLinearMap.isOrthogonalProjection_iff', and_comm, ← orthogonal_projection_iff]

theorem orthogonalProjection'_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [CompleteSpace (⊤ : Submodule ℂ E)]
  (U : Submodule ℂ E) [CompleteSpace U] :
  orthogonalProjection' U ≤ 1 :=
by
  rw [← orthogonalProjection_of_top, orthogonalProjection.is_le_iff_subset]
  exact fun _ _ ↦ trivial

theorem isOrthogonalProjection_le_one {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {p : E →L[ℂ] E} (hp : p.IsOrthogonalProjection) :
    p ≤ 1 :=
by
  obtain ⟨U, rfl⟩ := isOrthogonalProjection_iff_exists.mp hp
  exact orthogonalProjection'_le_one U

lemma QuantumGraph.Real.gns_le_one
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (hf : QuantumGraph.Real A f) (gns : k A = 0) :
    LinearMap.toContinuousLinearMap (PhiMap f).1 ≤ 1 :=
isOrthogonalProjection_le_one
  ((quantumGraphReal_iff_Upsilon_toBimodule_orthogonalProjection gns).mp hf)

theorem QuantumGraph.Real.innerOne_map_one_le_norm_one_pow_four
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1) {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) (gns : k A = 0) :
    ⟪1, f 1⟫_ℂ ≤ ‖(1 : A)‖ ^ 4 :=
by
  have sP : schurProjection f := ⟨h.isIdempotentElem, h.isReal⟩
  have iPM := schurProjection.isPosMap h₁ hδ h₂ sP
  calc ⟪1, f 1⟫_ℂ = Complex.re ⟪1, f 1⟫_ℂ :=
      QuantumSet.innerOne_map_one_isReal_ofReal h.isReal
    _ = Complex.re ⟪1, (PhiMap f).1 1⟫_ℂ := by rw [← oneInner_map_one_eq_oneInner_PhiMap_map_one]
    _ = (RCLike.re ⟪1, LinearMap.toContinuousLinearMap (PhiMap f).1 1⟫_ℂ) := rfl
    _ ≤ RCLike.re ⟪(1 : A ⊗[ℂ] A), (1 : (A ⊗[ℂ] A) →L[ℂ] (A ⊗[ℂ] A)) 1⟫_ℂ :=
        by
          rw [Complex.real_le_real]
          exact
            ((RCLike.le_def.mp ((ContinuousLinearMap.le_iff_complex_inner_le
                (p := LinearMap.toContinuousLinearMap (PhiMap f).1)
                (q := 1)).mp
              (QuantumGraph.Real.gns_le_one h gns) 1)).1)
    _ = (‖(1 : A)‖ ^ 2) ^ 2 :=
      by
        rw [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq (𝕜 := ℂ) (E := A ⊗[ℂ] A),
          Algebra.TensorProduct.one_def, norm_tmul, ← pow_two]
        simp
    _ = ‖(1 : A)‖ ^ 4 := by simp only [← pow_mul]

lemma QuantumGraph.zero_le_degree_le_norm_one_sq
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1) {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) (d : ℂ)
  (h2 : (h.toQuantumGraph).IsRegular d)
  (gns : k A = 0) :
    0 ≤ d ∧ d ≤ ‖(1 : A)‖ ^ 2 :=
by
  have sP : schurProjection f := ⟨h.isIdempotentElem, h.isReal⟩
  have iPM := schurProjection.isPosMap h₁ hδ h₂ sP
  have hd : d = ⟪1, f 1⟫_ℂ / ⟪1, (1 : A)⟫_ℂ :=
    by
      rw [h2.1, inner_smul_right, mul_div_assoc, div_self, mul_one]
      norm_num
  rw [hd]
  refine ⟨mul_nonneg (QuantumGraph.Real.innerOne_map_one_nonneg h₁ hδ h₂ h) ?_, ?_⟩
  . simp only [inner_self_eq_norm_sq_to_K]
    simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      Complex.zero_le_real, inv_nonneg, pow_two_nonneg]
  rw [← ge_iff_le, ← Complex.ofReal_pow]
  calc ((‖(1 : A)‖ ^ 2 : ℝ) : ℂ) = ((‖(1 : A)‖ ^ 2) ^ 2 / ‖(1 : A)‖ ^ 2 : ℝ) :=
      by
        rw [pow_two, pow_two, mul_div_assoc, div_self, mul_one]
        norm_num
    _ = ((‖(1 : A)‖ ^ 4 / ‖(1 : A)‖ ^ 2 : ℝ) : ℂ) := by simp [← pow_mul]
    _ ≥ (⟪1, f 1⟫_ℂ / (‖(1 : A)‖ ^ 2 : ℝ) : ℂ) :=
      by
        rw [QuantumSet.innerOne_map_one_isReal_ofReal h.isReal]
        rw [← Complex.ofReal_div, ge_iff_le, Complex.real_le_real]
        apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
        . simp [← Complex.real_le_real, ← QuantumSet.innerOne_map_one_isReal_ofReal h.isReal]
          exact Real.innerOne_map_one_le_norm_one_pow_four h₁ hδ h₂ h gns
  simp [inner_self_eq_norm_sq_to_K]
