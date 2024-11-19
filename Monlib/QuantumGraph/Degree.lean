import Monlib.LinearAlgebra.QuantumSet.PhiMap
import Monlib.QuantumGraph.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Monlib.QuantumGraph.Example

open scoped InnerProductSpace ComplexOrder

theorem QuantumSet.innerOne_map_one_toSubset_eq
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  (r₁ r₂ : ℝ) {f : A →ₗ[ℂ] B} :
  letI := QuantumSet.instSubset (A := B) (by infer_instance) r₂
  ⟪1, f 1⟫_ℂ = ⟪1, (f.toSubsetQuantumSet r₁ r₂) 1⟫_ℂ :=
by
  simp
  rw [← AlgEquiv.toLinearMap_apply]
  letI := QuantumSet.instSubset (A := B) (by infer_instance) r₂
  nth_rw 2 [← LinearMap.adjoint_inner_left]
  rw [toSubset_algEquiv_adjoint, LinearMap.comp_apply]
  simp only [AlgEquiv.toLinearMap_apply, map_one]

theorem schurProjection.innerOne_map_one_nonneg_of_gns
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A]
  [QuantumSet B]
  [PartialOrder A] [PartialOrder B] [StarOrderedRing A] [StarOrderedRing B] (gns : k A = 0)
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  (h₂ : ∀ ⦃a : B⦄, 0 ≤ a ↔ ∃ (b : B), a = star b * b)
  {f : A →ₗ[ℂ] B}
  (h : schurProjection f) :
    0 ≤ ⟪1, f 1⟫_ℂ :=
by
  have iPM := schurProjection.isPosMap gns h₁ h
  obtain ⟨x, hx⟩ := h₂.mp (@iPM 1 zero_le_one)
  rw [hx, ← inner_conj_symm, QuantumSet.inner_star_left, star_star, mul_one,
    inner_conj_symm, ← add_halves (-k B), ← QuantumSet.modAut_apply_modAut,
    ← AlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_right,
    QuantumSet.modAut_adjoint, AlgEquiv.toLinearMap_apply]
  exact inner_self_nonneg'


instance {A : Type*} [hA : PartialOrder A] (r : ℝ) :
    PartialOrder (QuantumSet.subset r A) :=
hA
instance {A : Type*} [hA : NonUnitalNonAssocSemiring A] (r : ℝ) :
  NonUnitalNonAssocSemiring (QuantumSet.subset r A) :=
hA
instance {A : Type*} [hA : NonUnitalSemiring A] (r : ℝ) :
  NonUnitalSemiring (QuantumSet.subset r A) :=
hA
instance {A : Type*} [NonUnitalNonAssocSemiring A] [hA : StarRing A] (r : ℝ) :
  StarRing (QuantumSet.subset r A) :=
hA
instance {A : Type*} [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [hA : StarOrderedRing A] (r : ℝ) :
  StarOrderedRing (QuantumSet.subset r A) :=
hA
instance {A : Type*} [hA : Nontrivial A] (r : ℝ) :
  Nontrivial (QuantumSet.subset r A) :=
hA

theorem QuantumGraph.real_iff {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔ f •ₛ f = f ∧ LinearMap.IsReal f :=
⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

theorem quantumGraph_iff {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} :
  QuantumGraph A f ↔ f •ₛ f = f :=
⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem QuantumGraph.toSubset_iff {A : Type*} [starAlgebra A] [h : QuantumSet A] {f : A →ₗ[ℂ] A} (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) h r
  QuantumGraph (QuantumSet.subset r A)
  (LinearMap.toSubsetQuantumSet f r r) ↔ QuantumGraph A f :=
by
  simp only [quantumGraph_iff, schurMul_toSubsetQuantumSet, LinearMap.toSubsetQuantumSet_inj]

theorem QuantumGraph.real_toSubset_iff {A : Type*} [starAlgebra A] [h : QuantumSet A] {f : A →ₗ[ℂ] A} (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) h r
  QuantumGraph.Real (QuantumSet.subset r A)
  (LinearMap.toSubsetQuantumSet f r r) ↔ QuantumGraph.Real A f :=
by
  simp only [real_iff, LinearMap.toSubsetQuantumSet_isReal_iff,
    schurMul_toSubsetQuantumSet, LinearMap.toSubsetQuantumSet_inj]

theorem QuantumGraph.Real.innerOne_map_one_nonneg
  {A : Type*} [starAlgebra A] [hA : QuantumSet A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) :
    0 ≤ ⟪1, f 1⟫_ℂ :=
by
  rw [QuantumSet.innerOne_map_one_toSubset_eq 0 0]
  letI := hA.instSubset 0
  apply schurProjection.innerOne_map_one_nonneg_of_gns rfl
  exact h₁; exact h₁
  simp_rw [← quantumGraphReal_iff_schurProjection]
  exact (real_toSubset_iff 0).mpr h

open scoped TensorProduct

attribute [local instance] starAlgebra.mulOpposite
attribute [local instance] InnerProductAlgebra.mulOpposite
attribute [local instance] QuantumSet.mulOpposite
attribute [local instance] MulOpposite.starRing

theorem QuantumGraph.Real.innerOne_map_one_eq_zero_iff_of_kms
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) [kms : Fact (k A = - (1 / 2))] :
    ⟪1, f 1⟫_ℂ = 0 ↔ f = 0 :=
by
  rw [oneInner_map_one_eq_oneInner_Psi_map _ 0 (k A + (1/2)),
    ← (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp h).1]
  nth_rw 1 [← (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp h).2]
  simp_rw [Coalgebra.inner_eq_counit']
  rw [QuantumSet.counit_isFaithful, map_eq_zero_iff _ (LinearEquiv.injective _)]

theorem QuantumGraph.Real.innerOne_map_one_eq_zero_iff
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) :
    ⟪1, f 1⟫_ℂ = 0 ↔ f = 0 :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) (-(1 / 2))
  have kms : Fact (k (QuantumSet.subset (-(1/2)) A) = -(1/2)) := Fact.mk rfl
  let f' := LinearMap.toSubsetQuantumSet f (-(1/2)) (-(1/2))
  rw [QuantumSet.innerOne_map_one_toSubset_eq (- (1/2)) (- (1/2)),
    QuantumGraph.Real.innerOne_map_one_eq_zero_iff_of_kms
      ((QuantumGraph.real_toSubset_iff (-(1/2))).mpr h) (kms := kms)]
  rfl

theorem QuantumGraph.real_iff_complement'_real
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔ QuantumGraph.Real A (Qam.complement' f) :=
by
  simp only [real_iff, ← Qam.Nontracial.Complement'.qam, ← Qam.Nontracial.Complement'.qam.isReal]

set_option maxHeartbeats 250000 in
theorem QuantumGraph.Real.innerOne_map_one_eq_norm_pow_four_iff_of_kms
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) [kms : Fact (k A = - (1 / 2))] :
    ⟪1, f 1⟫_ℂ = ‖(1 : A)‖ ^ 4 ↔ f = rankOne ℂ (1 : A) (1 : A) :=
by
  have : ‖(1 : A)‖ ^ 4 = ⟪(1 : A ⊗[ℂ] Aᵐᵒᵖ), 1⟫_ℂ :=
  by
    simp only [Algebra.TensorProduct.one_def, TensorProduct.inner_tmul, inner_self_eq_norm_sq_to_K,
      ← mul_pow, MulOpposite.norm_eq, MulOpposite.unop_one, ← sq, ← pow_mul]
    rfl
  rw [oneInner_map_one_eq_oneInner_Psi_map _ 0 (k A + (1/2))]
  rw [this]
  nth_rw 3 [← QuantumSet.Psi_apply_one_one 0 (k A + ( 1 / 2))]
  rw [eq_comm, ← sub_eq_zero, ← inner_sub_right (𝕜 := ℂ) (E := A ⊗[ℂ] Aᵐᵒᵖ), ← map_sub,
    ← Qam.completeGraph_eq, ← Qam.complement'_eq]
  have := QuantumGraph.real_iff_complement'_real.mp h
  rw [← (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp this).1]
  nth_rw 1 [← (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp this).2]
  simp_rw [Coalgebra.inner_eq_counit']
  rw [QuantumSet.counit_isFaithful, map_eq_zero_iff _ (LinearEquiv.injective _),
    Qam.complement'_eq, sub_eq_zero, eq_comm]

theorem QuantumSet.normOne_toSubset {A : Type*} [starAlgebra A] [QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  ‖(1 : A)‖ = ‖(1 : QuantumSet.subset r A)‖ :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  simp_rw [norm_eq_sqrt_inner (𝕜 := ℂ), QuantumSet.subset_inner_eq,
    ← QuantumSet.toSubset_algEquiv_symm_eq_toSubset_equiv, map_one]

theorem LinearMap.toSubsetQuantumSet_eq_iff {A B : Type*}  [ha : starAlgebra A]
  [starAlgebra B] [hA : QuantumSet A] [hB : QuantumSet B] (sk₁ : ℝ) (sk₂ : ℝ)
  (f : A →ₗ[ℂ] B) (g : QuantumSet.subset sk₁ A →ₗ[ℂ] QuantumSet.subset sk₂ B) :
  f.toSubsetQuantumSet sk₁ sk₂ = g ↔ f = g.ofSubsetQuantumSet sk₁ sk₂ :=
by rfl

theorem QuantumGraph.Real.innerOne_map_one_eq_norm_pow_four_iff
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) :
    ⟪1, f 1⟫_ℂ = ‖(1 : A)‖ ^ 4 ↔ f = rankOne ℂ (1 : A) (1 : A) :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) (-(1 / 2))
  have kms : Fact (k (QuantumSet.subset (-(1/2)) A) = -(1/2)) := Fact.mk rfl
  let f' := LinearMap.toSubsetQuantumSet f (-(1/2)) (-(1/2))
  rw [QuantumSet.innerOne_map_one_toSubset_eq (- (1/2)) (- (1/2)), QuantumSet.normOne_toSubset]
  rw [QuantumGraph.Real.innerOne_map_one_eq_norm_pow_four_iff_of_kms
      ((QuantumGraph.real_toSubset_iff (-(1/2))).mpr h) (kms := kms)]
  rw [LinearMap.toSubsetQuantumSet_eq_iff, rankOne_ofSubsetQuantumSet]
  simp_rw [← QuantumSet.toSubset_algEquiv_symm_eq_toSubset_equiv, map_one]

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

theorem QuantumGraph.Real.innerOne_map_one_le_norm_one_pow_four_of_gns
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (gns : k A = 0)
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) :
    ⟪1, f 1⟫_ℂ ≤ ‖(1 : A)‖ ^ 4 :=
by
  have sP : schurProjection f := ⟨h.isIdempotentElem, h.isReal⟩
  have iPM := schurProjection.isPosMap gns h₁ sP
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

lemma QuantumGraph.zero_le_degree_le_norm_one_sq_of_gns
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) (gns : k A = 0)
  {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) (d : ℂ) (h2 : (h.toQuantumGraph).IsRegular d) :
    0 ≤ d ∧ d ≤ ‖(1 : A)‖ ^ 2 :=
by
  have sP : schurProjection f := ⟨h.isIdempotentElem, h.isReal⟩
  have iPM := schurProjection.isPosMap gns h₁ sP
  have hd : d = ⟪1, f 1⟫_ℂ / ⟪1, (1 : A)⟫_ℂ :=
    by
      rw [h2.1, inner_smul_right, mul_div_assoc, div_self, mul_one]
      norm_num
  rw [hd]
  refine ⟨mul_nonneg (QuantumGraph.Real.innerOne_map_one_nonneg h₁ h) ?_, ?_⟩
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
          exact Real.innerOne_map_one_le_norm_one_pow_four_of_gns gns h₁ h
  simp [inner_self_eq_norm_sq_to_K]

theorem StarOrderedRing.nonneg_iff_toQuantumSetSubset
  {A : Type*} [NonUnitalSemiring A] [StarRing A]
  [PartialOrder A] [StarOrderedRing A] (r : ℝ) :
  (∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) ↔
    ∀ ⦃a : QuantumSet.subset r A⦄, 0 ≤ a ↔ ∃ (b : QuantumSet.subset r A), a = star b * b :=
Iff.rfl

set_option maxHeartbeats 650000 in
set_option synthInstance.maxHeartbeats 30000 in
theorem Coalgebra.comul_comp_mul_quantumSetSubset
  {A : Type*} [starAlgebra A] [QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r;
  Coalgebra.comul ∘ₗ LinearMap.mul' ℂ (QuantumSet.subset r A)
    = (TensorProduct.map (QuantumSet.toSubset_algEquiv r).toLinearMap
        (QuantumSet.toSubset_algEquiv r).toLinearMap)
      ∘ₗ (Coalgebra.comul (R := ℂ) (A := A)
      ∘ₗ (LinearMap.mul' ℂ A))
      ∘ₗ (TensorProduct.map (QuantumSet.toSubset_algEquiv r).symm.toLinearMap
          (QuantumSet.toSubset_algEquiv r).symm.toLinearMap) :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  letI : Fact (k A = k A) := Fact.mk rfl
  letI hh := QuantumSet.tensorProduct (A := A) (B := A) (h := Fact.mk rfl)
  letI := QuantumSet.instSubset (A := A ⊗[ℂ] A) (by infer_instance) r
  have : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ (QuantumSet.subset r A)
    = (TensorProduct.map (QuantumSet.toSubset_algEquiv r).toLinearMap
          (QuantumSet.toSubset_algEquiv r).toLinearMap)
      ∘ₗ (Coalgebra.comul (R := ℂ) (A := A))
      ∘ₗ ((QuantumSet.toSubset_algEquiv r).symm.toLinearMap
      ∘ₗ (QuantumSet.toSubset_algEquiv r).toLinearMap)
      ∘ₗ (LinearMap.mul' ℂ A)
      ∘ₗ (TensorProduct.map (QuantumSet.toSubset_algEquiv r).symm.toLinearMap
          (QuantumSet.toSubset_algEquiv r).symm.toLinearMap) :=
  by
    rw [LinearMap.mul'_quantumSet_subset_eq]
    simp only [← LinearMap.comp_assoc]
    congr 4
    exact QuantumSet.comul_subset_eq _
  simpa only [LinearMap.comp_assoc, AlgEquiv.symm_comp_toLinearMap, LinearMap.comp_id]


theorem QuantumGraph.toSubset_isRegular_iff
  {A : Type*} [starAlgebra A] [QuantumSet A]
  {f : A →ₗ[ℂ] A} (r : ℝ) (h : QuantumGraph A f) (d : ℂ) :
  let h' := (QuantumGraph.toSubset_iff r).mpr h;
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r;
    h.IsRegular d ↔ h'.IsRegular d :=
by
  intro h'
  simp only [QuantumGraph.IsRegular, LinearMap.toSubsetQuantumSet_apply]
  rw [LinearMap.toSubsetQuantumSet_adjoint_apply]
  simp only [LinearMap.comp_apply, ← QuantumSet.toSubset_algEquiv_symm_eq_toSubset_equiv,
    ← QuantumSet.toSubset_algEquiv_eq_toSubset_equiv, map_one, AlgEquiv.toLinearMap_apply]
  nth_rw 3 [eq_comm]
  nth_rw 4 [eq_comm]
  simp_rw [← AlgEquiv.symm_apply_eq, map_smul, map_one]
  nth_rw 1 [eq_comm]
  nth_rw 2 [eq_comm]

set_option maxHeartbeats 550000 in
lemma QuantumGraph.zero_le_degree_le_norm_one_sq
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) (d : ℂ) (h2 : (h.toQuantumGraph).IsRegular d) :
    0 ≤ d ∧ d ≤ ‖(1 : A)‖ ^ 2 :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) 0
  rw [QuantumSet.normOne_toSubset 0]
  exact QuantumGraph.zero_le_degree_le_norm_one_sq_of_gns
    ((StarOrderedRing.nonneg_iff_toQuantumSetSubset 0).mp h₁) rfl
    ((QuantumGraph.real_toSubset_iff 0).mpr h) _
    ((QuantumGraph.toSubset_isRegular_iff 0 h.toQuantumGraph d).mp h2)
