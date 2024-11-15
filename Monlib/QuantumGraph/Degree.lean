import Monlib.LinearAlgebra.QuantumSet.PhiMap
import Monlib.QuantumGraph.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Monlib.LinearAlgebra.QuantumSet.TensorProduct
import Monlib.QuantumGraph.Example
import Monlib.LinearAlgebra.Ips.Functional

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
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  {f : A →ₗ[ℂ] B} (hf : LinearMap.IsReal f) :
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

open scoped TensorProduct
noncomputable def starAlgebra.mulOpposite {A : Type*} [starAlgebra A] :
    starAlgebra Aᵐᵒᵖ where
  modAut r := (modAut (-r)).op
  modAut_trans _ _ := by simp [AlgEquiv.op_trans, add_comm]
  modAut_zero := by simp
  modAut_star _ x := by simp [← MulOpposite.op_star]

attribute [local instance] starAlgebra.mulOpposite

noncomputable def InnerProductAlgebra.mulOpposite {A : Type*} [starAlgebra A] [InnerProductAlgebra A] :
    InnerProductAlgebra (Aᵐᵒᵖ) where
  dist_eq _ _ := by simp [norm_eq_sqrt_inner (𝕜 := ℂ), MulOpposite.inner_eq, dist_eq_norm]
  norm_sq_eq_inner _ := by
    simp [MulOpposite.inner_eq, norm_eq_sqrt_inner (𝕜 := ℂ)]
    rw [← RCLike.re_eq_complex_re]
    exact Real.sq_sqrt (inner_self_nonneg)
  conj_symm _ _ := inner_conj_symm _ _
  add_left _ _ _ := inner_add_left _ _ _
  smul_left x y _ := inner_smul_left _ _ _

attribute [local instance] InnerProductAlgebra.mulOpposite

noncomputable instance QuantumSet.mulOpposite {A : Type*} [starAlgebra A] [QuantumSet A]
  [kms : Fact (k A = - (1 / 2))] :
    QuantumSet Aᵐᵒᵖ where
  modAut_isSymmetric r x y := by
    simp [MulOpposite.inner_eq, modAut]
  k := k A
  inner_star_left _ _ _ := by
    simp only [MulOpposite.inner_eq, modAut, MulOpposite.unop_mul]
    rw [inner_conj_left]
    simp [kms.out]
    norm_num
  inner_conj_left _ _ _ := by
    simp only [MulOpposite.inner_eq, modAut, MulOpposite.unop_mul]
    rw [inner_star_left]
    simp [kms.out]
    norm_num
  n := n A
  n_isFintype := n_isFintype
  n_isDecidableEq := n_isDecidableEq
  onb := onb.mulOpposite

attribute [local instance] QuantumSet.mulOpposite

noncomputable instance CoalgebraStruct.mulOpposite {A : Type*} [Semiring A] [Algebra ℂ A] [CoalgebraStruct ℂ A] :
    CoalgebraStruct ℂ Aᵐᵒᵖ where
  comul := (Algebra.TensorProduct.opAlgEquiv ℂ ℂ A A).symm.toLinearMap ∘ₗ Coalgebra.comul.op
  counit := (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap ∘ₗ Coalgebra.counit.op
theorem Coalgebra.counit_mulOpposite_eq {A : Type*} [Semiring A] [Algebra ℂ A] [CoalgebraStruct ℂ A] (a : Aᵐᵒᵖ) :
  (Coalgebra.counit (R := ℂ) (A := Aᵐᵒᵖ)) a = Coalgebra.counit a.unop :=
rfl

theorem QuantumSet.counit_isFaithful {A : Type*} [starAlgebra A] [QuantumSet A] :
  Module.Dual.IsFaithful (Coalgebra.counit (R := ℂ) (A := A)) :=
by
  intro x
  simp [← QuantumSet.inner_eq_counit']
  rw [← inner_conj_symm, QuantumSet.inner_star_left, star_star, mul_one, ← add_halves (- k A),
    ← modAut_apply_modAut, ← modAut_isSymmetric, inner_conj_symm, inner_self_eq_zero,
    map_eq_zero_iff _ (AlgEquiv.injective _)]

def Module.Dual.op {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  (f : Module.Dual R A) :
  Module.Dual R Aᵐᵒᵖ :=
(unop R).toLinearMap ∘ₗ LinearMap.op f
theorem Module.Dual.op_apply {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  (f : Module.Dual R A) (x : Aᵐᵒᵖ) :
    Module.Dual.op f x = f x.unop :=
rfl

theorem Coalgebra.counit_moduleDualOp_eq {A : Type*} [Semiring A] [Algebra ℂ A]
  [CoalgebraStruct ℂ A] :
    Module.Dual.op (Coalgebra.counit (R := ℂ) (A := A)) = counit (R := ℂ) (A := Aᵐᵒᵖ) :=
rfl

def MulOpposite.starRing {A : Type*} [NonUnitalNonAssocSemiring A] [hA : StarRing A] :
    StarRing Aᵐᵒᵖ where
  star_add _ _ := star_add _ _

attribute [local instance] MulOpposite.starRing

theorem Module.Dual.op_isFaithful_iff {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalSemiring A]
  [StarRing A] [Module 𝕜 A] (φ : Module.Dual 𝕜 A) :
    Module.Dual.IsFaithful φ ↔ Module.Dual.IsFaithful (Module.Dual.op φ) :=
by
  simp only [Module.Dual.IsFaithful, Module.Dual.op_apply, MulOpposite.unop_mul,
    MulOpposite.unop_star]
  refine ⟨λ h a => ?_, λ h a => ?_⟩
  . simpa [star_star, MulOpposite.unop_eq_zero_iff] using h (star a.unop)
  . simpa using h (star (MulOpposite.op a))

theorem QuantumSet.counit_op_isFaithful {A : Type*} [starAlgebra A] [QuantumSet A] :
  Module.Dual.IsFaithful (Coalgebra.counit (R := ℂ) (A := Aᵐᵒᵖ)) :=
(Module.Dual.op_isFaithful_iff _).mp QuantumSet.counit_isFaithful

noncomputable instance QuantumSet.tensorOp_self {A : Type*} [starAlgebra A] [QuantumSet A] [kms : Fact (k A = - (1 / 2))] :
  QuantumSet (A ⊗[ℂ] Aᵐᵒᵖ) :=
QuantumSet.tensorProduct (h := Fact.mk rfl)

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

@[simp]
theorem QuantumSet.subset_k {A : Type*} [starAlgebra A] [h : QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset h r
  k (QuantumSet.subset r A) = r :=
rfl

theorem MulOpposite.norm_eq {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  (x : Hᵐᵒᵖ) : ‖x‖ = ‖x.unop‖ :=
rfl

theorem QuantumGraph.real_iff {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔ f •ₛ f = f ∧ LinearMap.IsReal f :=
⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

noncomputable def QuantumSet.subset_tensor_algEquiv {A B : Type*} [starAlgebra A] [starAlgebra B] (r : ℝ) :
  (QuantumSet.subset r A ⊗[ℂ] QuantumSet.subset r B) ≃ₐ[ℂ] QuantumSet.subset r (A ⊗[ℂ] B) :=
(AlgEquiv.TensorProduct.map
  (QuantumSet.toSubset_algEquiv r).symm
  (QuantumSet.toSubset_algEquiv r).symm).trans
(QuantumSet.toSubset_algEquiv r)
theorem QuantumSet.subset_tensor_algEquiv_tmul {A B : Type*} [starAlgebra A] [starAlgebra B]
  (r : ℝ) (x : QuantumSet.subset r A) (y : QuantumSet.subset r B) :
  QuantumSet.subset_tensor_algEquiv r (x ⊗ₜ[ℂ] y)
    = QuantumSet.toSubset_algEquiv r
      ((QuantumSet.toSubset_algEquiv r).symm x ⊗ₜ[ℂ] (QuantumSet.toSubset_algEquiv r).symm y) :=
rfl
theorem QuantumSet.subset_tensor_algEquiv_symm_tmul {A B : Type*} [starAlgebra A] [starAlgebra B]
  (r : ℝ) (a : A) (b : B) :
  (QuantumSet.subset_tensor_algEquiv r).symm (QuantumSet.toSubset_algEquiv r (a ⊗ₜ[ℂ] b))
    = (QuantumSet.toSubset_algEquiv r)
      ((QuantumSet.toSubset_algEquiv r a) ⊗ₜ[ℂ] (QuantumSet.toSubset_algEquiv r b)) :=
rfl

theorem LinearMap.mul'_quantumSet_subset_eq {A : Type*} [starAlgebra A] [QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  letI : Fact (k A = k A) := Fact.mk rfl
  LinearMap.mul' ℂ (QuantumSet.subset r A) = (QuantumSet.toSubset_algEquiv r).toLinearMap
      ∘ₗ (LinearMap.mul' ℂ A)
      ∘ₗ (TensorProduct.map
        (QuantumSet.toSubset_algEquiv r).symm.toLinearMap
        (QuantumSet.toSubset_algEquiv r).symm.toLinearMap) :=
by
  ext x y
  simp [AlgEquiv.toLinearMap_apply, QuantumSet.subset_tensor_algEquiv_tmul]

set_option maxHeartbeats 300000 in
set_option synthInstance.maxHeartbeats 30000 in
theorem QuantumSet.subset_tensor_algEquiv_adjoint
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  [h : Fact (k A = k B)] (r : ℝ) :
  letI h1 := QuantumSet.instSubset (A := A) (by infer_instance) r;
  letI h2 := QuantumSet.instSubset (A := B) (by infer_instance) r;
  letI h3 := QuantumSet.tensorProduct (h := h);
  letI := QuantumSet.tensorProduct (hA := h1) (hB := h2) (h := Fact.mk rfl);
  letI := QuantumSet.instSubset (A := A ⊗[ℂ] B) h3 r;
    LinearMap.adjoint (QuantumSet.subset_tensor_algEquiv (A := A) (B := B) r).toLinearMap
    = (QuantumSet.subset_tensor_algEquiv r).symm.toLinearMap :=
by
  simp [QuantumSet.subset_tensor_algEquiv, LinearMap.adjoint_comp]
  letI h1 := QuantumSet.instSubset (A := A) (by infer_instance) r
  letI h2 := QuantumSet.instSubset (A := B) (by infer_instance) r
  letI h3 := QuantumSet.tensorProduct (h := h)
  letI := QuantumSet.tensorProduct (hA := h1) (hB := h2) (h := Fact.mk rfl)
  letI := QuantumSet.instSubset (A := A ⊗[ℂ] B) h3 r
  simp [TensorProduct.map_adjoint]
  simp only [QuantumSet.toSubset_algEquiv_symm_adjoint, QuantumSet.toSubset_algEquiv_adjoint r,
    modAut_tensor, QuantumSet.tensorProduct.k_eq₁, ← h.out,
    ← LinearMap.comp_assoc, AlgEquiv.TensorProduct.map_toLinearMap]
  simp only [← TensorProduct.map_comp, LinearMap.comp_assoc]
  simp only [AlgEquiv.coe_comp (e := modAut _), QuantumSet.modAut_trans]
  ring_nf
  simp only [QuantumSet.modAut_zero]
  rfl

theorem QuantumSet.comul_subset_eq {A : Type*} [starAlgebra A] [QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  letI : Fact (k A = k A) := Fact.mk rfl
  Coalgebra.comul (R := ℂ) (A := QuantumSet.subset r A)
    = (TensorProduct.map (QuantumSet.toSubset_algEquiv r).toLinearMap
        (QuantumSet.toSubset_algEquiv r).toLinearMap)
      ∘ₗ
    (Coalgebra.comul (R := ℂ) (A := A))
       ∘ₗ (toSubset_algEquiv r).symm.toLinearMap  :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  letI : Fact (k A = k A) := Fact.mk rfl
  letI hh := QuantumSet.tensorProduct (A := A) (B := A) (h := Fact.mk rfl)
  letI := QuantumSet.instSubset (A := A ⊗[ℂ] A) (by infer_instance) r
  simp only [Coalgebra.comul_eq_mul_adjoint, LinearMap.mul'_quantumSet_subset_eq]
  simp only [LinearMap.adjoint_comp, QuantumSet.subset_tensor_algEquiv_adjoint,
    TensorProduct.map_adjoint, toSubset_algEquiv_symm_adjoint, toSubset_algEquiv_adjoint]
  simp only [QuantumSet.tensorProduct.k_eq₁, ← LinearMap.comp_assoc]
  congr 1
  simp only [LinearMap.comp_assoc, ← Coalgebra.comul_eq_mul_adjoint,
    ← (QuantumSet.modAut_isCoalgHom _).2, TensorProduct.map_comp,
    ← AlgEquiv.TensorProduct.map_toLinearMap, ← modAut_tensor]
  congr 1
  rw [← LinearMap.comp_assoc]
  rw [AlgEquiv.coe_comp, modAut_trans]
  ring_nf
  simp only [QuantumSet.modAut_zero, AlgEquiv.one_toLinearMap, LinearMap.one_comp]

theorem AlgEquiv.refl_toLinearMap {A : Type*} [Semiring A] [Algebra ℂ A] :
  (AlgEquiv.refl (R := ℂ) (A₁ := A)).toLinearMap = LinearMap.id :=
rfl
theorem AlgEquiv.symm_comp_toLinearMap {A B : Type*} [Semiring A] [Semiring B] [Algebra ℂ A] [Algebra ℂ B]
  (e : A ≃ₐ[ℂ] B) :
  e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
by simp only [coe_comp, self_trans_symm]; rfl
theorem AlgEquiv.comp_symm_toLinearMap {A B : Type*} [Semiring A] [Semiring B] [Algebra ℂ A] [Algebra ℂ B]
  (e : A ≃ₐ[ℂ] B) :
  e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id :=
by simp only [coe_comp, symm_trans_self]; rfl

theorem schurMul_toSubsetQuantumSet {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
    {f : A →ₗ[ℂ] B} (r₁ r₂ : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r₁;
  letI := QuantumSet.instSubset (A := B) (by infer_instance) r₂;
  (f.toSubsetQuantumSet r₁ r₂ •ₛ f.toSubsetQuantumSet r₁ r₂) = (f •ₛ f).toSubsetQuantumSet r₁ r₂ :=
by
  simp
  simp only [QuantumSet.comul_subset_eq]
  nth_rw 2 [← LinearMap.comp_assoc]
  rw [← TensorProduct.map_comp, LinearMap.mul'_quantumSet_subset_eq]
  simp only [LinearMap.toSubsetQuantumSet, LinearMap.comp_assoc]
  simp only [← LinearMap.comp_assoc, ← TensorProduct.map_comp, AlgEquiv.symm_comp_toLinearMap,
    LinearMap.id_comp, LinearMap.comp_id]

theorem LinearMap.toSubsetQuantumSet_inj
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  {f g : A →ₗ[ℂ] B} (r₁ r₂ : ℝ) :
  f.toSubsetQuantumSet r₁ r₂ = g.toSubsetQuantumSet r₁ r₂ ↔ f = g :=
by rfl

theorem QuantumSet.toSubset_equiv_isReal {A : Type*} [Star A] (r : ℝ) :
  LinearMap.IsReal (QuantumSet.toSubset_equiv r (A := A)) :=
λ _ => rfl
theorem QuantumSet.toSubset_equiv_symm_isReal {A : Type*} [Star A] (r : ℝ) :
  LinearMap.IsReal (QuantumSet.toSubset_equiv r (A := A)).symm :=
λ _ => rfl

theorem LinearMap.toSubsetQuantumSet_isReal_iff
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  {f : A →ₗ[ℂ] B} (r₁ r₂ : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r₁;
  letI := QuantumSet.instSubset (A := B) (by infer_instance) r₂;
    LinearMap.IsReal (f.toSubsetQuantumSet r₁ r₂) ↔ LinearMap.IsReal f :=
by
  simp only [LinearMap.IsReal, LinearMap.toSubsetQuantumSet_apply,
    ← QuantumSet.toSubset_equiv_isReal (A := B) r₂ _,
    QuantumSet.toSubset_equiv_symm_isReal (A := _) r₁ _]
  rfl

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
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1)
  (gns : k A = 0) {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) :
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

lemma QuantumGraph.zero_le_degree_le_norm_one_sq_of_gns
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1) (gns : k A = 0)
  {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) (d : ℂ) (h2 : (h.toQuantumGraph).IsRegular d) :
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
          exact Real.innerOne_map_one_le_norm_one_pow_four_of_gns h₁ hδ h₂ gns h
  simp [inner_self_eq_norm_sq_to_K]

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

theorem comul_comp_mul_eq_iff_to_quantumSetSubset
  {A : Type*} [starAlgebra A] [QuantumSet A] {δ : ℂ} (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r;
  Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1
  ↔
  Coalgebra.comul ∘ₗ LinearMap.mul' ℂ (QuantumSet.subset r A) = δ • 1 :=
by
  simp [Coalgebra.comul_comp_mul_quantumSetSubset, ← AlgEquiv.TensorProduct.map_toLinearMap,
    AlgEquiv.comp_linearMap_eq_iff, AlgEquiv.linearMap_comp_eq_iff,
    LinearMap.comp_smul, LinearMap.smul_comp]
  simp only [LinearMap.comp_one, ← AlgEquiv.TensorProduct.map_symm, AlgEquiv.symm_symm,
    AlgEquiv.symm_comp_toLinearMap]
  rfl

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
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1)
  {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) (d : ℂ) (h2 : (h.toQuantumGraph).IsRegular d) :
    0 ≤ d ∧ d ≤ ‖(1 : A)‖ ^ 2 :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) 0
  rw [QuantumSet.normOne_toSubset 0]
  exact QuantumGraph.zero_le_degree_le_norm_one_sq_of_gns
    ((StarOrderedRing.nonneg_iff_toQuantumSetSubset 0).mp h₁) hδ
    ((comul_comp_mul_eq_iff_to_quantumSetSubset 0).mp h₂) rfl
    ((QuantumGraph.real_toSubset_iff 0).mpr h) _
    ((QuantumGraph.toSubset_isRegular_iff 0 h.toQuantumGraph d).mp h2)
