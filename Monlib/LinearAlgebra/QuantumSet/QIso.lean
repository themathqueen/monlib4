import Monlib.LinearAlgebra.QuantumSet.Basic

local notation "lT" => LinearMap.lTensor
local notation "rT" => LinearMap.rTensor

open scoped InnerProductSpace TensorProduct

variable {B₁ B₂ : Type*} [starAlgebra B₁] [starAlgebra B₂]
  [QuantumSet B₁] [QuantumSet B₂]

noncomputable abbrev QFun.map_unit' {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
P ∘ₗ (rT _ (Algebra.linearMap ℂ _))
  ∘ₗ (TensorProduct.lid ℂ _).symm.toLinearMap

noncomputable abbrev QFun.map_mul' {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
(lT _ (LinearMap.mul' ℂ B₂))
  ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap
  ∘ₗ (rT _ P)
  ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
  ∘ₗ (lT _ P)

noncomputable abbrev QFun.map_real' {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
(rT _ ((TensorProduct.lid ℂ _).toLinearMap
    ∘ₗ (rT _ (Coalgebra.counit ∘ₗ LinearMap.mul' ℂ _))
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap))
  ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
  ∘ₗ (lT B₁ (((LinearMap.rTensor B₂ (LinearMap.adjoint P)))
    ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap))
  ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap
  ∘ₗ (lT (B₁ ⊗[ℂ] H) ((Coalgebra.comul ∘ₗ Algebra.linearMap ℂ B₂)))
  ∘ₗ (TensorProduct.rid ℂ (B₁ ⊗[ℂ] H)).symm.toLinearMap

class QFun (H : Type*)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :
    Prop where
  map_unit : QFun.map_unit' P
    = (lT _ (Algebra.linearMap ℂ _)) ∘ₗ (TensorProduct.rid ℂ _).symm.toLinearMap
  map_mul : QFun.map_mul' P
    = P ∘ₗ (rT _ (LinearMap.mul' ℂ B₁))
        ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
  map_real : QFun.map_real' P = P

lemma TensorProduct.rid_symm_adjoint {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    LinearMap.adjoint (TensorProduct.rid 𝕜 E).symm.toLinearMap = (TensorProduct.rid 𝕜 E).toLinearMap :=
by rw [← LinearMap.adjoint_adjoint (TensorProduct.rid 𝕜 E).toLinearMap, TensorProduct.rid_adjoint]

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

set_option maxHeartbeats 600000 in
lemma QFun.adjoint_eq
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
  LinearMap.adjoint P =
    (TensorProduct.rid ℂ _).toLinearMap
      ∘ₗ (lT _ (Coalgebra.counit ∘ₗ LinearMap.mul' ℂ _))
      ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
      ∘ₗ (lT _ (((TensorProduct.assoc ℂ _ _ _).toLinearMap
        ∘ₗ (rT _ P))))
      ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap
      ∘ₗ (rT _ ((TensorProduct.assoc ℂ _ _ _).toLinearMap
        ∘ₗ (rT _ (Coalgebra.comul ∘ₗ Algebra.linearMap ℂ _))
        ∘ₗ (TensorProduct.lid ℂ _).symm.toLinearMap)) :=
by
  simp_rw [Coalgebra.comul_eq_mul_adjoint, Coalgebra.counit_eq_unit_adjoint]
  nth_rw 1 [← LinearMap.adjoint_adjoint (LinearMap.mul' ℂ B₂)]
  nth_rw 1 [← LinearMap.adjoint_adjoint (Algebra.linearMap ℂ B₁)]
  simp_rw [← LinearMap.adjoint_comp, ← LinearMap.lTensor_adjoint, ← LinearMap.rTensor_adjoint]
  simp_rw [← TensorProduct.lid_adjoint, ← TensorProduct.assoc_adjoint]
  nth_rw 4 [← TensorProduct.assoc_symm_adjoint]
  nth_rw 3 [← TensorProduct.assoc_symm_adjoint]
  simp_rw [← LinearMap.adjoint_comp, ← LinearMap.rTensor_adjoint]
  nth_rw 2 [← LinearMap.adjoint_adjoint P]
  rw [← LinearMap.rTensor_adjoint]
  nth_rw 2 [← TensorProduct.assoc_symm_adjoint]
  simp_rw [← LinearMap.adjoint_comp, ← LinearMap.lTensor_adjoint, ← LinearMap.adjoint_comp]
  rw [← TensorProduct.rid_symm_adjoint]
  simp only [← LinearMap.adjoint_comp]
  simp_rw [← Coalgebra.comul_eq_mul_adjoint, LinearMap.comp_assoc]
  nth_rw 1 [← hp.map_real]
  simp only [QFun.map_real', Coalgebra.counit_eq_unit_adjoint]
  congr <;> exact IsScalarTower.Algebra.ext_iff.mpr fun r ↦ congrFun rfl

noncomputable abbrev QFun.map_counit' (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
(TensorProduct.rid ℂ _).toLinearMap ∘ₗ (lT H Coalgebra.counit) ∘ₗ P

noncomputable abbrev QFun.map_comul' (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
(rT B₂ P)
  ∘ₗ (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
  ∘ₗ (lT B₁ P)
  ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap
  ∘ₗ (rT H Coalgebra.comul)

class QFun.qBijective
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
    Prop where
  map_counit : QFun.map_counit' P = (TensorProduct.lid ℂ H).toLinearMap ∘ₗ (rT H Coalgebra.counit)
  map_comul : QFun.map_comul' P
    = (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap ∘ₗ (lT H Coalgebra.comul) ∘ₗ P


section
variable {R : Type*} [CommSemiring R]

local notation "m" => LinearMap.mul' R
local notation "ϰ" => TensorProduct.assoc R
local notation "τ" => TensorProduct.lid R
local notation "τ'" => TensorProduct.rid R
local notation x " ⊗ₘ " y => TensorProduct.map x y

theorem LinearMap.comp_rid_eq_rid_comp_rTensor {M M₂ : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂] (f : M →ₗ[R] M₂) :
  f ∘ₗ (τ' M).toLinearMap = (τ' M₂).toLinearMap ∘ₗ (rT R f) :=
by ext; simp

theorem LinearMap.rTensor_lid_symm_comp_eq_assoc_symm_comp_lTensor_comp_lid_symm
  {M₁ M₂ M₃ M₄ : Type*}
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
  (f : M₁ ⊗[R] M₂ →ₗ[R] M₃ ⊗[R] M₄) :
  (rT M₄ (τ _).symm.toLinearMap) ∘ₗ f
    = (ϰ _ _ _).symm.toLinearMap ∘ₗ (lT _ f) ∘ₗ (τ _).symm.toLinearMap :=
by
  ext a b
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := R) (f (a ⊗ₜ[R] b))
  simp [hS, TensorProduct.sum_tmul, TensorProduct.tmul_sum]

theorem LinearMap.rTensor_tensor_eq_assoc_comp_rTensor_rTensor_comp_assoc_symm
  {A B C D : Type*} [AddCommMonoid A]
  [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  rT (B ⊗[R] C) x =
  (ϰ _ _ _).toLinearMap
    ∘ₗ rT C (rT B x)
    ∘ₗ (ϰ A B C).symm.toLinearMap :=
by
  rw [← TensorProduct.assoc_symm_comp_rTensor, ← LinearMap.comp_assoc,
    LinearEquiv.comp_coe, LinearEquiv.symm_trans_self]
  rfl
theorem LinearMap.rTensor_rTensor_eq_assoc_symm_comp_rTensor_comp_assoc
  {A B C D : Type*} [AddCommMonoid A]
  [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
  rT C (rT B x) = (ϰ _ _ _).symm.toLinearMap ∘ₗ (rT _ x) ∘ₗ (ϰ _ _ _).toLinearMap :=
by
  rw [rTensor_tensor_eq_assoc_comp_rTensor_rTensor_comp_assoc_symm]
  ext
  simp

theorem TensorProduct.lTensor_lTensor_comp_assoc {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
    lT B (lT C x) ∘ₗ (ϰ _ _ _).toLinearMap = (ϰ _ _ _).toLinearMap ∘ₗ lT _ x :=
by ext; simp

theorem LinearMap.rTensor_assoc_symm_comp_assoc_symm {A B C D : Type*} [AddCommMonoid A]
  [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] :
  rT D (ϰ A B C).symm.toLinearMap ∘ₗ (ϰ A (B ⊗[R] C) D).symm.toLinearMap
    = (ϰ (A ⊗[R] B) C D).symm.toLinearMap ∘ₗ (ϰ A B (C ⊗[R] D)).symm.toLinearMap
      ∘ₗ (lT A (ϰ B C D).toLinearMap) :=
by ext; simp

theorem rid_tensor {A B : Type*} [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B] :
  (τ' (TensorProduct R A B)).toLinearMap = lT A (τ' B).toLinearMap ∘ₗ (ϰ A B R).toLinearMap :=
by ext; simp

theorem FrobeniusAlgebra.snake_equation_2 {A : Type*} [Semiring A] [FrobeniusAlgebra R A] :
  (τ' _).toLinearMap ∘ₗ (lT _ (Coalgebra.counit ∘ₗ LinearMap.mul' R _))
    ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ (rT _ (Coalgebra.comul ∘ₗ Algebra.linearMap R _))
    ∘ₗ (τ A).symm.toLinearMap
  = 1 :=
by
  nth_rw 2 [← LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  nth_rw 2 [LinearMap.comp_assoc]
  rw [lTensor_counit_mul_comp_rTensor_comul_unit]
  ext
  simp

end

local notation "ϰ" => TensorProduct.assoc ℂ
local notation "τ" => TensorProduct.lid ℂ
local notation "τ'" => TensorProduct.rid ℂ
local notation "η" => Algebra.linearMap ℂ

theorem QFun.self_comp_adjoint_eq_id_of_map_comul
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P)
  (h : QFun.map_comul' P = (ϰ _ _ _).symm.toLinearMap ∘ₗ (lT H Coalgebra.comul) ∘ₗ P) :
  P ∘ₗ LinearMap.adjoint P = 1 :=
by
  rw [QFun.adjoint_eq hp]
  simp only [← LinearMap.comp_assoc]
  rw [LinearMap.comp_rid_eq_rid_comp_rTensor]
  simp only [LinearMap.comp_assoc, rTensor_comp_lTensor']
  rw [LinearMap.rTensor_tensor_eq_assoc_comp_rTensor_rTensor_comp_assoc_symm]
  simp only [LinearMap.rTensor_comp, LinearMap.lTensor_comp, LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ _ (ϰ (B₁ ⊗[ℂ] H) _ _).symm.toLinearMap]
  rw [← LinearMap.comp_assoc (lT B₁ (rT B₂ P) ∘ₗ _ ∘ₗ _ ∘ₗ _ ∘ₗ _),
    LinearMap.comp_assoc (lT _ _) _ _]
  rw [← LinearMap.rTensor_assoc_symm_comp_assoc_symm]
  rw [← LinearMap.comp_assoc _ _ (rT B₂ (rT _ _)),
    ← LinearMap.comp_assoc _ _ (rT B₂ (rT _ _)),
    ← LinearMap.rTensor_comp]
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (ϰ _ _ _).symm.toLinearMap]
  rw [← TensorProduct.rTensor_lTensor_comp_assoc_symm,
    LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (ϰ _ _ _).symm.toLinearMap,
    LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
    LinearEquiv.refl_toLinearMap, LinearMap.id_comp]
  simp only [LinearMap.comp_assoc, ← LinearMap.rTensor_comp]
  simp only [← LinearMap.comp_assoc] at h ⊢
  rw [h]
  simp only [LinearMap.comp_assoc, hp.1]
  rw [← LinearMap.comp_assoc _ _ (lT (H ⊗[ℂ] B₂) _),
    ← LinearMap.lTensor_comp, ← LinearMap.comp_assoc _ _ (lT H _),
    ← LinearMap.lTensor_comp, ← LinearMap.comp_assoc _ _ (lT _ _)]
  ext a b
  simp
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := ℂ) (Coalgebra.comul (1 : B₂))
  rw [hS]
  simp [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  simp_rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
  congr
  simp_rw [← TensorProduct.rid_tmul,
    ← LinearMap.mul'_apply (R := ℂ) (A := B₂), ← LinearMap.comp_apply,
    ← LinearMap.lTensor_tmul, ← TensorProduct.assoc_tmul,
    ← LinearEquiv.coe_toLinearMap, ← map_sum]
  rw [← TensorProduct.sum_tmul, ← hS]
  have := @FrobeniusAlgebra.lTensor_counit_mul_comp_rTensor_comul_unit (R := ℂ) (A := B₂)
    _ _ (QuantumSet.isFrobeniusAlgebra (A := B₂))
  simp only [TensorProduct.ext_iff', LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, LinearMap.lTensor_tmul,
    Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one] at this
  specialize this 1
  simp only [map_smul, one_smul] at this
  simp [this]

set_option maxHeartbeats 300000 in
theorem QFun.adjoint_comp_self_eq_id_of_map_counit
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P)
  (h : QFun.map_counit' P = (τ H).toLinearMap ∘ₗ (rT H Coalgebra.counit)) :
  LinearMap.adjoint P ∘ₗ P = 1 :=
by
  rw [QFun.adjoint_eq hp]
  simp only [LinearMap.rTensor_comp, LinearMap.lTensor_comp, LinearMap.comp_assoc]
  rw [LinearMap.rTensor_lid_symm_comp_eq_assoc_symm_comp_lTensor_comp_lid_symm,
    ← LinearMap.comp_assoc (_ ∘ₗ (τ _).symm.toLinearMap) _ (rT _ (rT _ _)),
    ← TensorProduct.assoc_symm_comp_rTensor]
  simp only [LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ (ϰ B₁ H B₂).symm.toLinearMap,
    ← TensorProduct.assoc_symm_comp_rTensor,
    ← LinearMap.comp_assoc _ _ (rT _ (η B₁)),
    LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
  simp only [LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc (_ ∘ₗ _) (lT B₁ P) (rT (H ⊗[ℂ] B₂) _),
    LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
  have :
    (ϰ B₁ (B₁ ⊗[ℂ] H) B₂).toLinearMap
        ∘ₗ rT B₂ (ϰ B₁ B₁ H).toLinearMap
        ∘ₗ (ϰ (B₁ ⊗[ℂ] B₁) H B₂).symm.toLinearMap
    = lT _ (ϰ _ _ _).symm.toLinearMap ∘ₗ (ϰ _ _ _).toLinearMap :=
  by
    apply TensorProduct.ext_fourfold'
    intro a b c d
    simp
  calc (τ' (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ lT (B₁ ⊗[ℂ] H) Coalgebra.counit
        ∘ₗ lT (B₁ ⊗[ℂ] H) (LinearMap.mul' ℂ B₂)
        ∘ₗ (ϰ B₁ H (B₂ ⊗[ℂ] B₂)).symm.toLinearMap
        ∘ₗ lT B₁ (ϰ H B₂ B₂).toLinearMap
        ∘ₗ lT B₁ (rT B₂ P)
        ∘ₗ (ϰ B₁ (B₁ ⊗[ℂ] H) B₂).toLinearMap
        ∘ₗ rT B₂ (ϰ B₁ B₁ H).toLinearMap
        ∘ₗ (ϰ (B₁ ⊗[ℂ] B₁) H B₂).symm.toLinearMap
        ∘ₗ lT (B₁ ⊗[ℂ] B₁) P
        ∘ₗ rT (B₁ ⊗[ℂ] H) Coalgebra.comul
        ∘ₗ rT (B₁ ⊗[ℂ] H) (η B₁) ∘ₗ (τ (B₁ ⊗[ℂ] H)).symm.toLinearMap
      = (τ' (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ lT (B₁ ⊗[ℂ] H) Coalgebra.counit
        ∘ₗ ((ϰ _ _ _).symm.toLinearMap ∘ₗ lT _ (lT _ (LinearMap.mul' ℂ B₂)))
          ∘ₗ (lT _ ((ϰ H _ _).toLinearMap ∘ₗ rT B₂ P))
          ∘ₗ (lT _ (ϰ _ _ _).symm.toLinearMap ∘ₗ (ϰ _ _ _).toLinearMap)
          ∘ₗ lT _ P
        ∘ₗ rT (B₁ ⊗[ℂ] H) Coalgebra.comul
        ∘ₗ rT (B₁ ⊗[ℂ] H) (η B₁) ∘ₗ (τ (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
        rw [TensorProduct.assoc_symm_comp_lTensor_lTensor, ← this]
        simp only [LinearMap.lTensor_comp, LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ = (τ' (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ lT (B₁ ⊗[ℂ] H) Coalgebra.counit
        ∘ₗ (ϰ _ _ _).symm.toLinearMap
        ∘ₗ lT _ (lT _ (LinearMap.mul' ℂ B₂) ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ rT _ P
          ∘ₗ (ϰ _ _ _).symm.toLinearMap)
        ∘ₗ (lT _ (lT _ P) ∘ₗ (ϰ _ _ _).toLinearMap)
        ∘ₗ rT (B₁ ⊗[ℂ] H) Coalgebra.comul
        ∘ₗ rT (B₁ ⊗[ℂ] H) (η B₁) ∘ₗ (τ (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
        rw [TensorProduct.lTensor_lTensor_comp_assoc]
        simp only [LinearMap.lTensor_comp, LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ = (τ' (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ lT (B₁ ⊗[ℂ] H) Coalgebra.counit
        ∘ₗ (ϰ _ _ _).symm.toLinearMap
        ∘ₗ lT _ (lT _ (LinearMap.mul' ℂ B₂) ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ rT _ P
          ∘ₗ (ϰ _ _ _).symm.toLinearMap ∘ₗ lT _ P)
        ∘ₗ (ϰ _ _ _).toLinearMap
        ∘ₗ rT (B₁ ⊗[ℂ] H) Coalgebra.comul
        ∘ₗ rT (B₁ ⊗[ℂ] H) (η B₁) ∘ₗ (τ (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
        simp only [LinearMap.lTensor_comp, LinearMap.comp_assoc]
    _ = (τ' (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ (lT (B₁ ⊗[ℂ] H) Coalgebra.counit
        ∘ₗ (ϰ _ _ _).symm.toLinearMap)
        ∘ₗ lT _ (P ∘ₗ (rT _ (LinearMap.mul' ℂ B₁)) ∘ₗ (ϰ _ _ _).symm.toLinearMap)
        ∘ₗ (ϰ _ _ _).toLinearMap
        ∘ₗ rT (B₁ ⊗[ℂ] H) Coalgebra.comul
        ∘ₗ rT (B₁ ⊗[ℂ] H) (η B₁) ∘ₗ (τ (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
        simp only [hp.map_mul, LinearMap.comp_assoc]
    _ = lT _ (τ' _).toLinearMap ∘ₗ ((ϰ _ _ _).toLinearMap ∘ₗ (ϰ _ _ _).symm.toLinearMap)
        ∘ₗ lT _ (lT _ Coalgebra.counit ∘ₗ P ∘ₗ (rT _ (LinearMap.mul' ℂ B₁)) ∘ₗ (ϰ _ _ _).symm.toLinearMap)
        ∘ₗ (ϰ _ _ _).toLinearMap
        ∘ₗ rT (B₁ ⊗[ℂ] H) (Coalgebra.comul ∘ₗ η B₁)
        ∘ₗ (τ (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
        simp only [← TensorProduct.assoc_symm_comp_lTensor_lTensor, rid_tensor,
          LinearMap.lTensor_comp, LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ = lT _ (((τ' _).toLinearMap ∘ₗ lT _ Coalgebra.counit ∘ₗ P)
          ∘ₗ (rT _ (LinearMap.mul' ℂ B₁)) ∘ₗ (ϰ _ _ _).symm.toLinearMap)
        ∘ₗ (ϰ _ _ _).toLinearMap
        ∘ₗ rT (B₁ ⊗[ℂ] H) (Coalgebra.comul ∘ₗ η B₁)
        ∘ₗ (τ (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
        simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
          LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.lTensor_comp,
          LinearMap.comp_assoc]
    _ = lT _ (((τ H).toLinearMap ∘ₗ (rT H Coalgebra.counit))
          ∘ₗ (rT _ (LinearMap.mul' ℂ B₁)) ∘ₗ (ϰ _ _ _).symm.toLinearMap)
        ∘ₗ (ϰ _ _ _).toLinearMap
        ∘ₗ rT (B₁ ⊗[ℂ] H) (Coalgebra.comul ∘ₗ η B₁)
        ∘ₗ (τ (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by simp [h]
    _ = rT H ((τ' _).toLinearMap ∘ₗ (lT _ (Coalgebra.counit ∘ₗ LinearMap.mul' ℂ _))
        ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ (rT _ (Coalgebra.comul ∘ₗ η _))
        ∘ₗ (τ _).symm.toLinearMap) :=
      by
        ext
        obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := ℂ) (Coalgebra.comul (1 : B₁))
        simp
        rw [hS]
        simp [TensorProduct.sum_tmul, map_sum, TensorProduct.smul_tmul]
    _ = rT H 1 :=
      by rw [@FrobeniusAlgebra.snake_equation_2 ℂ _ B₁ _
        (QuantumSet.isFrobeniusAlgebra (A := B₁))]
    _ = 1 := by ext; simp

theorem QFun.map_counit_of_adjoint_comp_self_eq_id
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) (h : LinearMap.adjoint P ∘ₗ P = 1) :
  map_counit' P = (τ H).toLinearMap ∘ₗ (rT H Coalgebra.counit) :=
by
  have :=
    calc LinearMap.adjoint P ∘ₗ (lT H (η B₂) ∘ₗ (τ' H).symm.toLinearMap)
          = LinearMap.adjoint P ∘ₗ (P ∘ₗ rT H (η _) ∘ₗ (τ H).symm.toLinearMap) :=
            by rw [← hp.map_unit]
        _ = rT H (η _) ∘ₗ (τ H).symm.toLinearMap :=
            by rw [← LinearMap.comp_assoc, h, LinearMap.one_comp]
  apply_fun LinearMap.adjoint at this
  simp only [LinearMap.adjoint_comp, LinearMap.lTensor_adjoint, LinearMap.rTensor_adjoint,
    ← TensorProduct.rid_adjoint, Coalgebra.counit_eq_unit_adjoint, LinearMap.adjoint_adjoint,
    ← TensorProduct.lid_adjoint, LinearMap.comp_assoc] at this
  rw [← sub_eq_zero] at this ⊢
  simp only [map_counit', Coalgebra.counit_eq_unit_adjoint]
  simp [← this]
  congr <;> ext <;> simp

lemma LinearMap.lTensor_one {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂] :
  lT M₁ (1 : M₂ →ₗ[R] M₂) = 1 :=
by ext; simp
lemma LinearMap.rTensor_one {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂] :
  rT M₁ (1 : M₂ →ₗ[R] M₂) = 1 :=
by ext; simp

set_option maxHeartbeats 300000 in
theorem QFun.map_comul_of_inv_eq_adjoint
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) (h₁ : P ∘ₗ LinearMap.adjoint P = 1)
  (h₂ : LinearMap.adjoint P ∘ₗ P = 1) :
    map_comul' P = (ϰ _ _ _).symm.toLinearMap ∘ₗ (lT H Coalgebra.comul) ∘ₗ P :=
by
  have : LinearMap.adjoint P ∘ₗ map_mul' P ∘ₗ (lT B₁ (LinearMap.adjoint P))
    ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ (rT B₂ (LinearMap.adjoint P)) = LinearMap.adjoint (map_comul' P) :=
  by
    rw [hp.map_mul]
    simp_rw [← LinearMap.comp_assoc, h₂, LinearMap.one_comp, ← LinearMap.lTensor_adjoint,
      ← LinearMap.rTensor_adjoint, Coalgebra.comul_eq_mul_adjoint]
    rw [← TensorProduct.assoc_adjoint]
    nth_rw 2 [← TensorProduct.assoc_symm_adjoint]
    nth_rw 1 [← LinearMap.adjoint_adjoint (LinearMap.mul' ℂ B₁)]
    rw [← LinearMap.rTensor_adjoint]
    simp only [← LinearMap.adjoint_comp, LinearMap.comp_assoc]
  simp_all [map_mul', LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ _ (lT B₁ P), ← LinearMap.lTensor_comp, h₁, LinearMap.lTensor_one,
    LinearMap.one_comp, ← LinearMap.comp_assoc _ _ (ϰ _ _ _).symm.toLinearMap,
    LinearEquiv.comp_coe, LinearEquiv.self_trans_symm] at this
  simp only [LinearEquiv.refl_toLinearMap] at this
  rw [LinearMap.id_comp, ← LinearMap.rTensor_comp, h₁, LinearMap.rTensor_one, LinearMap.comp_one] at this
  apply_fun LinearMap.adjoint at this
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] at this
  rw [← this, ← TensorProduct.assoc_adjoint, Coalgebra.comul_eq_mul_adjoint,
    ← LinearMap.lTensor_adjoint, ← LinearMap.comp_assoc, ← LinearMap.adjoint_comp]

theorem QFun.qBijective_iff_inv_eq_adjoint
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
  hp.qBijective ↔ P ∘ₗ LinearMap.adjoint P = 1 ∧ LinearMap.adjoint P ∘ₗ P = 1 :=
⟨λ h => ⟨hp.self_comp_adjoint_eq_id_of_map_comul h.2,
  hp.adjoint_comp_self_eq_id_of_map_counit h.1⟩,
  λ ⟨h1, h2⟩ => ⟨hp.map_counit_of_adjoint_comp_self_eq_id h2,
  hp.map_comul_of_inv_eq_adjoint h1 h2⟩⟩

noncomputable def QFun.qBijective.toLinearEquiv
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P]
  (h : hp.qBijective) :
    (B₁ ⊗[ℂ] H) ≃ₗ[ℂ] (H ⊗[ℂ] B₂) where
  toLinearMap := P
  invFun := LinearMap.adjoint P
  left_inv _ := by
    simp only [LinearMap.toFun_eq_coe, ← LinearMap.comp_apply]
    rw [(hp.qBijective_iff_inv_eq_adjoint.mp h).2, LinearMap.one_apply]
  right_inv _ := by
    simp only [LinearMap.toFun_eq_coe, ← LinearMap.comp_apply]
    rw [(hp.qBijective_iff_inv_eq_adjoint.mp h).1, LinearMap.one_apply]

lemma QFun.qBijective.toLinearEquiv_toLinearMap
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P]
  (h : hp.qBijective) :
    h.toLinearEquiv.toLinearMap = P :=
rfl

lemma QFun.qBijective.toLinearEquiv_symm_toLinearMap
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P]
  (h : hp.qBijective) :
    h.toLinearEquiv.symm.toLinearMap = LinearMap.adjoint P :=
rfl

theorem QFun.qBijective_iso_id
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P] (h : hp.qBijective) :
    h.toLinearEquiv.toLinearMap ∘ₗ
      (rT _ 1) ∘ₗ h.toLinearEquiv.symm.toLinearMap = lT _ 1 :=
by
  ext
  simp [LinearMap.rTensor_one, LinearMap.lTensor_one]

theorem rankOne_one_one_eq :
  ContinuousLinearMap.toLinearMap (rankOne ℂ (1 : B₁) (1 : B₂)) = η B₁ ∘ₗ Coalgebra.counit :=
by
  rw [Coalgebra.counit_eq_bra_one]
  ext
  simp [Algebra.algebraMap_eq_smul_one]

lemma QFun.map_unit'' {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
  P ∘ₗ rT H (η B₁) = lT H (η B₂) ∘ₗ (TensorProduct.comm ℂ _ _).toLinearMap :=
calc P ∘ₗ rT H (η B₁) = lT H (η B₂) ∘ₗ ((τ' _).symm.toLinearMap ∘ₗ (τ _).toLinearMap) :=
    by
      rw [← LinearMap.comp_assoc, ← hp.map_unit, map_unit']
      simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm]
      rfl
  _ = lT H (η B₂) ∘ₗ (TensorProduct.comm ℂ _ _).toLinearMap := by ext; simp

lemma QFun.counit_map_adjoint {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
  (rT _ Coalgebra.counit) ∘ₗ LinearMap.adjoint P
    = (TensorProduct.comm ℂ _ _).symm.toLinearMap ∘ₗ lT _ Coalgebra.counit :=
calc (rT _ Coalgebra.counit) ∘ₗ LinearMap.adjoint P
    = LinearMap.adjoint (P ∘ₗ (rT _ (η B₁))) :=
      by
        rw [Coalgebra.counit_eq_unit_adjoint, ← LinearMap.rTensor_adjoint,
          LinearMap.adjoint_comp]
        congr; ext; rfl
  _ = LinearMap.adjoint (lT H (η B₂) ∘ₗ (TensorProduct.comm ℂ _ _).toLinearMap) :=
      by rw [hp.map_unit'']
  _ = (TensorProduct.comm ℂ _ _).symm.toLinearMap ∘ₗ lT _ Coalgebra.counit :=
      by
        rw [LinearMap.adjoint_comp, LinearMap.lTensor_adjoint,
          Coalgebra.counit_eq_unit_adjoint, TensorProduct.comm_adjoint]
        congr; ext; rfl

/-- for any `qBijective` function `P`,
  we get `P ∘ (|1⟩⟨1| ⊗ id) ∘ adjoint P = (id ⊗ |1⟩⟨1|)`. -/
theorem QFun.qBijective_iso_rankOne_one_one
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P] (h : hp.qBijective) :
    h.toLinearEquiv.toLinearMap ∘ₗ (rT _ (rankOne ℂ (1 : B₁) (1 : B₁))) ∘ₗ h.toLinearEquiv.symm.toLinearMap
      = lT _ (rankOne ℂ (1 : B₂) (1 : B₂)) :=
by
  rw [rankOne_one_one_eq, LinearMap.rTensor_comp,
    h.toLinearEquiv_toLinearMap, h.toLinearEquiv_symm_toLinearMap,
    LinearMap.comp_assoc, hp.counit_map_adjoint, ← LinearMap.comp_assoc, hp.map_unit'']
  nth_rw 1 [LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  rw [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp, ← LinearMap.lTensor_comp, rankOne_one_one_eq]
