import Monlib.LinearAlgebra.QuantumSet.SchurMul
import Monlib.LinearAlgebra.QuantumSet.Symm
import Monlib.LinearAlgebra.tensorProduct
import Monlib.LinearAlgebra.Ips.MinimalProj
import Monlib.LinearAlgebra.PosMap_isReal

local notation x " ⊗ₘ " y => TensorProduct.map x y

theorem symmMap_apply_schurMul {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
    [hA : QuantumSet A] [QuantumSet B] (f g : A →ₗ[ℂ] B) :
  symmMap ℂ _ _ (f •ₛ g) = (symmMap _ _ _ g) •ₛ (symmMap _ _ _ f) :=
by
  rw [symmMap_apply, schurMul_real, schurMul_adjoint]
  rfl

@[simps]
def LinearMap.op {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : M →ₛₗ[σ] M₂) : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ where
    toFun x := MulOpposite.op (f (MulOpposite.unop x))
    map_add' _ _ := by simp only [MulOpposite.unop_add, map_add, MulOpposite.op_add]
    map_smul' _ _ := by simp only [MulOpposite.unop_smul, LinearMap.map_smulₛₗ, MulOpposite.op_smul]
@[simps]
def LinearMap.unop {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ) : M →ₛₗ[σ] M₂ where
    toFun x := MulOpposite.unop (f (MulOpposite.op x))
    map_add' _ _ := by simp only [MulOpposite.unop_add, map_add, MulOpposite.op_add]
    map_smul' _ _ := by simp only [MulOpposite.unop_smul, LinearMap.map_smulₛₗ, MulOpposite.op_smul]
@[simp]
lemma LinearMap.unop_op {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ) :
  f.unop.op = f :=
rfl
@[simp]
lemma LinearMap.op_unop {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : M →ₛₗ[σ] M₂) :
  f.op.unop = f :=
rfl


theorem Psi_apply_linearMap_comp_linearMap_of_commute_modAut {A B C D : Type*}
  [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [NormedAddCommGroupOfRing C] [NormedAddCommGroupOfRing D]
  [hA : QuantumSet A] [hB : QuantumSet B]
  [hC : QuantumSet C] [hD : QuantumSet D]
  {f : A →ₗ[ℂ] B} {g : D →ₗ[ℂ] C}
  (t r : ℝ)
  (hf : (hB.modAut t).toLinearMap.comp f = f.comp (hA.modAut t).toLinearMap)
  (hg : (hC.modAut r).toLinearMap.comp g = g.comp (hD.modAut r).toLinearMap)
  (x : C →ₗ[ℂ] A) :
  QuantumSet.Psi t r (f ∘ₗ x ∘ₗ g)
    = (f ⊗ₘ ((symmMap ℂ _ _).symm g).op) (QuantumSet.Psi t r x) :=
by
  apply_fun LinearMap.adjoint at hg
  simp_rw [LinearMap.adjoint_comp, ← LinearMap.star_eq_adjoint,
    isSelfAdjoint_iff.mp (QuantumSet.modAut_isSelfAdjoint _)] at hg
  have : ∀ a b, QuantumSet.Psi t r (f ∘ₗ (rankOne ℂ a b).toLinearMap ∘ₗ g)
    = (f ⊗ₘ ((symmMap ℂ _ _).symm g).op) (QuantumSet.Psi t r (rankOne ℂ a b).toLinearMap) := λ _ _ => by
    simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] at hf hg
    simp only [symmMap_symm_apply,
      QuantumSet.Psi_apply, LinearMap.rankOne_comp, LinearMap.comp_rankOne,
      QuantumSet.Psi_toFun_apply, TensorProduct.map_tmul,
      QuantumSet.modAut_star, LinearMap.real_apply,
      LinearMap.op_apply, MulOpposite.unop_star,
      MulOpposite.unop_op, neg_neg, star_star,
      ← MulOpposite.op_star, ← hf, ← hg, QuantumSet.modAut_star]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp only [LinearMap.comp_sum, LinearMap.sum_comp, map_sum, this]

theorem symmMap_symm_comp {A B C : Type*} [NormedAddCommGroupOfRing A]
  [NormedAddCommGroupOfRing B] [hA : QuantumSet A] [hB : QuantumSet B]
  [NormedAddCommGroupOfRing C] [QuantumSet C]
  (x : A →ₗ[ℂ] B) (y : C →ₗ[ℂ] A) :
  (symmMap ℂ _ _).symm (x ∘ₗ y) = (symmMap ℂ _ _).symm y ∘ₗ (symmMap ℂ _ _).symm x :=
by
  simp only [symmMap_symm_apply, LinearMap.adjoint_comp, LinearMap.real_comp]

theorem linearMap_map_Psi_of_commute_modAut {A B C D : Type*}
  [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [NormedAddCommGroupOfRing C] [NormedAddCommGroupOfRing D]
  [hA : QuantumSet A] [hB : QuantumSet B]
  [hC : QuantumSet C] [hD : QuantumSet D]
  {f : A →ₗ[ℂ] B} {g : Cᵐᵒᵖ →ₗ[ℂ] Dᵐᵒᵖ}
  (t r : ℝ)
  (hf : (hB.modAut t).toLinearMap.comp f = f.comp (hA.modAut t).toLinearMap)
  (hg : (hD.modAut r).toLinearMap.comp g.unop = g.unop.comp (hC.modAut r).toLinearMap)
  (x : C →ₗ[ℂ] A) :
  (f ⊗ₘ g) (QuantumSet.Psi t r x) = QuantumSet.Psi t r (f ∘ₗ x ∘ₗ ((symmMap ℂ _ _) g.unop)) :=
by
  rw [Psi_apply_linearMap_comp_linearMap_of_commute_modAut,
    LinearEquiv.symm_apply_apply, LinearMap.unop_op]
  . exact hf
  . apply_fun (symmMap ℂ _ _).symm using LinearEquiv.injective _
    simp_rw [symmMap_symm_comp, LinearEquiv.symm_apply_apply,
      symmMap_symm_apply, ← LinearMap.star_eq_adjoint,
      isSelfAdjoint_iff.mp (QuantumSet.modAut_isSelfAdjoint _),
      QuantumSet.modAut_real, AlgEquiv.linearMap_comp_eq_iff, QuantumSet.modAut_symm,
      neg_neg, LinearMap.comp_assoc, ← hg, ← QuantumSet.modAut_symm,
      ← AlgEquiv.comp_linearMap_eq_iff]

lemma schurIdempotent_iff_Psi_isIdempotentElem {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
    [hA : QuantumSet A] [QuantumSet B] (f : A →ₗ[ℂ] B) (t r : ℝ) :
  f •ₛ f = f ↔ IsIdempotentElem (hA.Psi t r f) :=
by
  simp_rw [IsIdempotentElem, ← Psi.schurMul, Function.Injective.eq_iff (LinearEquiv.injective _)]

@[simp]
theorem AlgEquiv.op_toLinearMap
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B] (f : A ≃ₐ[R] B) :
  f.op.toLinearMap = f.toLinearMap.op :=
rfl
@[simp]
theorem LinearMap.op_real {K E F : Type*}
  [AddCommMonoid E] [StarAddMonoid E] [AddCommMonoid F] [StarAddMonoid F]
  [Semiring K] [Module K E] [Module K F] [InvolutiveStar K] [StarModule K E]  [StarModule K F]
  (φ : E →ₗ[K] F) :
  φ.op.real = φ.real.op :=
rfl

lemma modAut_map_comp_Psi {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
    [hA : QuantumSet A] [hB : QuantumSet B] (t₁ r₁ t₂ r₂ : ℝ) :
  ((hB.modAut t₁).toLinearMap ⊗ₘ ((hA.modAut r₁).op.toLinearMap)) ∘ₗ (hA.Psi t₂ r₂).toLinearMap
    = (hA.Psi (t₁ + t₂) (-r₁ + r₂)).toLinearMap :=
by
  apply LinearMap.ext_of_rank_one'
  intro _ _
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [linearMap_map_Psi_of_commute_modAut, AlgEquiv.op_toLinearMap,
    LinearMap.op_unop, symmMap_apply, LinearMap.rankOne_comp',
    LinearMap.comp_rankOne]
  simp_rw [AlgEquiv.toLinearMap_apply, QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply,
    QuantumSet.modAut_real, AlgEquiv.toLinearMap_apply, QuantumSet.modAut_apply_modAut, add_comm]
  all_goals
    ext
    simp only [AlgEquiv.op_toLinearMap, LinearMap.op_unop,
      LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      QuantumSet.modAut_apply_modAut, add_comm]

open scoped TensorProduct

lemma isReal_iff_Psi {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
    [hA : QuantumSet A] [hB : QuantumSet B] (f : A →ₗ[ℂ] B) (t r : ℝ) :
  LinearMap.IsReal f ↔ star (hA.Psi t r f) = hA.Psi (-t) (1 - r) f :=
by
  simp_rw [LinearMap.isReal_iff, ← Function.Injective.eq_iff (hA.Psi t r).injective,
    Psi.real_apply]
  nth_rw 1 [← Function.Injective.eq_iff
    (AlgEquiv.TensorProduct.map (hB.modAut (- (2 * t)))
      (AlgEquiv.op (hA.modAut (2 * r - 1)))).injective]
  simp_rw [← AlgEquiv.TensorProduct.map_toLinearMap, AlgEquiv.toLinearMap_apply,
    AlgEquiv.TensorProduct.map_map_toLinearMap, AlgEquiv.op_trans,
    QuantumSet.modAut_trans]
  simp only [add_right_neg, QuantumSet.modAut_zero, sub_add_sub_cancel, sub_self,
    AlgEquiv.op_one, AlgEquiv.TensorProduct.map_one, AlgEquiv.one_apply]
  simp only [← LinearEquiv.coe_toLinearMap, ← AlgEquiv.toLinearMap_apply,
    ← LinearMap.comp_apply, AlgEquiv.TensorProduct.map_toLinearMap, modAut_map_comp_Psi,
    two_mul, neg_add, neg_sub, sub_add]
  norm_num

lemma isReal_iff_Psi_isSelfAdjoint {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
    [hA : QuantumSet A] [hB : QuantumSet B] (f : A →ₗ[ℂ] B) :
  LinearMap.IsReal f ↔ IsSelfAdjoint (hA.Psi 0 (1 / 2) f) :=
by
  rw [_root_.IsSelfAdjoint, isReal_iff_Psi f 0 (1 / 2)]
  norm_num

class schurProjection {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [hA : QuantumSet A] [hB : QuantumSet B] (f : A →ₗ[ℂ] B) :
    Prop :=
  isIdempotentElem : f •ₛ f = f
  isReal : LinearMap.IsReal f

structure isEquivToPiMat (A : Type*) [Add A] [Mul A] [Star A] [SMul ℂ A] :=
  n : Type*
  hn₁ : Fintype n
  hn₂ : DecidableEq n
  k : n → Type*
  hk₁ : Π i, Fintype (k i)
  hk₂ : Π i, DecidableEq (k i)
  φ : A ≃⋆ₐ[ℂ] PiMat ℂ n k
attribute [instance] isEquivToPiMat.hn₁
attribute [instance] isEquivToPiMat.hn₂
attribute [instance] isEquivToPiMat.hk₁
attribute [instance] isEquivToPiMat.hk₂

open scoped ComplexOrder
def schurProjection.isPosMap {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [hA : QuantumSet A] [hB : QuantumSet B] [PartialOrder A] [PartialOrder B]
  [StarOrderedRing B]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1)
  -- (hh : isEquivToPiMat A)
  {f : A →ₗ[ℂ] B}
  (hf : schurProjection f) :
  LinearMap.IsPosMap f :=
by
  revert hf
  rintro ⟨h1, h2⟩ x hx
  obtain ⟨a, b, rfl⟩ := h₁.mp hx
  rw [← h1, ← @LinearMap.mul'_apply ℂ, schurMul_apply_apply]
  simp_rw [← LinearMap.comp_apply, LinearMap.comp_assoc, h₂,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.one_apply,
    map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply, h2 a]
  have : δ = Real.sqrt (RCLike.re δ) * Real.sqrt (RCLike.re δ) :=
  by
    simp only [← Complex.ofReal_mul, ← Real.sqrt_mul' _ (RCLike.nonneg_def'.mp hδ).2,
      Real.sqrt_mul_self (RCLike.nonneg_def'.mp hδ).2]
    exact (RCLike.nonneg_def'.mp hδ).1.symm
  have : δ • (star (f a) * f a) = star (f ((Real.sqrt (RCLike.re δ) : ℂ) • a)) *
    f ((Real.sqrt (RCLike.re δ) : ℂ) • a) :=
  by
    rw [map_smul, star_smul, smul_mul_smul, RCLike.star_def, Complex.conj_ofReal, ← this]
  rw [this]
  exact star_mul_self_nonneg _

def schurIdempotent.isSchurProjection_iff_isPosMap {A B : Type*}
  [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [QuantumSet A] [QuantumSet B] [PartialOrder A] [PartialOrder B]
  [StarOrderedRing A] [StarOrderedRing B]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1)
  (hh : isEquivToPiMat A)
  {f : A →ₗ[ℂ] B} (hf : f •ₛ f = f) :
  schurProjection f ↔ LinearMap.IsPosMap f :=
⟨λ h => h.isPosMap h₁ hδ h₂,
 λ h => ⟨hf, isReal_of_isPosMap_of_starAlgEquiv_piMat hh.φ h⟩⟩

class QuantumGraph (A : Type*) [NormedAddCommGroupOfRing A] [hA : QuantumSet A]
    (f : A →ₗ[ℂ] A) : Prop :=
  isIdempotentElem : f •ₛ f = f

-- class QuantumGraphHom {A B : Type*} [NormedAddCommGroupOfRing A]
--   [NormedAddCommGroupOfRing B] [hA : QuantumSet A] [hB : QuantumSet B]
--   {x : A →ₗ[ℂ] A} (hx : QuantumGraph A x)
--   {y : B →ₗ[ℂ] B} (hy : QuantumGraph B y)
--     extends A →⋆ₐ[ℂ] B where
--   isGraphHom :
--     y •ₛ (toStarAlgHom.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint toStarAlgHom.toLinearMap))
--       = toStarAlgHom.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint toStarAlgHom.toLinearMap)
