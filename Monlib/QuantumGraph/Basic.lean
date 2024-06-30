import Monlib.LinearAlgebra.QuantumSet.SchurMul
import Monlib.LinearAlgebra.QuantumSet.Symm
import Monlib.LinearAlgebra.TensorProduct.Lemmas
import Monlib.LinearAlgebra.Ips.MinimalProj
import Monlib.LinearAlgebra.PosMap_isReal

local notation x " ⊗ₘ " y => TensorProduct.map x y

theorem symmMap_apply_schurMul {A B : Type*} [starAlgebra A] [starAlgebra B]
    [hA : QuantumSet A] [QuantumSet B] (f g : A →ₗ[ℂ] B) :
  symmMap ℂ _ _ (f •ₛ g) = (symmMap _ _ _ g) •ₛ (symmMap _ _ _ f) :=
by
  rw [symmMap_apply, schurMul_real, schurMul_adjoint]
  rfl

alias QuantumSet.modAut_star := starAlgebra.modAut_star
alias QuantumSet.modAut_zero := starAlgebra.modAut_zero

theorem Psi_apply_linearMap_comp_linearMap_of_commute_modAut {A B C D : Type*}
  [ha:starAlgebra A] [hb:starAlgebra B]
  [hc:starAlgebra C] [hd:starAlgebra D]
  [hA : QuantumSet A] [hB : QuantumSet B]
  [hC : QuantumSet C] [hD : QuantumSet D]
  {f : A →ₗ[ℂ] B} {g : D →ₗ[ℂ] C}
  (t r : ℝ)
  (hf : (hb.modAut t).toLinearMap.comp f = f.comp (ha.modAut t).toLinearMap)
  (hg : (hc.modAut r).toLinearMap.comp g = g.comp (hd.modAut r).toLinearMap)
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

theorem symmMap_symm_comp {A B C : Type*} [starAlgebra A]
  [starAlgebra B] [hA : QuantumSet A] [hB : QuantumSet B]
  [starAlgebra C] [QuantumSet C]
  (x : A →ₗ[ℂ] B) (y : C →ₗ[ℂ] A) :
  (symmMap ℂ _ _).symm (x ∘ₗ y) = (symmMap ℂ _ _).symm y ∘ₗ (symmMap ℂ _ _).symm x :=
by
  simp only [symmMap_symm_apply, LinearMap.adjoint_comp, LinearMap.real_comp]

theorem linearMap_map_Psi_of_commute_modAut {A B C D : Type*}
  [ha:starAlgebra A] [hb:starAlgebra B]
  [hc:starAlgebra C] [hd:starAlgebra D]
  [hA : QuantumSet A] [hB : QuantumSet B]
  [hC : QuantumSet C] [hD : QuantumSet D]
  {f : A →ₗ[ℂ] B} {g : Cᵐᵒᵖ →ₗ[ℂ] Dᵐᵒᵖ}
  (t r : ℝ)
  (hf : (hb.modAut t).toLinearMap.comp f = f.comp (ha.modAut t).toLinearMap)
  (hg : (hd.modAut r).toLinearMap.comp g.unop = g.unop.comp (hc.modAut r).toLinearMap)
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

lemma schurIdempotent_iff_Psi_isIdempotentElem {A B : Type*} [starAlgebra A] [starAlgebra B]
    [hA : QuantumSet A] [QuantumSet B] (f : A →ₗ[ℂ] B) (t r : ℝ) :
  f •ₛ f = f ↔ IsIdempotentElem (hA.Psi t r f) :=
by
  simp_rw [IsIdempotentElem, ← Psi.schurMul, Function.Injective.eq_iff (LinearEquiv.injective _)]

@[simp]
theorem LinearMap.op_real {K E F : Type*}
  [AddCommMonoid E] [StarAddMonoid E] [AddCommMonoid F] [StarAddMonoid F]
  [Semiring K] [Module K E] [Module K F] [InvolutiveStar K] [StarModule K E]  [StarModule K F]
  (φ : E →ₗ[K] F) :
  φ.op.real = φ.real.op :=
rfl

lemma modAut_map_comp_Psi {A B : Type*} [ha:starAlgebra A] [hb:starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B] (t₁ r₁ t₂ r₂ : ℝ) :
  ((hb.modAut t₁).toLinearMap ⊗ₘ ((ha.modAut r₁).op.toLinearMap)) ∘ₗ (hA.Psi t₂ r₂).toLinearMap
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

lemma lTensor_modAut_comp_Psi {A B : Type*} [ha:starAlgebra A] [hb:starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B] (t₂ r₁ r₂ : ℝ) :
  (LinearMap.lTensor B (ha.modAut r₁).op.toLinearMap)
    ∘ₗ (hA.Psi t₂ r₂).toLinearMap
  = (hA.Psi t₂ (-r₁ + r₂)).toLinearMap :=
by
  nth_rw 2 [← zero_add t₂]
  rw [← modAut_map_comp_Psi, QuantumSet.modAut_zero]
  rfl
lemma rTensor_modAut_comp_Psi {A B : Type*} [ha:starAlgebra A] [hb:starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B] (t₁ t₂ r₂ : ℝ) :
  (LinearMap.rTensor Aᵐᵒᵖ (hb.modAut t₁).toLinearMap)
    ∘ₗ (hA.Psi t₂ r₂).toLinearMap
  = (hA.Psi (t₁ + t₂) r₂).toLinearMap :=
by
  nth_rw 2 [← zero_add r₂]
  rw [← neg_zero, ← modAut_map_comp_Psi, QuantumSet.modAut_zero]
  rfl

variable {A B : Type*} [ha:starAlgebra A] [hb:starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B]
open scoped TensorProduct
theorem QuantumSet.comm_op_modAut_map_comul_one_eq_Psi (r : ℝ) (f : A →ₗ[ℂ] B) :
  (TensorProduct.comm _ _ _)
  ((TensorProduct.map (op ∘ₗ (modAut r).toLinearMap) f) (Coalgebra.comul 1)) = Psi 0 (k A + 1 - r) f :=
by
  calc (TensorProduct.comm ℂ Aᵐᵒᵖ B)
        ((TensorProduct.map
        ((op : A →ₗ[ℂ] Aᵐᵒᵖ) ∘ₗ (ha.modAut r).toLinearMap) f) (Coalgebra.comul 1 : A ⊗[ℂ] A))
      = (TensorProduct.comm ℂ Aᵐᵒᵖ B)
        ((TensorProduct.map (op ∘ₗ (modAut r).toLinearMap) unop)
        (tenSwap (Psi 0 (k A + 1) f))) := ?_
    _ = (TensorProduct.comm _ _ _)
        ((TensorProduct.map op unop)
        (tenSwap
        ((LinearMap.lTensor _ (modAut r).op.toLinearMap)
        (Psi 0 (k A + 1) f)))) := ?_
    _ = (TensorProduct.comm _ _ _)
      ((TensorProduct.map op unop)
      (tenSwap
      (Psi 0 (k A + 1 - r) f))) := ?_
    _ = Psi 0 (k A + 1 - r) f := ?_
  . rw [← tenSwap_lTensor_comul_one_eq_Psi, tenSwap_apply_tenSwap]
    simp_rw [LinearMap.lTensor, TensorProduct.map_apply_map_apply]
    simp only [LinearMap.comp_id, EmbeddingLike.apply_eq_iff_eq, ← LinearMap.comp_assoc,
      unop_comp_op, LinearMap.one_comp]
  . congr 1
    simp_rw [AlgEquiv.op_toLinearMap, tenSwap_apply_lTensor,
      ← LinearMap.comp_apply,
      ← LinearMap.comp_assoc, LinearMap.map_comp_rTensor]
  . simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
      lTensor_modAut_comp_Psi]
    ring_nf
  . suffices ∀ x, (TensorProduct.comm ℂ Aᵐᵒᵖ B) ((op ⊗ₘ unop) (tenSwap x)) = x by
      rw [this]
    intro x
    simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
    nth_rw 2 [← LinearMap.id_apply (R := ℂ) x]
    revert x
    rw [← LinearMap.ext_iff, TensorProduct.ext_iff]
    intro a b
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.id_coe,
      id_eq, tenSwap_apply, TensorProduct.map_tmul,
      TensorProduct.comm_tmul]
    rfl

open scoped TensorProduct

@[simp]
theorem AlgEquiv.symm_one {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (1 : A ≃ₐ[R] A).symm = 1 :=
rfl
theorem LinearMap.lTensor_eq {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M]
  [Module R N] [Module R P] (f : N →ₗ[R] P) :
  lTensor M f = TensorProduct.map LinearMap.id f :=
rfl
theorem AlgEquiv.symm_op
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (f : A ≃ₐ[R] B) :
  (AlgEquiv.op f).symm = AlgEquiv.op f.symm :=
rfl

alias QuantumSet.modAut_trans := starAlgebra.modAut_trans

variable {A B : Type*} [ha:starAlgebra A] [hb:starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B]
lemma isReal_iff_Psi (f : A →ₗ[ℂ] B) (t r : ℝ) :
  LinearMap.IsReal f ↔ star (hA.Psi t r f) = hA.Psi (-t) ((2 * hA.k) + 1 - r) f :=
by
  simp_rw [LinearMap.isReal_iff, ← Function.Injective.eq_iff (hA.Psi t r).injective,
    Psi.real_apply]
  nth_rw 1 [← Function.Injective.eq_iff
    (AlgEquiv.TensorProduct.map (hb.modAut (- (2 * t)))
      (AlgEquiv.op (ha.modAut (2 * r - 1)))).injective]
  simp_rw [← AlgEquiv.TensorProduct.map_toLinearMap, AlgEquiv.toLinearMap_apply,
    AlgEquiv.TensorProduct.map_map_toLinearMap, AlgEquiv.op_trans,
    QuantumSet.modAut_trans]
  simp only [add_right_neg, QuantumSet.modAut_zero, sub_add_sub_cancel, sub_self,
    AlgEquiv.op_one, AlgEquiv.TensorProduct.map_one, AlgEquiv.one_apply]
  simp only [← LinearEquiv.coe_toLinearMap, ← AlgEquiv.toLinearMap_apply,
    ← LinearMap.comp_apply, AlgEquiv.TensorProduct.map_toLinearMap, modAut_map_comp_Psi,
    two_mul, neg_add, neg_sub, sub_add]
  ring_nf
  simp only [← AlgEquiv.TensorProduct.map_toLinearMap,
    AlgEquiv.toLinearMap_apply]
  rw [eq_comm, AlgEquiv.eq_apply_iff_symm_eq, AlgEquiv.TensorProduct.map_symm,
    AlgEquiv.symm_one, ← AlgEquiv.toLinearMap_apply,
    AlgEquiv.TensorProduct.map_toLinearMap, AlgEquiv.one_toLinearMap,
    LinearMap.one_eq_id, ← LinearMap.lTensor_eq,
    AlgEquiv.symm_op, QuantumSet.modAut_symm]
  simp_rw [← LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [lTensor_modAut_comp_Psi, neg_neg, eq_comm, LinearEquiv.coe_toLinearMap]
  ring_nf


lemma isReal_iff_Psi_isSelfAdjoint (f : A →ₗ[ℂ] B) :
  LinearMap.IsReal f ↔ IsSelfAdjoint (hA.Psi 0 (hA.k + (1 / 2)) f) :=
by
  rw [_root_.IsSelfAdjoint, isReal_iff_Psi f 0 (hA.k + 1/2)]
  ring_nf


class schurProjection (f : A →ₗ[ℂ] B) :
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
def schurProjection.isPosMap [PartialOrder A] [PartialOrder B]
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

def schurIdempotent.isSchurProjection_iff_isPosMap
  [PartialOrder A] [PartialOrder B]
  [StarOrderedRing A] [StarOrderedRing B]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  {δ : ℂ} (hδ : 0 ≤ δ)
  (h₂ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • 1)
  (hh : isEquivToPiMat A)
  {f : A →ₗ[ℂ] B} (hf : f •ₛ f = f) :
  schurProjection f ↔ LinearMap.IsPosMap f :=
⟨λ h => h.isPosMap h₁ hδ h₂,
 λ h => ⟨hf, isReal_of_isPosMap_of_starAlgEquiv_piMat hh.φ h⟩⟩

class QuantumGraph (A : Type*) [starAlgebra A] [hA : QuantumSet A]
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
