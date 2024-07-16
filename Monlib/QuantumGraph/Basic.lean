import Monlib.LinearAlgebra.QuantumSet.SchurMul
import Monlib.LinearAlgebra.QuantumSet.Symm
import Monlib.LinearAlgebra.TensorProduct.Lemmas
import Monlib.LinearAlgebra.Ips.MinimalProj
import Monlib.LinearAlgebra.PosMap_isReal
import Monlib.LinearAlgebra.MyBimodule
import Monlib.LinearAlgebra.TensorProduct.Submodule
-- import Monlib.LinearAlgebra.QuantumSet.TensorProduct

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

open scoped TensorProduct
variable {A B : Type*} [ha:starAlgebra A] [hb:starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B]

private noncomputable def rmulMapLmul_apply_Upsilon_apply_aux :
    (A →ₗ[ℂ] B) →ₗ[ℂ] ((A ⊗[ℂ] B) →ₗ[ℂ] (A ⊗[ℂ] B)) where
  toFun x :=
  { toFun := λ y => Upsilon (x •ₛ Upsilon.symm y)
    map_add' := λ _ _ => by simp only [LinearEquiv.trans_symm, map_add, LinearEquiv.trans_apply,
      LinearEquiv.TensorProduct.map_symm_apply, LinearEquiv.symm_symm, QuantumSet.Psi_symm_apply,
      schurMul_apply_apply, QuantumSet.Psi_apply, LinearEquiv.TensorProduct.map_apply]
    map_smul' := λ _ _ => by simp only [LinearEquiv.trans_symm, LinearMapClass.map_smul,
      LinearEquiv.trans_apply, LinearEquiv.TensorProduct.map_symm_apply, LinearEquiv.symm_symm,
      QuantumSet.Psi_symm_apply, schurMul_apply_apply, QuantumSet.Psi_apply,
      LinearEquiv.TensorProduct.map_apply, RingHom.id_apply] }
  map_add' _ _ := by
    simp_rw [map_add, LinearMap.add_apply, map_add]; rfl
  map_smul' _ _ := by
    simp_rw [map_smul, LinearMap.smul_apply, map_smul]; rfl

private lemma rmulMapLmul_apply_Upsilon_apply_aux_apply
  (x : A →ₗ[ℂ] B) (y : A ⊗[ℂ] B) :
  rmulMapLmul_apply_Upsilon_apply_aux x y = Upsilon (x •ₛ Upsilon.symm y) :=
rfl

lemma Upsilon_rankOne (a : A) (b : B) :
  Upsilon (rankOne ℂ a b).toLinearMap = (modAut (- k B - 1) (star b)) ⊗ₜ[ℂ] a :=
by
  rw [Upsilon_apply, QuantumSet.Psi_toFun_apply, TensorProduct.comm_tmul,
    TensorProduct.map_tmul, LinearEquiv.lTensor_tmul, starAlgebra.modAut_star,
    starAlgebra.modAut_zero]
  ring_nf
  rfl
lemma Upsilon_symm_tmul (a : A) (b : B) :
  Upsilon.symm (a ⊗ₜ[ℂ] b) = (rankOne ℂ b (modAut (- k A - 1) (star a))).toLinearMap :=
by
  rw [Upsilon_symm_apply]
  simp only [LinearEquiv.lTensor_symm_tmul, LinearEquiv.symm_symm, op_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, unop_apply, MulOpposite.unop_op, TensorProduct.comm_symm_tmul, QuantumSet.Psi_invFun_apply,
    starAlgebra.modAut_zero, neg_zero]
  ring_nf
  rfl

theorem rmulMapLmul_apply_Upsilon_apply (x : A →ₗ[ℂ] B) (y : A ⊗[ℂ] B) :
  (rmulMapLmul (Upsilon x)) y = Upsilon (x •ₛ Upsilon.symm y) :=
by
  rw [← rmulMapLmul_apply_Upsilon_apply_aux_apply, ← LinearEquiv.coe_toLinearMap,
    ← LinearMap.comp_apply]
  revert y x
  simp_rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro x y
  rw [TensorProduct.ext_iff]
  intro a b
  simp only [rmulMapLmul_apply_Upsilon_apply_aux_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Upsilon_rankOne, Upsilon_symm_tmul,
    schurMul.apply_rankOne, rmulMapLmul_apply,
    TensorProduct.map_tmul, star_mul, map_mul,
    starAlgebra.modAut_star, QuantumSet.modAut_apply_modAut,
    add_neg_self, QuantumSet.modAut_zero, star_star]
  rfl


theorem QuantumSet.comm_op_modAut_map_comul_one_eq_Psi (r : ℝ) (f : A →ₗ[ℂ] B) :
  (TensorProduct.comm _ _ _)
  ((TensorProduct.map ((op ℂ).toLinearMap ∘ₗ (modAut r).toLinearMap) f) (Coalgebra.comul 1)) = Psi 0 (k A + 1 - r) f :=
by
  calc (TensorProduct.comm ℂ Aᵐᵒᵖ B)
        ((TensorProduct.map
        ((op ℂ).toLinearMap ∘ₗ (ha.modAut r).toLinearMap) f) (Coalgebra.comul 1 : A ⊗[ℂ] A))
      = (TensorProduct.comm ℂ Aᵐᵒᵖ B)
        ((TensorProduct.map ((op ℂ).toLinearMap ∘ₗ (modAut r).toLinearMap) (unop ℂ).toLinearMap)
        (tenSwap ℂ (Psi 0 (k A + 1) f))) := ?_
    _ = (TensorProduct.comm _ _ _)
        ((TensorProduct.map (op ℂ).toLinearMap (unop ℂ).toLinearMap)
        (tenSwap ℂ
        ((LinearMap.lTensor _ (modAut r).op.toLinearMap)
        (Psi 0 (k A + 1) f)))) := ?_
    _ = (TensorProduct.comm _ _ _)
      ((TensorProduct.map (op ℂ).toLinearMap (unop ℂ).toLinearMap)
      (tenSwap ℂ
      (Psi 0 (k A + 1 - r) f))) := ?_
    _ = Psi 0 (k A + 1 - r) f := ?_
  . rw [← tenSwap_lTensor_comul_one_eq_Psi, tenSwap_apply_tenSwap]
    simp_rw [LinearMap.lTensor, TensorProduct.map_apply_map_apply]
    simp only [LinearMap.comp_id, EmbeddingLike.apply_eq_iff_eq, ← LinearMap.comp_assoc,
      unop_comp_op, LinearMap.one_comp]
  . congr 1
    simp_rw [AlgEquiv.op_toLinearMap, tenSwap_apply_lTensor,
      ← LinearMap.comp_apply,
      ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
      ← LinearMap.comp_assoc, LinearMap.map_comp_rTensor]
  . simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
      lTensor_modAut_comp_Psi]
    ring_nf
  . suffices ∀ x, (TensorProduct.comm ℂ Aᵐᵒᵖ B) (((op ℂ).toLinearMap ⊗ₘ (unop ℂ).toLinearMap) (tenSwap ℂ x)) = x by
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
theorem schurProjection.isPosMap [PartialOrder A] [PartialOrder B]
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

theorem schurIdempotent.isSchurProjection_iff_isPosMap
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

class QuantumGraph.IsReal {A : Type*} [starAlgebra A] [hA : QuantumSet A]
    {f : A →ₗ[ℂ] A} (h : QuantumGraph A f) : Prop :=
  isReal : LinearMap.IsReal f

class QuantumGraph.Real (A : Type*) [starAlgebra A] [hA : QuantumSet A]
    (f : A →ₗ[ℂ] A) : Prop where
  isIdempotentElem : f •ₛ f = f
  isReal : LinearMap.IsReal f

theorem quantumGraphReal_iff_schurProjection {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔ schurProjection f :=
⟨λ h => ⟨h.isIdempotentElem, h.isReal⟩,
 λ h => ⟨h.isIdempotentElem, h.isReal⟩⟩

theorem QuantumGraph.Real.toQuantumGraph {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) :
  QuantumGraph A f :=
⟨h.isIdempotentElem⟩

theorem quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔
  (IsIdempotentElem (hA.Psi 0 (hA.k + 1/2) f) ∧
    IsSelfAdjoint (hA.Psi 0 (hA.k + 1/2) f)) :=
by
  rw [← schurIdempotent_iff_Psi_isIdempotentElem, ← isReal_iff_Psi_isSelfAdjoint]
  exact ⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

theorem real_Upsilon_toBimodule {f : A →ₗ[ℂ] B} (gns₁ : hA.k = 0)
  (gns₂ : hB.k = 0) :
  (Upsilon f.real).toIsBimoduleMap.1
    = LinearMap.adjoint
      (Upsilon f).toIsBimoduleMap.1 :=
by
  have : ∀ (a : B) (b : A),
    (Upsilon (rankOne ℂ a b).toLinearMap.real).toIsBimoduleMap.1
    = LinearMap.adjoint (Upsilon (rankOne ℂ a b).toLinearMap).toIsBimoduleMap.1 :=
  by
    intro a b
    simp_rw [Upsilon_rankOne, LinearEquiv.trans_apply, QuantumSet.Psi_apply,
      rankOne_real, QuantumSet.Psi_toFun_apply,
      LinearEquiv.TensorProduct.map_apply,
      TensorProduct.toIsBimoduleMap_apply_coe,
      rmulMapLmul_apply, TensorProduct.map_adjoint,
      TensorProduct.comm_tmul, TensorProduct.map_tmul,
      LinearEquiv.lTensor_tmul, rmulMapLmul_apply,
      rmul_adjoint, QuantumSet.modAut_star, QuantumSet.modAut_apply_modAut,
      lmul_adjoint,]
    ring_nf
    simp only [neg_add_rev, neg_sub, sub_neg_eq_add, star_star, LinearEquiv.coe_coe, unop_apply,
      MulOpposite.unop_op, starAlgebra.modAut_zero, AlgEquiv.one_apply, op_apply,
      MulOpposite.op_star, MulOpposite.unop_star, gns₁, gns₂, neg_zero]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  simp only [map_sum, LinearMap.real_sum, Submodule.coe_sum, this]

theorem schurMul_Upsilon_toBimodule {f g : A →ₗ[ℂ] B} :
  (Upsilon (f •ₛ g)).toIsBimoduleMap.1
    = (Upsilon f).toIsBimoduleMap.1 * (Upsilon g).toIsBimoduleMap.1 :=
by
  have : ∀ (a c : B) (b d : A),
    (Upsilon ((rankOne ℂ a b).toLinearMap •ₛ (rankOne ℂ c d).toLinearMap)).toIsBimoduleMap.1
    = (Upsilon (rankOne ℂ a b).toLinearMap).toIsBimoduleMap.1
      * (Upsilon (rankOne ℂ c d).toLinearMap).toIsBimoduleMap.1 :=
  by
    intro a c b d
    simp_rw [schurMul.apply_rankOne, Upsilon_rankOne, TensorProduct.toIsBimoduleMap_apply_coe,
      rmulMapLmul_apply, ← TensorProduct.map_mul,
      rmul_eq_mul, LinearMap.mul_eq_comp, ← LinearMap.mulRight_mul,
      lmul_eq_mul, ← LinearMap.mulLeft_mul, ← map_mul, ← star_mul]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  obtain ⟨γ, δ, rfl⟩ := LinearMap.exists_sum_rankOne g
  simp only [map_sum, LinearMap.sum_apply, Finset.sum_mul,
    Finset.mul_sum, Submodule.coe_sum, this]

theorem quantumGraphReal_iff_Upsilon_toBimodule_orthogonalProjection
  {f : A →ₗ[ℂ] A} (gns : hA.k = 0) :
  QuantumGraph.Real A f ↔
  ContinuousLinearMap.IsOrthogonalProjection
  (LinearMap.toContinuousLinearMap
    (Upsilon f).toIsBimoduleMap.1) :=
by
  rw [LinearMap.isOrthogonalProjection_iff,
    IsIdempotentElem, ← schurMul_Upsilon_toBimodule,
    isSelfAdjoint_iff, LinearMap.star_eq_adjoint,
    ← real_Upsilon_toBimodule gns gns]
  simp_rw [Subtype.val_inj, (LinearEquiv.injective _).eq_iff,
    ← LinearMap.isReal_iff]
  exact ⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

section

theorem StarAlgEquiv.toAlgEquiv_toAlgHom_toLinearMap
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Star A] [Star B] (f : A ≃⋆ₐ[R] B) :
    f.toAlgEquiv.toAlgHom.toLinearMap = f.toLinearMap :=
rfl

def QuantumGraph.Real_conj_starAlgEquiv
  {A B : Type*} [starAlgebra A] [starAlgebra B]
  [QuantumSet A] [QuantumSet B]
  {x : A →ₗ[ℂ] A} (hx : QuantumGraph.Real A x)
  {f : A ≃⋆ₐ[ℂ] B} (hf : Isometry f) :
  QuantumGraph.Real _ (f.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint f.toLinearMap)) :=
by
  constructor
  . rw [← StarAlgEquiv.toAlgEquiv_toAlgHom_toLinearMap,
      schurMul_algHom_comp_algHom_adjoint, hx.1]
  . suffices LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap from ?_
    . simp_rw [this]
      rw [LinearMap.real_starAlgEquiv_conj_iff]
      exact QuantumGraph.Real.isReal
    . exact QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm.mp hf

theorem Submodule.eq_iff_orthogonalProjection_eq
  {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {U : Submodule ℂ E}
  {V : Submodule ℂ E} [CompleteSpace E] [CompleteSpace ↥U] [CompleteSpace ↥V] :
  U = V ↔ orthogonalProjection' U = orthogonalProjection' V :=
by simp_rw [le_antisymm_iff, orthogonalProjection.is_le_iff_subset]

open scoped FiniteDimensional in
theorem Submodule.adjoint_subtype {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Submodule ℂ E} :
  LinearMap.adjoint U.subtype = (orthogonalProjection U).toLinearMap :=
by
  rw [← Submodule.adjoint_subtypeL]
  rfl

theorem Submodule.map_orthogonalProjection_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Submodule ℂ E} :
  Submodule.map (orthogonalProjection U).toLinearMap U = ⊤ :=
by
  ext x
  simp only [mem_map, ContinuousLinearMap.coe_coe, mem_top, iff_true]
  use x
  simp only [SetLike.coe_mem, orthogonalProjection_mem_subspace_eq_self, and_self]

theorem OrthonormalBasis.orthogonalProjection_eq_sum_rankOne {ι 𝕜 : Type _} [RCLike 𝕜] {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] {U : Submodule 𝕜 E}
    [CompleteSpace U] (b : OrthonormalBasis ι 𝕜 ↥U) :
    orthogonalProjection U = ∑ i : ι, rankOne 𝕜 (b i) (b i : E) :=
by
  ext
  simp_rw [b.orthogonalProjection_eq_sum, ContinuousLinearMap.sum_apply, rankOne_apply]


theorem orthogonalProjection_submoduleMap {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {U : Submodule ℂ E}
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] (f : E ≃ₗᵢ[ℂ] E') :
  (orthogonalProjection' (Submodule.map f U)).toLinearMap
    = f.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.symm.toLinearMap :=
by
  ext
  simp only [orthogonalProjection'_eq, ContinuousLinearMap.coe_comp, Submodule.coe_subtypeL,
    LinearMap.coe_comp, Submodule.coeSubtype, ContinuousLinearMap.coe_coe, Function.comp_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [← orthogonalProjection_map_apply]
  rfl

theorem orthogonalProjection_submoduleMap_isometry {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {U : Submodule ℂ E}
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']
  {f : E ≃ₗ[ℂ] E'} (hf : Isometry f) :
  (orthogonalProjection' (Submodule.map f U)).toLinearMap
    = f.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.symm.toLinearMap :=
by
  ext x
  simp only [orthogonalProjection'_eq, ContinuousLinearMap.coe_comp, Submodule.coe_subtypeL,
    LinearMap.coe_comp, Submodule.coeSubtype, ContinuousLinearMap.coe_coe, Function.comp_apply,
    LinearEquiv.coe_coe]
  let f' : E ≃ₗᵢ[ℂ] E' := ⟨f, (isometry_iff_norm _).mp hf⟩
  calc ↑((orthogonalProjection (Submodule.map f U)) x)
      = ↑(orthogonalProjection (Submodule.map f'.toLinearEquiv U) x) := rfl
    _ = f' ↑((orthogonalProjection U) (f'.symm x)) := orthogonalProjection_map_apply _ _ _
    _ = f ↑((orthogonalProjection U) (f.symm x)) := rfl

 instance
   StarAlgEquivClass.instLinearMapClass
  {R A B : Type*} [Semiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Mul A] [Mul B] [Module R A] [Module R B] [Star A] [Star B]
  {F : Type*} [EquivLike F A B] [NonUnitalAlgEquivClass F R A B]
  [StarAlgEquivClass F R A B] :
  LinearMapClass F R A B :=
SemilinearMapClass.mk

theorem orthogonalProjection_submoduleMap_isometry_starAlgEquiv
  {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {U : Submodule ℂ E}
  [Mul E] [Mul E'] [Star E] [Star E']
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']
  {f : E ≃⋆ₐ[ℂ] E'} (hf : Isometry f) :
  (orthogonalProjection' (Submodule.map f U)).toLinearMap
    = f.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.symm.toLinearMap :=
by
  have hf' : Isometry f.toLinearEquiv := hf
  calc (orthogonalProjection' (Submodule.map f U)).toLinearMap
      = (orthogonalProjection' (Submodule.map f.toLinearEquiv U)).toLinearMap := rfl
    _ = f.toLinearEquiv.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.toLinearEquiv.symm.toLinearMap := orthogonalProjection_submoduleMap_isometry hf'

theorem orthogonalProjection_submoduleMap' {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {U : Submodule ℂ E}
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] (f : E' ≃ₗᵢ[ℂ] E) :
  (orthogonalProjection' (Submodule.map f.symm U)).toLinearMap
    = f.symm.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.toLinearMap :=
orthogonalProjection_submoduleMap f.symm

end
section

noncomputable def QuantumGraph.Real.upsilonSubmodule
  {f : A →ₗ[ℂ] A} (gns : hA.k = 0)
  (hf : QuantumGraph.Real A f) :
  Submodule ℂ (A ⊗[ℂ] A) :=
by
  choose U _ using
    (orthogonal_projection_iff.mpr
    (And.comm.mp
    (ContinuousLinearMap.isOrthogonalProjection_iff'.mp
      ((quantumGraphReal_iff_Upsilon_toBimodule_orthogonalProjection gns).mp hf))))
  exact U

theorem QuantumGraph.Real.upsilonOrthogonalProjection {f : A →ₗ[ℂ] A}
  (gns : hA.k = 0)
  (hf : QuantumGraph.Real A f) :
  orthogonalProjection' (upsilonSubmodule gns hf)
    = LinearMap.toContinuousLinearMap
      ((TensorProduct.toIsBimoduleMap (Upsilon f)).1) :=
(QuantumGraph.Real.upsilonSubmodule.proof_14 gns hf)

theorem QuantumGraph.Real.upsilonOrthogonalProjection' {f : A →ₗ[ℂ] A}
  (gns : hA.k = 0)
  (hf : QuantumGraph.Real A f) :
  (orthogonalProjection' (upsilonSubmodule gns hf)).toLinearMap
    = rmulMapLmul ((orthogonalProjection' (upsilonSubmodule gns hf)).toLinearMap 1) :=
by
  symm
  rw [← LinearMap.isBimoduleMap_iff', ← LinearMap.mem_isBimoduleMaps_iff]
  rw [upsilonOrthogonalProjection gns hf, LinearMap.coe_toContinuousLinearMap]
  exact Submodule.coe_mem (TensorProduct.toIsBimoduleMap (Upsilon f))

noncomputable def QuantumGraph.Real.upsilonOrthonormalBasis {f : A →ₗ[ℂ] A}
  (gns : hA.k = 0) (hf : QuantumGraph.Real A f) :
  OrthonormalBasis (Fin (FiniteDimensional.finrank ℂ (upsilonSubmodule gns hf))) ℂ (upsilonSubmodule gns hf) :=
stdOrthonormalBasis ℂ (upsilonSubmodule gns hf)

@[simp]
theorem OrthonormalBasis.tensorProduct_toBasis {𝕜 E F : Type*}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁]
  [DecidableEq ι₂] (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  (b₁.tensorProduct b₂).toBasis = b₁.toBasis.tensorProduct b₂.toBasis :=
by aesop

theorem TensorProduct.of_orthonormalBasis_eq_span
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : TensorProduct 𝕜 E F)
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁]
  [DecidableEq ι₂] (b₁ : OrthonormalBasis ι₁ 𝕜 E)
  (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  letI := FiniteDimensional.of_fintype_basis b₁.toBasis
  letI := FiniteDimensional.of_fintype_basis b₂.toBasis
  x = ∑ i : ι₁, ∑ j : ι₂, ((b₁.tensorProduct b₂).repr x) (i, j) • b₁ i ⊗ₜ[𝕜] b₂ j :=
by
  nth_rw 1 [TensorProduct.of_basis_eq_span x b₁.toBasis b₂.toBasis]
  rfl

noncomputable def TensorProduct.of_orthonormalBasis_prod
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : TensorProduct 𝕜 E F)
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁]
  [DecidableEq ι₂] (b₁ : OrthonormalBasis ι₁ 𝕜 E)
  (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  letI := FiniteDimensional.of_fintype_basis b₁.toBasis
  letI := FiniteDimensional.of_fintype_basis b₂.toBasis
  (ι₁ × ι₂) → (E × F) :=
letI := FiniteDimensional.of_fintype_basis b₁.toBasis
letI := FiniteDimensional.of_fintype_basis b₂.toBasis
λ (i,j) => ((((b₁.tensorProduct b₂).repr x) (i,j)) • b₁ i, b₂ j)

@[simp]
theorem TensorProduct.of_othonormalBasis_prod_eq
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : E ⊗[𝕜] F)
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁]
  [DecidableEq ι₂]
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  ∑ i : ι₁ × ι₂,
    (x.of_orthonormalBasis_prod b₁ b₂ i).1 ⊗ₜ[𝕜] (x.of_orthonormalBasis_prod b₁ b₂ i).2
      = x :=
by
  nth_rw 3 [TensorProduct.of_orthonormalBasis_eq_span x b₁ b₂]
  simp_rw [smul_tmul', Finset.sum_product_univ]
  rfl
@[simp]
theorem TensorProduct.of_othonormalBasis_prod_eq'
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : E ⊗[𝕜] F)
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁]
  [DecidableEq ι₂]
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  ∑ i : ι₁ × ι₂,
    (x.of_orthonormalBasis_prod b₁ b₂ i).1 ⊗ₜ[𝕜] b₂ i.2
      = x :=
by
  nth_rw 2 [TensorProduct.of_orthonormalBasis_eq_span x b₁ b₂]
  simp_rw [smul_tmul', Finset.sum_product_univ]
  rfl

theorem
  QuantumGraph.Real.upsilon_eq {f : A →ₗ[ℂ] A}
    (hf : QuantumGraph.Real A f) (gns : hA.k = 0) :
  let u := QuantumGraph.Real.upsilonOrthonormalBasis gns hf
  let b := hA.onb
  let a := λ (x : A ⊗[ℂ] A) =>
    λ i : (n A) × (n A) => (x.of_orthonormalBasis_prod b b i).1
  f = ∑ i, ∑ j, ⟪(u i : A ⊗[ℂ] A), 1⟫_ℂ
    • rankOne ℂ (b j.2) (modAut (-1) (star (a (u i : A ⊗[ℂ] A) j))) :=
by
  intro u b a
  symm
  have := Upsilon_symm_tmul (A := A) (B:=A)
  simp only [gns, neg_zero, zero_sub] at this
  simp_rw [ContinuousLinearMap.coe_sum, ContinuousLinearMap.coe_smul,
    ← this, ← map_smul]
  simp_rw [← map_sum, ← Finset.smul_sum, TensorProduct.of_othonormalBasis_prod_eq',
    ← rankOne_apply (𝕜 := ℂ) (1 : A ⊗[ℂ] A),
    ← ContinuousLinearMap.sum_apply,
    ← OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne]
  rw [upsilonOrthogonalProjection]
  simp_rw [TensorProduct.toIsBimoduleMap_apply_coe,
    LinearMap.coe_toContinuousLinearMap',
    rmulMapLmul_apply_one, LinearEquiv.symm_apply_apply]

@[simp]
theorem AlgEquiv.coe_comp
  {R A₁ A₂ A₃ : Type*} [CommSemiring R] [Semiring A₁] [Semiring A₂]
  [Semiring A₃] [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
  (e : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  e₂.toLinearMap.comp e.toLinearMap = (e.trans e₂).toLinearMap :=
rfl

@[simp]
theorem AlgEquiv.self_trans_symm
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (f : A ≃ₐ[R] B) :
  f.trans f.symm = AlgEquiv.refl :=
by aesop
@[simp]
theorem AlgEquiv.symm_trans_self
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (f : A ≃ₐ[R] B) :
  f.symm.trans f = AlgEquiv.refl :=
by aesop

theorem QuantumSet.starAlgEquiv_commutes_with_modAut_of_isometry''
  {A B : Type*} [hb : starAlgebra B] [ha : starAlgebra A]
  [hA : QuantumSet A] [hB : QuantumSet B] {f : A ≃⋆ₐ[ℂ] B}
  (hf : Isometry f) :
  f.toLinearMap ∘ₗ (modAut (-(2 * k A + 1))).toLinearMap
    = (modAut (-(2 * k B + 1))).toLinearMap ∘ₗ f.toLinearMap :=
by
  rw [← modAut_symm, AlgEquiv.linearMap_comp_eq_iff, AlgEquiv.symm_symm,
    LinearMap.comp_assoc, starAlgEquiv_commutes_with_modAut_of_isometry' hf,
    ← LinearMap.comp_assoc, ← modAut_symm]
  simp only [AlgEquiv.coe_comp, AlgEquiv.self_trans_symm]
  rfl

theorem LinearMap.tensorProduct_map_isometry_of {𝕜 A B C D : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C] [NormedAddCommGroup D]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [InnerProductSpace 𝕜 D]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] [FiniteDimensional 𝕜 D]
  {f : A →ₗ[𝕜] B} (hf : Isometry f) {g : C →ₗ[𝕜] D} (hg : Isometry g) :
  Isometry (f ⊗ₘ g) :=
by
  rw [isometry_iff_inner] at hf hg
  rw [isometry_iff_norm]
  intro x
  simp_rw [norm_eq_sqrt_inner (𝕜 := 𝕜)]
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  simp only [map_sum, sum_inner, inner_sum, TensorProduct.map_tmul]
  simp only [TensorProduct.inner_tmul, hf, hg, RCLike.mul_re,
    Finset.sum_sub_distrib]

theorem StarAlgEquiv.tensorProduct_map_isometry_of
  {A B C D : Type*} [starAlgebra A] [starAlgebra B] [starAlgebra C] [starAlgebra D]
  [QuantumSet A] [QuantumSet B] [QuantumSet C] [QuantumSet D]
  {f : A ≃⋆ₐ[ℂ] B} (hf : Isometry f) {g : C ≃⋆ₐ[ℂ] D}
  (hg : Isometry g) :
  Isometry (StarAlgEquiv.TensorProduct.map f g) :=
LinearMap.tensorProduct_map_isometry_of hf hg

@[simps!]
noncomputable def LinearIsometryEquiv.TensorProduct.map {𝕜 A B C D : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C] [NormedAddCommGroup D]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [InnerProductSpace 𝕜 D]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] [FiniteDimensional 𝕜 D]
  (f : A ≃ₗᵢ[𝕜] B) (g : C ≃ₗᵢ[𝕜] D) :
    A ⊗[𝕜] C ≃ₗᵢ[𝕜] B ⊗[𝕜] D where
  toLinearEquiv := LinearEquiv.TensorProduct.map f.toLinearEquiv g.toLinearEquiv
  norm_map' := by
    rw [← isometry_iff_norm]
    exact LinearMap.tensorProduct_map_isometry_of f.isometry g.isometry

theorem LinearIsometryEquiv.TensorProduct.map_tmul
  {𝕜 A B C D : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C] [NormedAddCommGroup D]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [InnerProductSpace 𝕜 D]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] [FiniteDimensional 𝕜 D]
  (f : A ≃ₗᵢ[𝕜] B) (g : C ≃ₗᵢ[𝕜] D) (x : A) (y : C) :
  (LinearIsometryEquiv.TensorProduct.map f g) (x ⊗ₜ y) = f x ⊗ₜ g y :=
rfl

theorem oneHom_isometry_inner_one_right
  {𝕜 A B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B]
  [One A] [One B]
  {F : Type*} [FunLike F A B] [LinearMapClass F 𝕜 A B]
  [OneHomClass F A B] {f : F}
  (hf : Isometry f) (x : A) :
  ⟪f x, 1⟫_𝕜 = ⟪x, 1⟫_𝕜 :=
by
  rw [← map_one f]
  exact (isometry_iff_inner _).mp hf _ _

theorem
  QuantumGraph.Real.upsilon_starAlgEquiv_conj_eq
  {f : A →ₗ[ℂ] A} (gns : hA.k = 0) (gns₂ : hB.k = 0)
  (hf : QuantumGraph.Real A f)
  {φ : A ≃⋆ₐ[ℂ] B} (hφ : Isometry φ) :
  let u := QuantumGraph.Real.upsilonOrthonormalBasis gns hf
  let b := hA.onb
  let a := λ (x : A ⊗[ℂ] A) =>
    λ i : (n A) × (n A) => (x.of_orthonormalBasis_prod b b i).1
  φ.toLinearMap ∘ₗ f ∘ₗ LinearMap.adjoint φ.toLinearMap
    = ∑ i, ∑ j, ∑ p,
      (⟪φ (a (u i : A ⊗[ℂ] A) p), 1⟫_ℂ
        * ⟪φ (b p.2), 1⟫_ℂ)
      • rankOne ℂ (φ (b j.2)) (modAut (-1) (star (φ (a (u i : A ⊗[ℂ] A) j)))) :=
by
  intro u b a
  nth_rw 1 [hf.upsilon_eq gns]
  simp only [ContinuousLinearMap.coe_sum,
    ContinuousLinearMap.coe_smul,
    LinearMap.comp_sum, LinearMap.sum_comp,
    LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_rankOne, LinearMap.rankOne_comp']
  simp only [StarAlgEquiv.toLinearMap_apply]
  have := QuantumSet.starAlgEquiv_commutes_with_modAut_of_isometry'' hφ
  simp only [gns, gns₂, mul_zero, zero_add, LinearMap.ext_iff,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.toLinearMap_apply] at this
  simp_rw [this, map_star, oneHom_isometry_inner_one_right hφ,
    ← TensorProduct.inner_tmul, ← Finset.sum_smul,
    ← sum_inner, ← Algebra.TensorProduct.one_def, TensorProduct.of_othonormalBasis_prod_eq']

theorem LinearMapClass.apply_rankOne_apply
  {E₁ E₂ E₃ 𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂] [InnerProductSpace 𝕜 E₃]
  {F : Type*}
  [FunLike F E₁ E₃] [LinearMapClass F 𝕜 E₁ E₃]
  (x : E₁) (y z : E₂) (u : F) :
    u ((rankOne 𝕜 x y) z) = rankOne 𝕜 (u x) y z :=
by simp only [rankOne_apply, map_smul]

end

-- class QuantumGraphHom {A B : Type*} [NormedAddCommGroupOfRing A]
--   [NormedAddCommGroupOfRing B] [hA : QuantumSet A] [hB : QuantumSet B]
--   {x : A →ₗ[ℂ] A} (hx : QuantumGraph A x)
--   {y : B →ₗ[ℂ] B} (hy : QuantumGraph B y)
--     extends A →⋆ₐ[ℂ] B where
--   isGraphHom :
--     y •ₛ (toStarAlgHom.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint toStarAlgHom.toLinearMap))
--       = toStarAlgHom.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint toStarAlgHom.toLinearMap)
