import Monlib.LinearAlgebra.QuantumSet.SchurMul
import Monlib.LinearAlgebra.QuantumSet.Symm
import Monlib.LinearAlgebra.tensorProduct
import Monlib.LinearAlgebra.Ips.MinimalProj
import Monlib.LinearAlgebra.PosMap_isReal

local notation x " ⊗ₘ " y => TensorProduct.map x y

lemma schurIdempotent_iff_Psi_isIdempotentElem {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
    [hA : QuantumSet A] [QuantumSet B] (f : A →ₗ[ℂ] B) (t r : ℝ) :
  f •ₛ f = f ↔ IsIdempotentElem (hA.Psi t r f) :=
by
  simp_rw [IsIdempotentElem, ← Psi.schurMul, Function.Injective.eq_iff (LinearEquiv.injective _)]

lemma modAut_map_comp_Psi {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
    [hA : QuantumSet A] [hB : QuantumSet B] (t₁ r₁ t₂ r₂ : ℝ) :
  ((hB.modAut t₁).toLinearMap ⊗ₘ ((hA.modAut r₁).op.toLinearMap)) ∘ₗ (hA.Psi t₂ r₂).toLinearMap
    = (hA.Psi (t₁ + t₂) (-r₁ + r₂)).toLinearMap :=
by
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hA.Psi_apply,
    QuantumSet.Psi_toFun_apply, TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
    AlgEquiv.op_apply_apply]
  simp only [QuantumSet.modAut_apply_modAut, MulOpposite.op_star, MulOpposite.unop_star,
    MulOpposite.unop_op, QuantumSet.modAut_star, neg_add, neg_neg]

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
