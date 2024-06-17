import Monlib.LinearAlgebra.QuantumSet.SchurMul
import Monlib.LinearAlgebra.QuantumSet.Symm
import Monlib.LinearAlgebra.tensorProduct
import Monlib.LinearAlgebra.Ips.MinimalProj

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

lemma AlgEquiv.TensorProduct.map_toLinearMap
    {R : Type _} [CommSemiring R] {A B C D : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) :
  (AlgEquiv.TensorProduct.map f g).toLinearMap = f.toLinearMap ⊗ₘ g.toLinearMap :=
rfl

open scoped TensorProduct

lemma AlgEquiv.TensorProduct.map_map_toLinearMap
  {R : Type _} [CommSemiring R] {A B C D E F : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Semiring E] [Semiring F]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R F]
    (h : B ≃ₐ[R] E) (i : D ≃ₐ[R] F) (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x : A ⊗[R] C) :
  (AlgEquiv.TensorProduct.map h i) ((AlgEquiv.TensorProduct.map f g) x)
    = (AlgEquiv.TensorProduct.map (f.trans h) (g.trans i)) x :=
by
  simp only [TensorProduct.map, toAlgHom_eq_coe, coe_mk, Algebra.TensorProduct.map_apply_map_apply]
  rfl

lemma AlgEquiv.op_trans {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
  (AlgEquiv.op f).trans (AlgEquiv.op g) = AlgEquiv.op (f.trans g) :=
rfl
lemma AlgEquiv.op_one {R A : Type*} [CommSemiring R] [Semiring A]
  [Algebra R A] :
  AlgEquiv.op (1 : A ≃ₐ[R] A) = 1 :=
rfl
lemma AlgEquiv.TensorProduct.map_one {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] :
  AlgEquiv.TensorProduct.map (1 : A ≃ₐ[R] A) (1 : B ≃ₐ[R] B) = 1 :=
by
  rw [AlgEquiv.ext_iff]
  simp_rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.ext_iff]
  simp only [map_toLinearMap, one_toLinearMap, _root_.TensorProduct.map_one]

lemma isReal_iff_Psi {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
    [hA : QuantumSet A] [hB : QuantumSet B] (f : A →ₗ[ℂ] B) (t r : ℝ) :
  f.IsReal ↔ star (hA.Psi t r f) = hA.Psi (-t) (1 - r) f :=
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
  f.IsReal ↔ IsSelfAdjoint (hA.Psi 0 (1 / 2) f) :=
by
  rw [_root_.IsSelfAdjoint, isReal_iff_Psi f 0 (1 / 2)]
  norm_num

class schurProjection {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [hA : QuantumSet A] [hB : QuantumSet B] (f : A →ₗ[ℂ] B) :
    Prop :=
  isIdempotentElem : f •ₛ f = f
  isReal : f.IsReal

lemma ContinuousLinearMap.isOrthogonalProjection_iff
  {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) :
  T.IsOrthogonalProjection ↔ IsIdempotentElem T ∧ LinearMap.ker T = (LinearMap.range T)ᗮ :=
⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

lemma lmul_isIdempotentElem_iff {R A : Type*} [CommSemiring R]
  [Semiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (a : A) :
  (IsIdempotentElem (lmul a : _ →ₗ[R] _)) ↔ (IsIdempotentElem a) :=
by
  simp_rw [IsIdempotentElem, LinearMap.mul_eq_comp, lmul_eq_mul, ← LinearMap.mulLeft_mul]
  refine ⟨λ h => ?_, λ h => by rw [h]⟩
  rw [LinearMap.ext_iff] at h
  specialize h 1
  simp_rw [LinearMap.mulLeft_apply, mul_one] at h
  exact h

lemma lmul_isSelfAdjoint_iff {A : Type*} [NormedAddCommGroupOfRing A]
    [hA : QuantumSet A] (a : A) :
  IsSelfAdjoint (lmul a : _ →ₗ[ℂ] _) ↔ IsSelfAdjoint a :=
by
  rw [IsSelfAdjoint, LinearMap.star_eq_adjoint, lmul_adjoint, LinearMap.ext_iff]
  refine ⟨λ h => ?_, λ h a => by rw [h]⟩
  specialize h 1
  simp_rw [lmul_apply, mul_one] at h
  exact h

lemma lmul_tmul {R A B : Type*} [CommSemiring R]
  [Semiring A] [Semiring B] [Module R A] [Module R B] [SMulCommClass R A A]
  [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B] (a : A) (b : B) :
  lmul (a ⊗ₜ[R] b) = lmul a ⊗ₘ lmul b :=
rfl

lemma lmul_tmul_adjoint_aux {A B : Type*} [NormedAddCommGroupOfRing A]
  [NormedAddCommGroupOfRing B] [hA : QuantumSet A] [hB : QuantumSet B]
  (a : A) (b : B) :
  LinearMap.adjoint (lmul (a ⊗ₜ[ℂ] b)) = lmul (star a) ⊗ₘ lmul (star b) :=
by
  rw [TensorProduct.ext_iff]
  intro c d
  rw [TensorProduct.inner_ext_iff']
  intro e f
  simp_rw [LinearMap.adjoint_inner_left, lmul_tmul, TensorProduct.map_tmul,
    TensorProduct.inner_tmul, lmul_apply, QuantumSet.inner_star_left, star_star]
lemma lmul_tmul_adjoint {A B : Type*} [NormedAddCommGroupOfRing A]
  [NormedAddCommGroupOfRing B] [hA : QuantumSet A] [hB : QuantumSet B]
  (a : A ⊗[ℂ] B) :
  LinearMap.adjoint (lmul a) = (lmul (star a) : _ →ₗ[ℂ] _) :=
by
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span a
  rw [← h]
  simp_rw [map_sum, lmul_tmul_adjoint_aux, star_sum, map_sum, ← lmul_tmul,
    TensorProduct.star_tmul]

lemma lmul_eq_lmul_iff {R A : Type*} [CommSemiring R]
  [Semiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (a b : A) :
  lmul a = (lmul b : _ →ₗ[R] _) ↔ a = b :=
by
  refine ⟨λ h => ?_, λ h => by rw [h]⟩
  rw [LinearMap.ext_iff] at h
  specialize h 1
  simp_rw [lmul_apply, mul_one] at h
  exact h

lemma lmul_isSelfAdjoint_iff' {A B : Type*} [NormedAddCommGroupOfRing A]
  [NormedAddCommGroupOfRing B]
  [hA : QuantumSet A] [hB : QuantumSet B] (a : A ⊗[ℂ] B) :
  IsSelfAdjoint (lmul a : _ →ₗ[ℂ] _) ↔ IsSelfAdjoint a :=
by
  rw [IsSelfAdjoint, LinearMap.star_eq_adjoint, lmul_tmul_adjoint, lmul_eq_lmul_iff]
  rfl

open scoped FiniteDimensional
theorem ContinuousLinearMap.isOrthogonalProjection_iff'
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {p : E →L[ℂ] E} :
  IsOrthogonalProjection p
  ↔ IsIdempotentElem p ∧ IsSelfAdjoint p :=
by

  rw [isOrthogonalProjection_iff]
  simp only [and_congr_right_iff]
  intro h
  have := List.TFAE.out (IsIdempotentElem.self_adjoint_is_positive_isOrthogonalProjection_tFAE h) 0 1
  rw [this, isOrthogonalProjection_iff]
  simp only [h, true_and]

lemma LinearMap.isSelfAdjoint_toContinuousLinearMap
  {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  (f : E →ₗ[𝕜] E) :
    _root_.IsSelfAdjoint (LinearMap.toContinuousLinearMap f) ↔ _root_.IsSelfAdjoint f :=
by
  simp_rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, isSymmetric_iff_isSelfAdjoint]
  rfl

lemma LinearMap.isOrthogonalProjection_iff
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
  (T : E →ₗ[ℂ] E) :
  (LinearMap.toContinuousLinearMap T).IsOrthogonalProjection
    ↔ IsIdempotentElem T ∧ IsSelfAdjoint T :=
by rw [ContinuousLinearMap.isOrthogonalProjection_iff',
  isSelfAdjoint_toContinuousLinearMap,
  ContinuousLinearMap.IsIdempotentElem.toLinearMap]; simp only [coe_toContinuousLinearMap]

-- lemma schurProjection_submodule {A B : Type*} [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
--     [hA : QuantumSet A] [hB : QuantumSet B]
--     (f : A →ₗ[ℂ] B) :
--     schurProjection f ↔
--   ContinuousLinearMap.IsOrthogonalProjection
--     (LinearMap.toContinuousLinearMap
--       (lmul (hA.Psi 0 (1 / 2) f) : _ →ₗ[ℂ] _)) :=
-- by
--   rw [LinearMap.isOrthogonalProjection_iff, lmul_isIdempotentElem_iff,
--     ← schurIdempotent_iff_Psi_isIdempotentElem, lmul_isSelfAdjoint_iff']
