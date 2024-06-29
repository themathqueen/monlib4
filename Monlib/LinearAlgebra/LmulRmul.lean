/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Algebra.Bilinear
import Monlib.LinearAlgebra.TensorProduct.BasicLemmas

#align_import linear_algebra.lmul_rmul

/-!
 # lmul and rmul (the left and right multiplication maps)

 Basically just copies of `linear_map.mul_left` and `linear_map.mul_right` but defined as linear maps.

-/


section

variable {R E F : Type _} [CommSemiring R] [NonUnitalNonAssocSemiring E]
  [NonUnitalNonAssocSemiring F] [Module R E] [Module R F] [SMulCommClass R E E]
  [SMulCommClass R F F] [IsScalarTower R E E] [IsScalarTower R F F] (f : E ≃* F)

theorem LinearMap.mulLeft_conj_of_mulEquiv (x : E) :
    f ∘ LinearMap.mulLeft R x ∘ f.symm = LinearMap.mulLeft R (f x) :=
  by
  ext
  simp_rw [Function.comp_apply, LinearMap.mulLeft_apply, map_mul, MulEquiv.apply_symm_apply]

theorem LinearMap.mulRight_conj_of_mulEquiv (x : E) :
    f ∘ LinearMap.mulRight R x ∘ f.symm = LinearMap.mulRight R (f x) :=
  by
  ext
  simp_rw [Function.comp_apply, LinearMap.mulRight_apply, map_mul, MulEquiv.apply_symm_apply]

end

local notation "l(" x "," y ")" => y →ₗ[x] y

variable {R H₁ H₂ : Type _} [CommSemiring R]
  -- [semiring H₁] [semiring H₂]
  -- [algebra R H₁] [algebra R H₂]
  [NonUnitalNonAssocSemiring H₁]
  [Module R H₁] [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] [NonUnitalNonAssocSemiring H₂]
  [Module R H₂] [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂]

theorem left_module_map_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] {x : l(R,H₁)} :
    (∀ a b : H₁, x (a * b) = a * x b) ↔ x = LinearMap.mulRight R (x 1) :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.mulRight_apply]
  constructor <;> intro h <;> intros
  · rw [← h, mul_one]
  · rw [h, mul_assoc, ← h]

theorem right_module_map_iff {H₂ : Type _} [Semiring H₂] [Algebra R H₂] {x : l(R,H₂)} :
    (∀ a b : H₂, x (a * b) = x a * b) ↔ x = LinearMap.mulLeft R (x 1) :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.mulLeft_apply]
  constructor <;> intro h <;> intros
  · rw [← h, one_mul]
  · rw [h, ← mul_assoc, ← h]

def lmul : H₁ →ₗ[R] l(R,H₁) where
  toFun x := LinearMap.mulLeft R x
  map_add' x y := by
    ext1
    simp only [LinearMap.mulLeft_apply, add_mul, LinearMap.add_apply]
  map_smul' r x := by
    ext1
    simp only [LinearMap.mulLeft_apply, LinearMap.smul_apply, RingHom.id_apply, smul_mul_assoc]

theorem lmul_apply (x y : H₁) : (lmul x : l(R,H₁)) y = x * y :=
  rfl

theorem lmul_eq_mul (x : H₁) : lmul x = LinearMap.mulLeft R x :=
  rfl

theorem lmul_eq_alg_lmul {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (lmul x : l(R,H₁)) = Algebra.lmul R H₁ x :=
  rfl

theorem lmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] : (lmul (1 : H₁) : l(R,H₁)) = 1 := by
    ext
    simp_rw [lmul_apply, LinearMap.one_apply, one_mul]

def rmul : H₂ →ₗ[R] l(R,H₂) where
  toFun x := LinearMap.mulRight R x
  map_add' x y := by
    ext1
    simp only [LinearMap.mulRight_apply, mul_add, LinearMap.add_apply]
  map_smul' r x := by
    ext1
    simp only [LinearMap.mulRight_apply, LinearMap.smul_apply, RingHom.id_apply, mul_smul_comm]

theorem rmul_apply (x y : H₂) : (rmul x : l(R,H₂)) y = y * x :=
  rfl

theorem rmul_eq_mul (x : H₂) : rmul x = LinearMap.mulRight R x :=
  rfl

theorem rmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] : (rmul (1 : H₁) : l(R,H₁)) = 1 :=
  by
  ext
  simp only [rmul_apply, mul_one, LinearMap.one_apply]

open scoped TensorProduct

local notation x " ⊗ₘ " y => TensorProduct.map x y

noncomputable def rmulMapLmul {R H₁ H₂ : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁]
  [NonUnitalNonAssocSemiring H₂] [Module R H₂] [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂] :
  H₁ ⊗[R] H₂ →ₗ[R] ((H₁ ⊗[R] H₂) →ₗ[R] (H₁ ⊗[R] H₂)) :=
(TensorProduct.homTensorHomMap R H₁ H₂ H₁ H₂) ∘ₗ (TensorProduct.map rmul lmul)

theorem rmulMapLmul_apply (x : H₁) (y : H₂) : rmulMapLmul (x ⊗ₜ[R] y) = rmul x ⊗ₘ lmul y :=
  rfl

theorem rmulMapLmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] {H₂ : Type _} [NonAssocSemiring H₂] [Module R H₂]
    [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂] : rmulMapLmul (1 ⊗ₜ 1 : H₁ ⊗[R] H₂) = 1 :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  simp_rw [rmulMapLmul_apply, TensorProduct.map_tmul, rmul_apply, lmul_apply, mul_one, one_mul,
    LinearMap.one_apply]

open scoped BigOperators

theorem LinearMap.mulLeft_sum {R : Type _} {A : Type _} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    {n : Type _} {s : Finset n} {x : n → A} :
    ∑ i : n in s, LinearMap.mulLeft R (x i) = LinearMap.mulLeft R (∑ i : n in s, x i) :=
by simp_rw [← lmul_eq_mul, map_sum]

theorem LinearMap.mulRight_sum {R : Type _} {A : Type _} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    {n : Type _} {s : Finset n} {x : n → A} :
    ∑ i : n in s, LinearMap.mulRight R (x i) = LinearMap.mulRight R (∑ i : n in s, x i) :=
by simp_rw [← rmul_eq_mul, map_sum]

theorem lmul_eq_zero_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (lmul x : l(R,H₁)) = 0 ↔ x = 0 :=
  LinearMap.mulLeft_eq_zero_iff _

theorem rmul_eq_zero_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (rmul x : l(R,H₁)) = 0 ↔ x = 0 :=
  LinearMap.mulRight_eq_zero_iff _

theorem lmul_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] (x : H₁) : (lmul x : l(R,H₁)) = 1 ↔ x = 1 :=
  by
  simp_rw [LinearMap.ext_iff, lmul_apply, LinearMap.one_apply]
  refine' ⟨fun h => _, fun h a => by rw [h, one_mul]⟩
  · specialize h 1
    rw [mul_one] at h
    exact h

theorem LinearMap.mulLeft_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁]
    [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] (x : H₁) : LinearMap.mulLeft R x = 1 ↔ x = 1 :=
  lmul_eq_one_iff _

theorem rmul_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] (x : H₁) : (rmul x : l(R,H₁)) = 1 ↔ x = 1 :=
  by
  simp_rw [LinearMap.ext_iff, rmul_apply, LinearMap.one_apply]
  refine' ⟨fun h => _, fun h a => by rw [h, mul_one]⟩
  · specialize h 1
    rw [one_mul] at h
    exact h

theorem LinearMap.mulRight_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁]
    [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] (x : H₁) : LinearMap.mulRight R x = 1 ↔ x = 1 :=
  rmul_eq_one_iff _

theorem LinearMap.mulLeft_eq_one_or_zero_iff_mulRight_tfae {H₁ : Type _} [Semiring H₁]
    [Algebra R H₁] (x : H₁) (p : Prop) [Decidable p] :
    List.TFAE [LinearMap.mulLeft R x = ite p 1 0,
      LinearMap.mulRight R x = ite p 1 0, x = ite p 1 0] :=
  by
  by_cases h : p
  · simp_rw [h, if_true, LinearMap.mulLeft_eq_one_iff, LinearMap.mulRight_eq_one_iff]
    tfae_finish
  · simp_rw [h, if_false, LinearMap.mulLeft_eq_zero_iff, LinearMap.mulRight_eq_zero_iff]
    tfae_finish

theorem LinearMap.mulLeft_eq_one_or_zero_iff_mulRight {H₁ : Type _} [Semiring H₁] [Algebra R H₁]
    (x : H₁) (p : Prop) [Decidable p] :
    LinearMap.mulLeft R x = ite p 1 0 ↔ LinearMap.mulRight R x = ite p 1 0 :=
  List.TFAE.out (@LinearMap.mulLeft_eq_one_or_zero_iff_mulRight_tfae R _ H₁ _ _ x p _) 0 1

theorem LinearMap.mulRight_smul (x : H₁) (α : R) :
    LinearMap.mulRight R (α • x) = α • LinearMap.mulRight R x :=
  rmul.map_smul _ _

theorem LinearMap.mulLeft_smul (x : H₁) (α : R) :
    LinearMap.mulLeft R (α • x) = α • LinearMap.mulLeft R x :=
  lmul.map_smul _ _

theorem LinearMap.mulLeft_comp_inj {H₁ H₂ : Type _} [Semiring H₁] [Module R H₁] [AddCommMonoid H₂]
    [Module R H₂] [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] (f g : H₁ →ₗ[R] H₂) (x : H₁)
    [Invertible x] : f ∘ₗ LinearMap.mulLeft R x = g ∘ₗ LinearMap.mulLeft R x ↔ f = g :=
  by
  refine' ⟨_, fun h => by rw [h]⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  intro h y
  specialize h (⅟ x * y)
  simp_rw [← mul_assoc, mul_invOf_self, one_mul] at h
  exact h

theorem LinearMap.mulLeft_inj {H₁ : Type _} [Semiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] (x : H₁) [Invertible x] (y z : H₁) :
    LinearMap.mulLeft R x y = LinearMap.mulLeft R x z ↔ y = z :=
  IsUnit.mul_right_inj (isUnit_of_invertible x)
