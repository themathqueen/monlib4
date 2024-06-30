import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Opposites
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Opposite

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

@[simp]
theorem AlgEquiv.op_toLinearMap
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B] (f : A ≃ₐ[R] B) :
  f.op.toLinearMap = f.toLinearMap.op :=
rfl
