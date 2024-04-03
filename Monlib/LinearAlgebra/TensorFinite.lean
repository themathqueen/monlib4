/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.RCLike.Basic
import Monlib.LinearAlgebra.IsReal
import Monlib.LinearAlgebra.MyIps.OpUnop
import Monlib.LinearAlgebra.MyIps.MulOp

#align_import linear_algebra.tensor_finite

/-!

# tensor_finite

This file defines the star operation on a tensor product of finite-dimensional star-modules $E,F$,
i.e., ${(x \otimes y)}^*=x^* \otimes y^*$ for $x\in{E}$ and $x\in{F}$.

-/


open scoped TensorProduct BigOperators

section

variable {𝕜 E F G : Type _} [Field 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [StarAddMonoid E] [StarAddMonoid F] [StarAddMonoid G] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
  [StarRing 𝕜] [StarModule 𝕜 G] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [FiniteDimensional 𝕜 G]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
noncomputable instance TensorProduct.Star : Star (E ⊗[𝕜] F)
  where
    star := fun x =>
      let b₁ := Basis.ofVectorSpace 𝕜 E
      let b₂ := Basis.ofVectorSpace 𝕜 F
      ∑ i, ∑ j, star (((b₁.tensorProduct b₂).repr x) (i, j))
        • star (b₁ i) ⊗ₜ[𝕜] star (b₂ j)

@[simp]
theorem TensorProduct.star_tmul [StarModule 𝕜 E] [StarModule 𝕜 F] (x : E) (y : F) :
    star (x ⊗ₜ[𝕜] y) = star x ⊗ₜ[𝕜] star y := by
  simp_rw [star, Basis.tensorProduct_repr_tmul_apply, star_mul',
    mul_comm _ (star (((Basis.ofVectorSpace 𝕜 F).repr y) _)), TensorProduct.smul_tmul', ← smul_smul,
    TensorProduct.smul_tmul (star (((Basis.ofVectorSpace 𝕜 F).repr y) _)), ← TensorProduct.tmul_sum,
    ← TensorProduct.sum_tmul, ← @StarModule.star_smul 𝕜, ← star_sum, Basis.sum_repr]

theorem TensorProduct.star_add
  (x y : E ⊗[𝕜] F) : star (x + y) = star x + star y :=
by
  simp only [star, _root_.map_add, add_smul, StarAddMonoid.star_add, Finsupp.add_apply, Finset.sum_add_distrib]

def TensorProduct.star_is_involutive [StarModule 𝕜 E] [StarModule 𝕜 F] :
    Function.Involutive (TensorProduct.Star.star : E ⊗[𝕜] F → E ⊗[𝕜] F) :=
fun a => a.induction_on
  (by simp only [star, map_zero, Finsupp.zero_apply, star_zero, zero_smul, Finset.sum_const_zero])
  (fun x y => by simp_rw [TensorProduct.star_tmul, star_star])
  (fun x y hx hy => by
    nth_rw 2 [← hx]
    nth_rw 2 [← hy]
    simp_rw [← TensorProduct.star_add])

@[instance]
noncomputable def TensorProduct.InvolutiveStar [StarModule 𝕜 E] [StarModule 𝕜 F] :
    InvolutiveStar (E ⊗[𝕜] F)
    where
  star := TensorProduct.Star.star
  star_involutive := TensorProduct.star_is_involutive

@[instance]
noncomputable def TensorProduct.starAddMonoid [StarModule 𝕜 E] [StarModule 𝕜 F] :
    StarAddMonoid (E ⊗[𝕜] F)
    where
  star_involutive := TensorProduct.InvolutiveStar.star_involutive
  star_add := TensorProduct.star_add

@[instance]
def TensorProduct.starModule : StarModule 𝕜 (E ⊗[𝕜] F)
  where star_smul := fun r α => by simp only [star, map_smul, Finsupp.smul_apply,
    star_smul, smul_assoc, ← Finset.smul_sum]

theorem TensorProduct.map_real {A B E F : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup E]
    [AddCommGroup F] [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid E] [StarAddMonoid F]
    [Module 𝕜 A] [Module 𝕜 B] [Module 𝕜 E] [Module 𝕜 F] [StarModule 𝕜 A] [StarModule 𝕜 B]
    [StarModule 𝕜 E] [StarModule 𝕜 F] [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F) (g : A →ₗ[𝕜] B) :
    (TensorProduct.map f g).real = TensorProduct.map f.real g.real :=
  by
  rw [TensorProduct.ext_iff]
  intro x y
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, TensorProduct.map_tmul]


variable (A : Type _) [Ring A] [Module 𝕜 A] [StarRing A] [StarModule 𝕜 A] [SMulCommClass 𝕜 A A]
  [IsScalarTower 𝕜 A A] [FiniteDimensional 𝕜 A]

theorem LinearMap.mul'_real :
    (LinearMap.mul' 𝕜 A).real = LinearMap.mul' 𝕜 A ∘ₗ (TensorProduct.comm 𝕜 A A).toLinearMap :=
  by
  rw [TensorProduct.ext_iff]
  intro a b
  simp only [LinearMap.real_apply, TensorProduct.star_tmul,
    LinearEquiv.coe_coe, LinearMap.comp_apply, TensorProduct.comm_tmul, LinearMap.mul'_apply,
    star_mul, star_star]

variable [StarModule 𝕜 E] [StarModule 𝕜 F]

theorem TensorProduct.assoc_real :
    (TensorProduct.assoc 𝕜 E F G : (E ⊗[𝕜] F) ⊗[𝕜] G →ₗ[𝕜] E ⊗[𝕜] F ⊗[𝕜] G).real =
      TensorProduct.assoc 𝕜 E F G :=
  by
  apply TensorProduct.ext_threefold
  intro a b c
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, LinearEquiv.coe_coe,
    TensorProduct.assoc_tmul, star_star]

theorem TensorProduct.comm_real :
    (TensorProduct.comm 𝕜 E F : E ⊗[𝕜] F →ₗ[𝕜] F ⊗[𝕜] E).real = TensorProduct.comm 𝕜 E F :=
  by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, star_star]

theorem TensorProduct.lid_real :
    (TensorProduct.lid 𝕜 E : 𝕜 ⊗[𝕜] E →ₗ[𝕜] E).real = TensorProduct.lid 𝕜 E :=
  by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, star_star, star_smul]

theorem TensorProduct.rid_real :
    (TensorProduct.rid 𝕜 E : E ⊗[𝕜] 𝕜 →ₗ[𝕜] E).real = TensorProduct.rid 𝕜 E :=
  by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, star_star, star_smul]

theorem tensor_op_star_apply (x : E) (y : Eᵐᵒᵖ) :
    star (x ⊗ₜ[𝕜] y) = star x ⊗ₜ[𝕜] (op : E →ₗ[𝕜] Eᵐᵒᵖ) (star ((unop : Eᵐᵒᵖ →ₗ[𝕜] E) y)) :=
  by
  simp only [TensorProduct.star_tmul]
  rfl

theorem tenSwap_star (x : E ⊗[𝕜] Eᵐᵒᵖ) : star (tenSwap x) = tenSwap (star x) :=
x.induction_on
  (by simp only [star_zero, map_zero])
  (fun _ _ => by
    simp only [tenSwap_apply, tensor_op_star_apply, unop_apply, op_apply, MulOpposite.unop_op,
      MulOpposite.op_unop])
  (fun z w hz hw => by simp only [map_add, StarAddMonoid.star_add, hz, hw])

end
