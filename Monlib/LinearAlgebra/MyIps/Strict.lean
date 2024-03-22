/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.TensorProduct
import Algebra.Algebra.Bilinear

#align_import linear_algebra.my_ips.strict

/-!
 # Strict tensor product (wip)
-/


variable {R E F G : Type _} [CommSemiring R] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [Module R E] [Module R F] [Module R G]

open scoped TensorProduct

@[instance]
def TensorProduct.assocHasCoe : Coe ((E ⊗[R] F) ⊗[R] G) (E ⊗[R] F ⊗[R] G)
    where coe x := TensorProduct.assoc R E F G x

@[instance]
def TensorProduct.assocSymmHasCoe : Coe (E ⊗[R] F ⊗[R] G) ((E ⊗[R] F) ⊗[R] G)
    where coe x := (TensorProduct.assoc R E F G).symm x

@[simp]
theorem TensorProduct.assoc_tmul_coe (a : E) (b : F) (c : G) :
    (a ⊗ₜ[R] b) ⊗ₜ[R] c = ↑(a ⊗ₜ[R] b ⊗ₜ[R] c) :=
  rfl

theorem TensorProduct.assoc_coe_coe (a : (E ⊗[R] F) ⊗[R] G) : a = ↑(a : E ⊗[R] F ⊗[R] G) := by
  unfold_coes <;> simp only [LinearEquiv.toFun_eq_coe, LinearEquiv.symm_apply_apply]

@[simp]
theorem TensorProduct.tmul_assoc_coe (a : E) (b : F) (c : G) :
    a ⊗ₜ[R] b ⊗ₜ[R] c = ↑((a ⊗ₜ[R] b) ⊗ₜ[R] c) :=
  rfl

theorem TensorProduct.coe_coe_assoc (a : E ⊗[R] F ⊗[R] G) : a = ↑(a : (E ⊗[R] F) ⊗[R] G) := by
  unfold_coes <;> simp only [LinearEquiv.toFun_eq_coe, LinearEquiv.apply_symm_apply]

@[instance]
def TensorProduct.lidHasCoe : Coe (R ⊗[R] E) E where coe x := TensorProduct.lid R E x

@[instance]
def TensorProduct.ridHasCoe : Coe (E ⊗[R] R) E where coe x := TensorProduct.rid R E x

@[instance]
def TensorProduct.lidSymmHasCoe : Coe E (R ⊗[R] E) where coe x := (TensorProduct.lid R E).symm x

@[instance]
def TensorProduct.ridSymmHasCoe : Coe E (E ⊗[R] R) where coe x := (TensorProduct.rid R E).symm x

theorem TensorProduct.lid_coe (x : E) (r : R) : ↑(r ⊗ₜ[R] x) = r • x :=
  rfl

theorem TensorProduct.rid_coe (x : E) (r : R) : ↑(x ⊗ₜ[R] r) = r • x :=
  rfl

theorem TensorProduct.lid_symm_coe (x : E) : (x : R ⊗[R] E) = (1 : R) ⊗ₜ[R] x :=
  rfl

theorem TensorProduct.rid_symm_coe (x : E) : (x : E ⊗[R] R) = x ⊗ₜ[R] (1 : R) :=
  rfl

theorem TensorProduct.lid_coe' (x : E) (r : R) : r ⊗ₜ[R] x = r • x := by
  rw [TensorProduct.lid_symm_coe, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem TensorProduct.rid_coe' (x : E) (r : R) : x ⊗ₜ[R] r = r • x := by
  rw [TensorProduct.rid_symm_coe, TensorProduct.smul_tmul', TensorProduct.smul_tmul, smul_eq_mul,
    mul_one]

theorem TensorProduct.lid_coe_rid_coe (x : E) : (x : R ⊗[R] E) = (x : E ⊗[R] R) :=
  by
  unfold_coes
  simp only [LinearEquiv.toFun_eq_coe, LinearEquiv.apply_symm_apply]

@[instance]
def funTensorProductAssocHasCoe {A : Type _} : Coe ((E ⊗[R] F) ⊗[R] G → A) (E ⊗[R] F ⊗[R] G → A)
    where coe f x := f x

@[instance]
def LinearMap.tensorProductAssocHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe ((E ⊗[R] F) ⊗[R] G →ₗ[R] A) (E ⊗[R] F ⊗[R] G →ₗ[R] A)
    where coe f :=
    f ∘ₗ
      (((TensorProduct.assoc R E F G).symm : E ⊗[R] F ⊗[R] G ≃ₗ[R] (E ⊗[R] F) ⊗[R] G) :
        E ⊗[R] F ⊗[R] G →ₗ[R] (E ⊗[R] F) ⊗[R] G)

@[instance]
def funTensorProductAssocHasCoe' {A : Type _} : Coe (E ⊗[R] F ⊗[R] G → A) ((E ⊗[R] F) ⊗[R] G → A)
    where coe f x := f x

@[instance]
def LinearMap.tensorProductAssocHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E ⊗[R] F ⊗[R] G →ₗ[R] A) ((E ⊗[R] F) ⊗[R] G →ₗ[R] A)
    where coe f :=
    f ∘ₗ
      ((TensorProduct.assoc R E F G : (E ⊗[R] F) ⊗[R] G ≃ₗ[R] E ⊗[R] F ⊗[R] G) :
        (E ⊗[R] F) ⊗[R] G →ₗ[R] E ⊗[R] F ⊗[R] G)

@[instance]
def funLidHasCoe {A : Type _} : Coe (R ⊗[R] E → A) (E → A) where coe f x := f x

@[instance]
def LinearMap.tensorProductLidHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (R ⊗[R] E →ₗ[R] A) (E →ₗ[R] A) where coe f := f ∘ₗ ↑(TensorProduct.lid R E).symm

@[instance]
def funLidHasCoe' {A : Type _} : Coe (E → A) (R ⊗[R] E → A) where coe f x := f x

@[instance]
def LinearMap.tensorProductLidHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E →ₗ[R] A) (R ⊗[R] E →ₗ[R] A) where coe f := f ∘ₗ ↑(TensorProduct.lid R E)

@[instance]
def funRidHasCoe {A : Type _} : Coe (E ⊗[R] R → A) (E → A) where coe f x := f x

@[instance]
def LinearMap.tensorProductRidHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E ⊗[R] R →ₗ[R] A) (E →ₗ[R] A) where coe f := f ∘ₗ ↑(TensorProduct.rid R E).symm

@[instance]
def funRidHasCoe' {A : Type _} : Coe (E → A) (E ⊗[R] R → A) where coe f x := f x

@[instance]
def LinearMap.tensorProductRidHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E →ₗ[R] A) (E ⊗[R] R →ₗ[R] A) where coe f := f ∘ₗ ↑(TensorProduct.rid R E)

theorem LinearMap.lid_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E →ₗ[R] A) :
    f = (f : R ⊗[R] E →ₗ[R] A) := by
  unfold_coes <;>
    ·
      simp only [LinearMap.comp_assoc, LinearEquiv.toLinearMap_eq_coe, LinearEquiv.comp_coe,
        LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

theorem LinearMap.lid_symm_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : R ⊗[R] E →ₗ[R] A) :
    f = (f : E →ₗ[R] A) := by
  unfold_coes <;>
    ·
      simp only [LinearMap.comp_assoc, LinearEquiv.toLinearMap_eq_coe, LinearEquiv.comp_coe,
        LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

theorem LinearMap.rid_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E →ₗ[R] A) :
    f = (f : E ⊗[R] R →ₗ[R] A) := by
  unfold_coes <;>
    ·
      simp only [LinearMap.comp_assoc, LinearEquiv.toLinearMap_eq_coe, LinearEquiv.comp_coe,
        LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

theorem LinearMap.rid_symm_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E ⊗[R] R →ₗ[R] A) :
    f = (f : E →ₗ[R] A) := by
  unfold_coes <;>
    ·
      simp only [LinearMap.comp_assoc, LinearEquiv.toLinearMap_eq_coe, LinearEquiv.comp_coe,
        LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

example {A : Type _} (f : E ⊗[R] F ⊗[R] G → A) (g : (E ⊗[R] F) ⊗[R] G → A) :
    f = ↑(↑f : (E ⊗[R] F) ⊗[R] G → A) := by
  unfold_coes
  simp only [LinearEquiv.toFun_eq_coe, LinearEquiv.apply_symm_apply]

