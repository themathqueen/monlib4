/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Monlib.Preq.Finset
import Monlib.LinearAlgebra.MyIps.Basic

#align_import linear_algebra.my_ips.tensor_hilbert

/-!

 # Tensor product of inner product spaces

  This file constructs the tensor product of finite-dimensional inner product spaces.

-/


section

variable {𝕜 E F : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

open scoped TensorProduct BigOperators

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
noncomputable instance TensorProduct.Inner : Inner 𝕜 (E ⊗[𝕜] F)
  where inner := fun x y : E ⊗[𝕜] F =>
    ∑ i, ∑ j,
      star ((((stdOrthonormalBasis 𝕜 E).toBasis.tensorProduct (stdOrthonormalBasis 𝕜 F).toBasis).repr x) (i, j)) *
        (((stdOrthonormalBasis 𝕜 E).toBasis.tensorProduct (stdOrthonormalBasis 𝕜 F).toBasis).repr y) (i, j)

-- lemma orthonormal.to_basis_tensor_product {n m : Type*} [fintype n] [fintype m]
--   (b₁ : orthonormal_basis n 𝕜 E) (b₂ : orthonormal_basis m 𝕜 F) :
--   (b₁.to_basis.tensor_product b₂.to_basis).repr
theorem TensorProduct.inner_tmul (x z : E) (y w : F) :
    (inner (x ⊗ₜ[𝕜] y) (z ⊗ₜ[𝕜] w) : 𝕜) = inner x z * inner y w := by
  simp_rw [inner, Basis.tensorProduct_repr_tmul_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    star_mul', RCLike.star_def, OrthonormalBasis.repr_apply_apply,
    inner_conj_symm, mul_mul_mul_comm, ← Finset.mul_sum, ← Finset.sum_mul, OrthonormalBasis.sum_inner_mul_inner]

protected theorem TensorProduct.inner_add_left (x y z : E ⊗[𝕜] F) :
    (inner (x + y) z : 𝕜) = inner x z + inner y z := by
  simp_rw [inner, ← Finset.sum_add_distrib, map_add, Finsupp.add_apply, star_add, add_mul]

protected theorem TensorProduct.inner_zero_right (x : E ⊗[𝕜] F) :
    (inner x (0 : E ⊗[𝕜] F) : 𝕜) = 0 :=
  x.induction_on
  (by simp_rw [← TensorProduct.zero_tmul E (0 : F), TensorProduct.inner_tmul,
    inner_zero_left, MulZeroClass.zero_mul])
  (fun _ _ => by
    simp_rw [← TensorProduct.zero_tmul E (0 : F),
      TensorProduct.inner_tmul, inner_zero_right, MulZeroClass.mul_zero])
  (fun a b ha hb =>
    by simp_rw [TensorProduct.inner_add_left, ha, hb, add_zero])

protected theorem TensorProduct.inner_conj_symm (x y : E ⊗[𝕜] F) :
    starRingEnd 𝕜 (inner x y : 𝕜) = inner y x := by
  simp_rw [inner, starRingEnd_apply, star_sum, star_mul', star_star, mul_comm]

protected theorem TensorProduct.inner_zero_left (x : E ⊗[𝕜] F) : (inner (0 : E ⊗[𝕜] F) x : 𝕜) = 0 :=
  by rw [← TensorProduct.inner_conj_symm, TensorProduct.inner_zero_right, map_zero]

protected theorem TensorProduct.inner_add_right (x y z : E ⊗[𝕜] F) :
    (inner x (y + z) : 𝕜) = inner x y + inner x z := by
  rw [← TensorProduct.inner_conj_symm, TensorProduct.inner_add_left, map_add,
    TensorProduct.inner_conj_symm, TensorProduct.inner_conj_symm]

protected theorem TensorProduct.inner_sum {n : Type _} [Fintype n] (x : n → E ⊗[𝕜] F)
    (y : E ⊗[𝕜] F) : (inner (∑ i, x i) y : 𝕜) = ∑ i, inner (x i) y :=
  by
  simp_rw [inner, map_sum, Finset.sum_apply', star_sum, Finset.sum_mul]
  rw [Finset.sum_rotate]

protected theorem TensorProduct.sum_inner {n : Type _} [Fintype n] (y : E ⊗[𝕜] F)
    (x : n → E ⊗[𝕜] F) : (inner y (∑ i, x i) : 𝕜) = ∑ i, inner y (x i) := by
  rw [← TensorProduct.inner_conj_symm, TensorProduct.inner_sum, map_sum]
  simp_rw [TensorProduct.inner_conj_symm]

protected theorem TensorProduct.inner_nonneg_re (x : E ⊗[𝕜] F) : 0 ≤ RCLike.re (inner x x : 𝕜) :=
  by
  simp_rw [inner, map_sum, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re, ←
    Finset.sum_product', Finset.univ_product_univ, Prod.mk.eta]
  apply Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem TensorProduct.eq_span {𝕜 E F : Type _} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (x : E ⊗[𝕜] F) :
    ∃ (α : Basis.ofVectorSpaceIndex 𝕜 E × Basis.ofVectorSpaceIndex 𝕜 F → E) (β :
      Basis.ofVectorSpaceIndex 𝕜 E × Basis.ofVectorSpaceIndex 𝕜 F → F), ∑ i, α i ⊗ₜ[𝕜] β i = x :=
  by
  let b₁ := Basis.ofVectorSpace 𝕜 E
  let b₂ := Basis.ofVectorSpace 𝕜 F
  rw [← Basis.sum_repr (b₁.tensorProduct b₂) x]
  simp_rw [Basis.tensorProduct_apply', TensorProduct.smul_tmul']
  exact ⟨fun i => ((b₁.tensorProduct b₂).repr x) i • b₁ i.fst, fun i => b₂ i.snd, rfl⟩

@[instance, reducible]
noncomputable def TensorProduct.normedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 (E ⊗[𝕜] F) _ _ _
    { inner := (⟪·, ·⟫_𝕜)
      conj_symm := fun x y => y.inner_conj_symm x
      nonneg_re := fun x => x.inner_nonneg_re
      definite := fun x hx =>
        by
        simp_rw [inner, RCLike.star_def, RCLike.conj_mul, ← Finset.sum_product',
          Finset.univ_product_univ, Prod.mk.eta, ← RCLike.ofReal_pow,
          ← RCLike.ofReal_sum, RCLike.ofReal_eq_zero] at hx
        rw [Finset.sum_eq_zero_iff_of_nonneg] at hx
        · simp_rw [sq_eq_zero_iff, norm_eq_zero, Finset.mem_univ, true_imp_iff] at hx
          apply
            Basis.ext_elem
              ((stdOrthonormalBasis 𝕜 E).toBasis.tensorProduct (stdOrthonormalBasis 𝕜 F).toBasis)
          simp_rw [map_zero, Finsupp.zero_apply]
          exact hx
        · exact fun _  _ => sq_nonneg _
      add_left := fun x y z => x.inner_add_left _ _
      smul_left := fun x y r => by
        obtain ⟨α, β, rfl⟩ := x.eq_span
        obtain ⟨γ, ζ, rfl⟩ := y.eq_span
        simp_rw [Finset.smul_sum, TensorProduct.sum_inner, TensorProduct.inner_sum,
          smul_tmul', inner_tmul, inner_smul_left, Finset.mul_sum, mul_assoc] }

@[instance, reducible]
noncomputable def TensorProduct.innerProductSpace :
    @InnerProductSpace 𝕜 (E ⊗[𝕜] F) _ TensorProduct.normedAddCommGroup :=
  InnerProductSpace.ofCore _

example (α β : 𝕜) (x y : E) :
    TensorProduct.innerProductSpace.inner (α ⊗ₜ[𝕜] x) (β ⊗ₜ[𝕜] y) = inner α β * inner x y :=
  TensorProduct.inner_tmul _ _ _ _

theorem TensorProduct.lid_adjoint :
    LinearMap.adjoint (TensorProduct.lid 𝕜 E : 𝕜 ⊗[𝕜] E →ₗ[𝕜] E) = (TensorProduct.lid 𝕜 E).symm :=
  by
  ext1
  apply @ext_inner_right 𝕜
  intro y
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
  exact y.induction_on
    (by simp only [inner_zero_right, map_zero])
    (fun α z => by
      simp only [TensorProduct.lid_tmul, TensorProduct.inner_tmul, RCLike.inner_apply,
        starRingEnd_apply, star_one, one_mul, inner_smul_right])
    (fun z w hz hw => by simp only [map_add, inner_add_right, hz, hw])

theorem TensorProduct.comm_adjoint :
    LinearMap.adjoint (TensorProduct.comm 𝕜 E F : E ⊗[𝕜] F →ₗ[𝕜] F ⊗[𝕜] E) =
      (TensorProduct.comm 𝕜 E F).symm :=
  by
  apply TensorProduct.ext'
  intro x y
  apply @ext_inner_right 𝕜
  intro z
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.comm_symm_tmul]
  exact z.induction_on
    (by simp only [inner_zero_right, map_zero])
    (fun α z => by simp only [TensorProduct.comm_tmul, TensorProduct.inner_tmul, mul_comm])
    (fun z w hz hw => by simp only [map_add, inner_add_right, hz, hw])

theorem TensorProduct.assoc_symm_adjoint {G : Type _} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] :
    LinearMap.adjoint ((TensorProduct.assoc 𝕜 E F G).symm : E ⊗[𝕜] F ⊗[𝕜] G →ₗ[𝕜] (E ⊗[𝕜] F) ⊗[𝕜] G)
      = TensorProduct.assoc 𝕜 E F G :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  apply @ext_inner_right 𝕜
  intro w
  obtain ⟨w₁, w₂, rfl⟩ := w.eq_span
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.assoc_tmul, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨w₃, w₄, hw⟩ := (w₂ i).eq_span
  simp only [← hw, TensorProduct.assoc_symm_tmul, TensorProduct.tmul_sum, map_sum, inner_sum,
    TensorProduct.inner_tmul, mul_assoc]

theorem TensorProduct.assoc_adjoint {G : Type _} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] :
    LinearMap.adjoint (TensorProduct.assoc 𝕜 E F G : (E ⊗[𝕜] F) ⊗[𝕜] G →ₗ[𝕜] E ⊗[𝕜] F ⊗[𝕜] G)
      = (TensorProduct.assoc 𝕜 E F G).symm :=
  by
  have := @TensorProduct.assoc_symm_adjoint 𝕜 E F _ _ _ _ _ _ _ G _ _ _
  apply_fun LinearMap.adjoint at this
  rw [LinearMap.adjoint_adjoint] at this
  exact this.symm

theorem TensorProduct.map_adjoint {A B C D : Type _} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [NormedAddCommGroup D] [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B]
    [InnerProductSpace 𝕜 C] [InnerProductSpace 𝕜 D] [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] [FiniteDimensional 𝕜 D] (f : A →ₗ[𝕜] B) (g : C →ₗ[𝕜] D) :
    LinearMap.adjoint (TensorProduct.map f g) = TensorProduct.map (LinearMap.adjoint f) (LinearMap.adjoint g) :=
  by
  apply TensorProduct.ext'
  intro x y
  apply @ext_inner_right 𝕜
  intro z
  obtain ⟨w₁, w₂, rfl⟩ := z.eq_span
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.map_tmul, inner_sum, TensorProduct.inner_tmul]

theorem TensorProduct.inner_ext_iff (x z : E) (y w : F) :
    x ⊗ₜ y = z ⊗ₜ[𝕜] w ↔
      ∀ (a : E) (b : F), inner (x ⊗ₜ[𝕜] y) (a ⊗ₜ[𝕜] b) = (inner (z ⊗ₜ[𝕜] w) (a ⊗ₜ[𝕜] b) : 𝕜) :=
  by
  refine' ⟨fun h a b => by rw [h], fun h => _⟩
  apply @ext_inner_right 𝕜
  intro z
  obtain ⟨w₁, w₂, rfl⟩ := z.eq_span
  simp_rw [inner_sum]
  apply Finset.sum_congr rfl
  intros
  rw [h]

theorem TensorProduct.forall_inner_eq_zero {𝕜 E F : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (x : E ⊗[𝕜] F) :
    (∀ (a : E) (b : F), (inner x (a ⊗ₜ[𝕜] b) : 𝕜) = 0) ↔ x = 0 :=
  by
  refine' ⟨fun h => _, fun h a b => by rw [h, inner_zero_left]⟩
  rw [← @forall_inner_eq_zero_iff 𝕜]
  exact fun y => y.induction_on (inner_zero_right _) h
    (fun c d hc hd => by rw [inner_add_right, hc, hd, add_zero])

theorem TensorProduct.inner_ext_iff' {𝕜 E F : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (x y : E ⊗[𝕜] F) :
    x = y ↔ ∀ (a : E) (b : F), inner x (a ⊗ₜ[𝕜] b) = (inner y (a ⊗ₜ[𝕜] b) : 𝕜) := by
  simp_rw [← @sub_eq_zero 𝕜 _ _ (inner _ _ : 𝕜), ← inner_sub_left,
    TensorProduct.forall_inner_eq_zero, sub_eq_zero]

theorem TensorProduct.lid_symm_adjoint {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    LinearMap.adjoint (TensorProduct.lid 𝕜 E).symm
      = (TensorProduct.lid 𝕜 E : 𝕜 ⊗[𝕜] E →ₗ[𝕜] E) :=
  by
  have := @TensorProduct.lid_adjoint 𝕜 E _ _ _ _
  apply_fun LinearMap.adjoint at this
  rw [LinearMap.adjoint_adjoint] at this
  exact this.symm

theorem TensorProduct.comm_symm_adjoint {𝕜 E V : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 V] :
    LinearMap.adjoint (TensorProduct.comm 𝕜 E V).symm
      = (TensorProduct.comm 𝕜 E V : E ⊗[𝕜] V →ₗ[𝕜] V ⊗[𝕜] E) :=
  by
  have := @TensorProduct.comm_adjoint 𝕜 E V _ _ _ _ _ _ _
  apply_fun LinearMap.adjoint at this
  rw [LinearMap.adjoint_adjoint] at this
  exact this.symm

end
