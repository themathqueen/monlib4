/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Analysis.InnerProductSpace.Basic
import Analysis.InnerProductSpace.PiL2
import Analysis.InnerProductSpace.Adjoint
import Preq.Finset
import LinearAlgebra.MyIps.Basic

#align_import linear_algebra.my_ips.tensor_hilbert

/-!

 # Tensor product of inner product spaces

  This file constructs the tensor product of finite-dimensional inner product spaces.

-/


section

variable {𝕜 E F : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

open scoped TensorProduct BigOperators

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
noncomputable instance TensorProduct.hasInner : Inner 𝕜 (E ⊗[𝕜] F)
    where inner := fun x y : E ⊗[𝕜] F =>
    by
    let b₁ := stdOrthonormalBasis 𝕜 E
    let b₂ := stdOrthonormalBasis 𝕜 F
    exact
      ∑ (i) (j),
        star (((b₁.to_basis.tensor_product b₂.to_basis).repr x) (i, j)) *
          ((b₁.to_basis.tensor_product b₂.to_basis).repr y) (i, j)

-- lemma orthonormal.to_basis_tensor_product {n m : Type*} [fintype n] [fintype m]
--   (b₁ : orthonormal_basis n 𝕜 E) (b₂ : orthonormal_basis m 𝕜 F) :
--   (b₁.to_basis.tensor_product b₂.to_basis).repr
theorem TensorProduct.inner_tmul (x z : E) (y w : F) :
    (inner (x ⊗ₜ[𝕜] y) (z ⊗ₜ[𝕜] w) : 𝕜) = inner x z * inner y w := by
  simp_rw [inner, Basis.tensorProduct_repr_tmul_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    star_mul', mul_mul_mul_comm, IsROrC.star_def, OrthonormalBasis.repr_apply_apply,
    inner_conj_symm, ← Finset.mul_sum, ← Finset.sum_mul, OrthonormalBasis.sum_inner_mul_inner]

protected theorem TensorProduct.inner_add_left (x y z : E ⊗[𝕜] F) :
    (inner (x + y) z : 𝕜) = inner x z + inner y z := by
  simp_rw [inner, ← Finset.sum_add_distrib, map_add, Finsupp.add_apply, star_add, add_mul]

protected theorem TensorProduct.inner_zero_right (x : E ⊗[𝕜] F) :
    (inner x (0 : E ⊗[𝕜] F) : 𝕜) = 0 :=
  by
  apply x.induction_on
  all_goals rw [← TensorProduct.zero_tmul E (0 : F)]
  · rw [TensorProduct.inner_tmul]
    simp_rw [inner_zero_left, MulZeroClass.zero_mul]
  · intros
    simp_rw [TensorProduct.inner_tmul, inner_zero_right, MulZeroClass.mul_zero]
  · intro a b ha hb
    simp_rw [TensorProduct.inner_add_left, ha, hb, add_zero]

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
  rw [← TensorProduct.inner_conj_symm, TensorProduct.inner_sum, map_sum] <;>
    simp_rw [TensorProduct.inner_conj_symm]

protected theorem TensorProduct.inner_nonneg_re (x : E ⊗[𝕜] F) : 0 ≤ IsROrC.re (inner x x : 𝕜) :=
  by
  simp_rw [inner, map_sum, IsROrC.star_def, IsROrC.conj_mul, IsROrC.ofReal_re, ←
    Finset.sum_product', Finset.univ_product_univ, Prod.mk.eta]
  apply Finset.sum_nonneg
  intros
  exact IsROrC.normSq_nonneg _

theorem TensorProduct.eq_span {𝕜 E F : Type _} [IsROrC 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (x : E ⊗[𝕜] F) :
    ∃ (α : Basis.ofVectorSpaceIndex 𝕜 E × Basis.ofVectorSpaceIndex 𝕜 F → E) (β :
      Basis.ofVectorSpaceIndex 𝕜 E × Basis.ofVectorSpaceIndex 𝕜 F → F), ∑ i, α i ⊗ₜ[𝕜] β i = x :=
  by
  let b₁ := Basis.ofVectorSpace 𝕜 E
  let b₂ := Basis.ofVectorSpace 𝕜 F
  rw [← Basis.sum_repr (b₁.tensor_product b₂) x]
  simp_rw [Basis.tensorProduct_apply', TensorProduct.smul_tmul']
  exact ⟨fun i => ((b₁.tensor_product b₂).repr x) i • b₁ i.fst, fun i => b₂ i.snd, rfl⟩

@[instance, reducible]
noncomputable def TensorProduct.normedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 (E ⊗[𝕜] F) _ _ _
    { inner := fun x y => TensorProduct.hasInner.inner x y
      conj_symm := fun x y => y.inner_conj_symm x
      nonneg_re := fun x => x.inner_nonneg_re
      definite := fun x hx =>
        by
        simp_rw [inner, IsROrC.star_def, IsROrC.conj_mul, ← Finset.sum_product',
          Finset.univ_product_univ, Prod.mk.eta, ← IsROrC.ofReal_sum, IsROrC.ofReal_eq_zero] at hx
        rw [Finset.sum_eq_zero_iff_of_nonneg] at hx
        · simp_rw [IsROrC.normSq_eq_zero, Finset.mem_univ, true_imp_iff] at hx
          apply
            Basis.ext_elem
              ((stdOrthonormalBasis 𝕜 E).toBasis.TensorProduct (stdOrthonormalBasis 𝕜 F).toBasis)
          simp_rw [map_zero, Finsupp.zero_apply]
          exact hx
        · intro y hy
          exact IsROrC.normSq_nonneg _
      add_left := fun x y z => x.inner_add_left _ _
      smul_left := fun x y r => by
        apply x.induction_on
        · simp_rw [smul_zero, TensorProduct.inner_zero_left, MulZeroClass.mul_zero]
        · intro a b
          apply y.induction_on
          · simp_rw [smul_zero, TensorProduct.inner_zero_right, MulZeroClass.mul_zero]
          · intro c d
            all_goals
              simp only [TensorProduct.smul_tmul', TensorProduct.inner_tmul, inner_smul_left,
                mul_assoc, TensorProduct.inner_add_right, TensorProduct.inner_add_left, smul_add,
                mul_add]
          · intro α β ha hb
            simp_rw [TensorProduct.inner_add_right, ha, hb, mul_add]
        · intro a b ha hb
          simp_rw [smul_add, TensorProduct.inner_add_left, ha, hb, mul_add] }

@[instance, reducible]
noncomputable def TensorProduct.innerProductSpace :
    @InnerProductSpace 𝕜 (E ⊗[𝕜] F) _ TensorProduct.normedAddCommGroup :=
  InnerProductSpace.ofCore _

example (α β : 𝕜) (x y : E) :
    TensorProduct.innerProductSpace.inner (α ⊗ₜ[𝕜] x) (β ⊗ₜ[𝕜] y) = inner α β * inner x y :=
  TensorProduct.inner_tmul _ _ _ _

theorem TensorProduct.lid_adjoint :
    (TensorProduct.lid 𝕜 E : 𝕜 ⊗[𝕜] E →ₗ[𝕜] E).adjoint = (TensorProduct.lid 𝕜 E).symm :=
  by
  ext1
  apply @ext_inner_right 𝕜
  intro y
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
  apply y.induction_on
  · simp only [inner_zero_right, map_zero]
  · intro α z
    simp only [TensorProduct.lid_tmul, TensorProduct.inner_tmul, IsROrC.inner_apply,
      starRingEnd_apply, star_one, one_mul, inner_smul_right]
  · intro z w hz hw
    simp only [map_add, inner_add_right, hz, hw]

theorem TensorProduct.comm_adjoint :
    (TensorProduct.comm 𝕜 E F : E ⊗[𝕜] F →ₗ[𝕜] F ⊗[𝕜] E).adjoint =
      (TensorProduct.comm 𝕜 E F).symm :=
  by
  apply TensorProduct.ext'
  intro x y
  apply @ext_inner_right 𝕜
  intro z
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.comm_symm_tmul]
  apply z.induction_on
  · simp only [inner_zero_right, map_zero]
  · intro α z
    simp only [TensorProduct.comm_tmul, TensorProduct.inner_tmul, mul_comm]
  · intro z w hz hw
    simp only [map_add, inner_add_right, hz, hw]

theorem TensorProduct.assoc_symm_adjoint {G : Type _} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] :
    ((TensorProduct.assoc 𝕜 E F G).symm : E ⊗[𝕜] F ⊗[𝕜] G →ₗ[𝕜] (E ⊗[𝕜] F) ⊗[𝕜] G).adjoint =
      TensorProduct.assoc 𝕜 E F G :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  apply @ext_inner_right 𝕜
  intro w
  obtain ⟨w₁, w₂, rfl⟩ := w.eq_span
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, TensorProduct.assoc_tmul, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨w₃, w₄, hw⟩ := (w₂ i).eq_span
  simp only [← hw, TensorProduct.assoc_symm_tmul, TensorProduct.tmul_sum, map_sum, inner_sum,
    TensorProduct.inner_tmul, mul_assoc]

theorem TensorProduct.assoc_adjoint {G : Type _} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] :
    (TensorProduct.assoc 𝕜 E F G : (E ⊗[𝕜] F) ⊗[𝕜] G →ₗ[𝕜] E ⊗[𝕜] F ⊗[𝕜] G).adjoint =
      (TensorProduct.assoc 𝕜 E F G).symm :=
  by
  have := @TensorProduct.assoc_symm_adjoint 𝕜 E F _ _ _ _ _ _ _ G _ _ _
  apply_fun LinearMap.adjoint at this
  rw [LinearMap.adjoint_adjoint] at this
  exact this.symm

theorem TensorProduct.map_adjoint {A B C D : Type _} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [NormedAddCommGroup D] [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B]
    [InnerProductSpace 𝕜 C] [InnerProductSpace 𝕜 D] [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] [FiniteDimensional 𝕜 D] (f : A →ₗ[𝕜] B) (g : C →ₗ[𝕜] D) :
    (TensorProduct.map f g).adjoint = TensorProduct.map f.adjoint g.adjoint :=
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
  repeat'
    apply Finset.sum_congr rfl
    intros
  rw [h]

theorem TensorProduct.forall_inner_eq_zero {𝕜 E F : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (x : E ⊗[𝕜] F) :
    (∀ (a : E) (b : F), (inner x (a ⊗ₜ[𝕜] b) : 𝕜) = 0) ↔ x = 0 :=
  by
  refine' ⟨fun h => _, fun h a b => by rw [h, inner_zero_left]⟩
  rw [← @forall_inner_eq_zero_iff 𝕜]
  intro y
  apply TensorProduct.induction_on y
  · exact inner_zero_right _
  · exact h
  · intro c d hc hd
    rw [inner_add_right, hc, hd, add_zero]

theorem TensorProduct.inner_ext_iff' {𝕜 E F : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (x y : E ⊗[𝕜] F) :
    x = y ↔ ∀ (a : E) (b : F), inner x (a ⊗ₜ[𝕜] b) = (inner y (a ⊗ₜ[𝕜] b) : 𝕜) := by
  simp_rw [← @sub_eq_zero 𝕜 _ _ (inner _ _ : 𝕜), ← inner_sub_left,
    TensorProduct.forall_inner_eq_zero, sub_eq_zero]

theorem TensorProduct.lid_symm_adjoint {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    (TensorProduct.lid 𝕜 E).symm.toLinearMap.adjoint = TensorProduct.lid 𝕜 E :=
  by
  have := @TensorProduct.lid_adjoint 𝕜 E _ _ _ _
  apply_fun LinearMap.adjoint at this
  rw [LinearMap.adjoint_adjoint] at this
  exact this.symm

theorem TensorProduct.comm_symm_adjoint {𝕜 E V : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 V] :
    (TensorProduct.comm 𝕜 E V).symm.toLinearMap.adjoint = TensorProduct.comm 𝕜 E V :=
  by
  have := @TensorProduct.comm_adjoint 𝕜 E V _ _ _ _ _ _ _
  apply_fun LinearMap.adjoint at this
  rw [LinearMap.adjoint_adjoint] at this
  exact this.symm

end

