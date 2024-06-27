import Monlib.LinearAlgebra.QuantumSet.Basic
import Monlib.LinearAlgebra.TensorProduct.OrthonormalBasis

variable {A : Type*} [NormedAddCommGroupOfRing A] [hA : QuantumSet A]
  {B : Type*} [NormedAddCommGroupOfRing B] [hB : QuantumSet B]

open scoped TensorProduct
noncomputable instance :
  NormedAddCommGroupOfRing (A ⊗[ℂ] B) where
noncomputable instance :
    InnerProductAlgebra (A ⊗[ℂ] B) where
  toFun := algebraMap ℂ (A ⊗[ℂ] B)
  map_one' := map_one _
  map_mul' _ _ := RingHom.map_mul _ _ _
  map_zero' := map_zero _
  map_add' _ _ := RingHom.map_add _ _ _
  commutes' _ x := x.induction_on
    (by simp_rw [zero_mul, mul_zero])
    (λ _ _ => by
        simp only [RingHom.mk_coe, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        simp_rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_one])
    (λ _ _ h1 h2 => by
        simp only [mul_add, add_mul, h1, h2])
  smul_def' _ _ := by
    simp only [RingHom.mk_coe, Algebra.TensorProduct.algebraMap_apply]
    simp_rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul',
      ← Algebra.TensorProduct.one_def, smul_mul_assoc, one_mul]
noncomputable instance :
    InnerProductStarAlgebra (A ⊗[ℂ] B) where
  star_mul x y := x.induction_on (by simp_rw [zero_mul, star_zero, mul_zero])
    (λ _ _ =>
      y.induction_on (by simp_rw [mul_zero, star_zero, zero_mul])
      (λ _ _ => by simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.star_tmul,
        star_mul])
      λ _ _ h1 h2 => by simp only [mul_add, star_add, add_mul, h1, h2])
    (λ _ _ h1 h2 => by simp only [mul_add, add_mul, star_add, h1, h2])
  star_add x y := TensorProduct.star_add _ _

set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 60000 in
noncomputable instance QuantumSet.tensorProduct [h : Fact (hA.k = hB.k)] :
    QuantumSet (A ⊗[ℂ] B) where
  modAut r := AlgEquiv.TensorProduct.map (hA.modAut r) (hB.modAut (r))
  modAut_trans r s := by
    simp_rw [AlgEquiv.ext_iff, ← AlgEquiv.toLinearMap_apply, ← LinearMap.ext_iff]
    apply TensorProduct.ext'
    intro _ _
    simp only [AlgEquiv.trans_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.TensorProduct.map_tmul,
      modAut_apply_modAut, add_comm]
  modAut_zero := by
    simp only [QuantumSet.modAut_zero, AlgEquiv.TensorProduct.map_one]
  modAut_star _ x := x.induction_on (by simp only [map_zero, star_zero])
    (λ _ _ => by simp only [AlgEquiv.TensorProduct.map_tmul, TensorProduct.star_tmul, modAut_star])
    (λ _ _ h1 h2 => by simp only [map_add, star_add, h1, h2])
  modAut_isSymmetric r _ _ := by
    simp_rw [← AlgEquiv.toLinearMap_apply, AlgEquiv.TensorProduct.map_toLinearMap]
    nth_rw 1 [← @modAut_isSelfAdjoint A]
    nth_rw 1 [← @modAut_isSelfAdjoint B]
    simp_rw [LinearMap.star_eq_adjoint, ← TensorProduct.map_adjoint]
    exact LinearMap.adjoint_inner_left _ _ _
  k := hA.k
  inner_star_left a b c := by
    obtain ⟨α,β,h'⟩ := a.eq_span
    obtain ⟨α₂,β₂,h₂⟩ := b.eq_span
    obtain ⟨α₃,β₃,h₃⟩ := c.eq_span
    rw [← h']
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum, inner_sum, sum_inner, map_sum]
    simp_rw [← h₂]
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum, inner_sum, sum_inner, map_sum]
    simp_rw [← h₃]
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum, inner_sum, sum_inner, map_sum]
    simp only [TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      QuantumSet.inner_star_left, TensorProduct.inner_tmul,
      AlgEquiv.TensorProduct.map_tmul]
    rw [h.out]
  inner_conj_left a b c := by
    obtain ⟨α,β,h'⟩ := a.eq_span
    obtain ⟨α₂,β₂,h₂⟩ := b.eq_span
    obtain ⟨α₃,β₃,h₃⟩ := c.eq_span
    rw [← h']
    simp only [star_sum, map_sum, Finset.sum_mul, Finset.mul_sum, inner_sum, sum_inner]
    simp_rw [← h₂]
    simp only [star_sum, map_sum, Finset.sum_mul, Finset.mul_sum, inner_sum, sum_inner]
    simp_rw [← h₃]
    simp only [star_sum, map_sum, Finset.sum_mul, Finset.mul_sum, inner_sum, sum_inner]
    simp_rw [
      TensorProduct.star_tmul,
      AlgEquiv.TensorProduct.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul,
      TensorProduct.inner_tmul,
      QuantumSet.inner_conj_left,
      ]
    rw [h.out]
  onb := hA.onb.tensorProduct hB.onb
  n_isDecidableEq := by infer_instance

theorem modAut_tensor [Fact (hA.k = hB.k)] (r : ℝ) :
  QuantumSet.tensorProduct.modAut r =
    AlgEquiv.TensorProduct.map (hA.modAut r) (hB.modAut r) :=
rfl
theorem QuantumSet.tensorProduct.k_eq₁ [Fact (hA.k = hB.k)] :
  (QuantumSet.tensorProduct : QuantumSet (A ⊗[ℂ] B)).k = hA.k :=
rfl
theorem QuantumSet.tensorProduct.k_eq₂ [h : Fact (hA.k = hB.k)] :
  (QuantumSet.tensorProduct : QuantumSet (A ⊗[ℂ] B)).k = hB.k :=
by rw [← h.out]; rfl

theorem comul_real :
  (Coalgebra.comul : A →ₗ[ℂ] A ⊗[ℂ] A).real = (TensorProduct.comm ℂ A A).toLinearMap ∘ₗ Coalgebra.comul :=
by
  haveI := Fact.mk (rfl : hA.k = hA.k)
  rw [Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_real_eq,
    LinearMap.mul'_real, LinearMap.adjoint_comp, TensorProduct.comm_adjoint,
    LinearMap.comp_assoc, ← LinearMap.comp_assoc, modAut_tensor,
    AlgEquiv.TensorProduct.map_toLinearMap,
    ← TensorProduct.comm_symm_map, ← Coalgebra.comul_eq_mul_adjoint]
  simp_rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (TensorProduct.map _ _),
    (QuantumSet.modAut_isCoalgHom _).2, LinearMap.comp_assoc, ← AlgEquiv.trans_toLinearMap,
    QuantumSet.modAut_trans, neg_sub_left, add_comm,
    QuantumSet.tensorProduct.k_eq₁, neg_add_self, QuantumSet.modAut_zero]
  rfl

-- calc Coalgebra.comul.real = (LinearMap.adjoint (LinearMap.mul' ℂ A)).real :=
--     by rw [Coalgebra.comul_eq_mul_adjoint]
--   _ = (hA.modAut 1).toLinearMap
--     ∘ₗ (LinearMap.adjoint (LinearMap.mul' ℂ A).real) ∘ₗ (hA.modAut (-1)).toLinearMap := LinearMap.adjoint_real_eq _
--   _ = (hA.modAut 1).toLinearMap
--     ∘ₗ (LinearMap.adjoint (LinearMap.mul' ℂ A ∘ₗ (TensorProduct.comm ℂ A A).toLinearMap)) := ?_
--   _ =
