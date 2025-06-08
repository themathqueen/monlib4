import Monlib.LinearAlgebra.QuantumSet.Basic
import Monlib.LinearAlgebra.TensorProduct.OrthonormalBasis

variable {A : Type*} [ha : starAlgebra A]
  {B : Type*} [hb : starAlgebra B]

open scoped TensorProduct
-- noncomputable instance :
--   NormedAddCommGroupOfRing (A ⊗[ℂ] B) where
set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance tensorStarAlgebra
  [Module.Finite ℂ A] [Module.Finite ℂ B] :
    starAlgebra (A ⊗[ℂ] B) where
  star_mul x y := x.induction_on (by simp only [zero_mul, star_zero, mul_zero])
    (y.induction_on
      (by simp only [mul_zero, star_zero, TensorProduct.star_tmul, zero_mul,
        implies_true])
      (λ _ _ _ _ => by simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.star_tmul,
        star_mul])
      (λ _ _ h1 h2 _ _ => by simp only [mul_add, star_add, h1, h2, add_mul]))
    (λ _ _ h1 h2 => by simp only [star_add, add_mul, mul_add, h1, h2])
  star_add := star_add
  modAut r := AlgEquiv.TensorProduct.map (ha.modAut r) (hb.modAut (r))
  modAut_trans r s := by
    simp_rw [AlgEquiv.ext_iff, ← AlgEquiv.toLinearMap_apply, ← LinearMap.ext_iff]
    apply TensorProduct.ext'
    intro _ _
    simp only [AlgEquiv.trans_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.TensorProduct.map_tmul,
      QuantumSet.modAut_apply_modAut, add_comm]
  modAut_star _ x := x.induction_on (by simp only [map_zero, star_zero])
    (λ _ _ => by simp only [AlgEquiv.TensorProduct.map_tmul, TensorProduct.star_tmul, starAlgebra.modAut_star])
    (λ _ _ h1 h2 => by simp only [map_add, star_add, h1, h2])

lemma modAut_tensor [Module.Finite ℂ A] [Module.Finite ℂ B] (r : ℝ) :
  tensorStarAlgebra.modAut r = AlgEquiv.TensorProduct.map (ha.modAut r) (hb.modAut (r)) :=
rfl
lemma modAut_tensor_tmul [Module.Finite ℂ A] [Module.Finite ℂ B] (r : ℝ) (x : A) (y : B) :
  tensorStarAlgebra.modAut r (x ⊗ₜ[ℂ] y) = (ha.modAut r x) ⊗ₜ[ℂ] (hb.modAut (r) y) :=
rfl

  -- toFun := algebraMap ℂ (A ⊗[ℂ] B)
  -- map_one' := map_one _
  -- map_mul' _ _ := RingHom.map_mul _ _ _
  -- map_zero' := map_zero _
  -- map_add' _ _ := RingHom.map_add _ _ _
  -- commutes' _ x := x.induction_on
  --   (by simp_rw [zero_mul, mul_zero])
  --   (λ _ _ => by
  --       simp only [RingHom.mk_coe, Algebra.TensorProduct.algebraMap_apply,
  --         Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  --       simp_rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_one])
  --   (λ _ _ h1 h2 => by
  --       simp only [mul_add, add_mul, h1, h2])
  -- smul_def' _ _ := by
  --   simp only [RingHom.mk_coe, Algebra.TensorProduct.algebraMap_apply]
  --   simp_rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul',
  --     ← Algebra.TensorProduct.one_def, smul_mul_assoc, one_mul]

noncomputable instance
  [InnerProductAlgebra A] [InnerProductAlgebra B]
  [Module.Finite ℂ A] [Module.Finite ℂ B] :
    InnerProductAlgebra (A ⊗[ℂ] B) where
  -- norm_smul_le _ _ := by rw [← norm_smul]
  norm_sq_eq_inner _ := norm_sq_eq_re_inner (𝕜 := ℂ) _
  conj_symm x y := inner_conj_symm (𝕜 := ℂ) x y
    -- x.induction_on
    -- (by simp only [inner_zero_right, map_zero, inner_zero_left])
    -- (y.induction_on
    --   (by simp only [inner_zero_left, map_zero, inner_zero_right, implies_true])
    --   (λ _ _ _ _ => by simp only [TensorProduct.inner_tmul, map_mul, inner_conj_symm])
    --   (λ _ _ h1 h2 _ _ => by simp [inner_add_left, inner_add_right, h1, h2]))
    --   (λ _ _ h1 h2 => by simp_rw [inner_add_left, inner_add_right, h2, h2])
      -- inner_conj_symm (𝕜 := ℂ)
  add_left := inner_add_left
  smul_left r x y := inner_smul_left (𝕜 := ℂ) r x y

set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 60000 in
noncomputable instance QuantumSet.tensorProduct
  [hA : QuantumSet A] [hB : QuantumSet B] [h : Fact (hA.k = hB.k)] :
    QuantumSet (A ⊗[ℂ] B) where
  modAut_isSymmetric r _ _ := by
    simp_rw [← AlgEquiv.toLinearMap_apply, modAut_tensor, AlgEquiv.TensorProduct.map_toLinearMap]
    nth_rw 1 [← @modAut_isSelfAdjoint A]
    nth_rw 1 [← @modAut_isSelfAdjoint B]
    simp_rw [LinearMap.star_eq_adjoint, ← TensorProduct.map_adjoint]
    exact LinearMap.adjoint_inner_left _ _ _
  k := hA.k
  inner_star_left a b c := a.induction_on
    (by simp only [zero_mul, inner_zero_left, star_zero, map_zero, inner_zero_right])
    (b.induction_on
    (by simp only [mul_zero, inner_zero_left, TensorProduct.star_tmul, implies_true])
    (c.induction_on
    (by simp only [Algebra.TensorProduct.tmul_mul_tmul, inner_zero_right, TensorProduct.star_tmul,
      mul_zero, implies_true])
    (λ _ _ _ _ _ _ => by
      simp only [
        TensorProduct.star_tmul,
        modAut_tensor,
        Algebra.TensorProduct.tmul_mul_tmul,
        QuantumSet.inner_star_left, TensorProduct.inner_tmul,
        AlgEquiv.TensorProduct.map_tmul]
      rw [h.out])
    (λ _ _ h1 h2 _ _ _ _ => by simp only [inner_add_right, inner_add_left, h1, h2, mul_add]))
    (λ _ _ h1 h2 _ _ => by simp only [mul_add, inner_add_left, inner_add_right,
      h1, h2]))
    (λ _ _ h1 h2 => by simp only [add_mul, mul_add, inner_add_left, inner_add_right,
      h1, h2, star_add, map_add])
  inner_conj_left a b c := a.induction_on
    (by simp only [zero_mul, inner_zero_left])
    (b.induction_on
    (by simp only [mul_zero, inner_zero_left, star_zero, map_zero, inner_zero_right, implies_true])
    (c.induction_on
    (by simp only [Algebra.TensorProduct.tmul_mul_tmul, inner_zero_right, TensorProduct.star_tmul,
      zero_mul, implies_true])
    (λ _ _ _ _ _ _ => by
      simp_rw [
        TensorProduct.star_tmul,
        modAut_tensor_tmul,
        -- AlgEquiv.TensorProduct.map_tmul,
        Algebra.TensorProduct.tmul_mul_tmul,
        TensorProduct.inner_tmul,
        QuantumSet.inner_conj_left,]
      rw [h.out])
    (λ _ _ h1 h2 _ _ _ _ => by
      simp only [inner_add_right, add_mul, inner_add_left, h1, h2, mul_add]))
    (λ _ _ h1 h2 _ _ => by simp only [add_mul, mul_add, inner_add_left, inner_add_right,
      star_add, map_add, h1, h2]))
    (λ _ _ h1 h2 => by simp only [add_mul, mul_add, inner_add_left, inner_add_right,
      h1, h2, star_add, map_add])
  n := _
  n_isFintype := _
  onb := hA.onb.tensorProduct hB.onb
  n_isDecidableEq := by infer_instance

theorem QuantumSet.tensorProduct.k_eq₁ [hA : QuantumSet A] [hB : QuantumSet B] [Fact (hA.k = hB.k)] :
  (QuantumSet.tensorProduct : QuantumSet (A ⊗[ℂ] B)).k = hA.k :=
rfl
theorem QuantumSet.tensorProduct.k_eq₂ [hA : QuantumSet A] [hB : QuantumSet B] [h : Fact (hA.k = hB.k)] :
  (QuantumSet.tensorProduct : QuantumSet (A ⊗[ℂ] B)).k = hB.k :=
by rw [← h.out]; rfl

-- set_option trace.Meta.isDefEq true in
theorem comul_real
  [hA : QuantumSet A] :
  (Coalgebra.comul : A →ₗ[ℂ] A ⊗[ℂ] A).real = (TensorProduct.comm ℂ A A).toLinearMap ∘ₗ Coalgebra.comul :=
by
  letI := Fact.mk (rfl : hA.k = hA.k)
  letI : starAlgebra (A ⊗[ℂ] A) := by infer_instance
  letI : QuantumSet (A ⊗[ℂ] A) := QuantumSet.tensorProduct
  -- letI : NormedAddCommGroupOfRing (A ⊗[ℂ] A) := by infer_instance
  -- letI : InnerProductSpace ℂ (A ⊗[ℂ] A) := by infer_instance
  rw [Coalgebra.comul_eq_mul_adjoint, @LinearMap.adjoint_real_eq (A ⊗[ℂ] A) A _ _ _ _,
    LinearMap.mul'_real, LinearMap.adjoint_comp, TensorProduct.comm_adjoint,
    LinearMap.comp_assoc, ← LinearMap.comp_assoc, modAut_tensor,
    AlgEquiv.TensorProduct.map_toLinearMap,
    ← TensorProduct.comm_symm_map, ← Coalgebra.comul_eq_mul_adjoint]
  simp_rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (TensorProduct.map _ _),
    (QuantumSet.modAut_isCoalgHom _).2, LinearMap.comp_assoc, ← AlgEquiv.trans_toLinearMap,
    starAlgebra.modAut_trans, neg_sub_left, add_comm,
    QuantumSet.tensorProduct.k_eq₁, neg_add_cancel, starAlgebra.modAut_zero]
  rfl

-- calc Coalgebra.comul.real = (LinearMap.adjoint (LinearMap.mul' ℂ A)).real :=
--     by rw [Coalgebra.comul_eq_mul_adjoint]
--   _ = (hA.modAut 1).toLinearMap
--     ∘ₗ (LinearMap.adjoint (LinearMap.mul' ℂ A).real) ∘ₗ (hA.modAut (-1)).toLinearMap := LinearMap.adjoint_real_eq _
--   _ = (hA.modAut 1).toLinearMap
--     ∘ₗ (LinearMap.adjoint (LinearMap.mul' ℂ A ∘ₗ (TensorProduct.comm ℂ A A).toLinearMap)) := ?_
--   _ =

noncomputable def swap_middle_tensor
  (R : Type*) [CommSemiring R] (A B C D : Type*)
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] :
  (A ⊗[R] B) ⊗[R] (C ⊗[R] D) ≃ₗ[R] (A ⊗[R] C) ⊗[R] (B ⊗[R] D) :=
((TensorProduct.assoc R (A ⊗[R] B) C D).symm.trans
    (LinearEquiv.rTensor D (
      ((TensorProduct.assoc R A B C).trans
      ((LinearEquiv.lTensor A (TensorProduct.comm R B C)))).trans (TensorProduct.assoc R A C B).symm
    ))).trans (TensorProduct.assoc R (A ⊗[R] C) _ _)

@[simp]
lemma swap_middle_tensor_tmul_apply
  {R : Type*} [CommSemiring R] {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (x : A) (y : B) (z : C) (w : D) :
  swap_middle_tensor R A B C D ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w))
    = (x ⊗ₜ z) ⊗ₜ (y ⊗ₜ w) :=
rfl
@[simp]
lemma swap_middle_tensor_symm
  {R : Type*} [CommSemiring R] {A B C D : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] :
  (swap_middle_tensor R A B C D).symm = swap_middle_tensor R A C B D :=
rfl
lemma swap_middle_tensor_comp_map
  {R : Type*} [CommSemiring R] {A B C D E F G H : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G] [AddCommMonoid H]
  [Module R E] [Module R F] [Module R G] [Module R H]
  (f : A →ₗ[R] B) (g : C →ₗ[R] D)
  (h : E →ₗ[R] F) (k : G →ₗ[R] H) :
  (swap_middle_tensor R B D F H).toLinearMap ∘ₗ
   (TensorProduct.map (TensorProduct.map f g) (TensorProduct.map h k))
    =
      (TensorProduct.map (TensorProduct.map f h) (TensorProduct.map g k))
      ∘ₗ (swap_middle_tensor R A C E G).toLinearMap :=
by
  apply TensorProduct.ext_fourfold'
  simp

lemma LinearMap.mul'_tensorProduct {R A B : Type*}
  [CommSemiring R] [NonUnitalNonAssocSemiring A]
  [NonUnitalNonAssocSemiring B] [Module R A] [Module R B]
  [SMulCommClass R A A] [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B] :
  LinearMap.mul' R (A ⊗[R] B) = (TensorProduct.map (LinearMap.mul' R A) (LinearMap.mul' R B))
    ∘ₗ (swap_middle_tensor R A B A B).toLinearMap :=
by
  apply TensorProduct.ext_fourfold'
  simp

lemma swap_middle_tensor_map_conj {R A B C D E F G H : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G] [AddCommMonoid H]
  [Module R E] [Module R F] [Module R G] [Module R H]
  (f : A →ₗ[R] B) (g : C →ₗ[R] D)
  (h : E →ₗ[R] F) (k : G →ₗ[R] H) :
 (swap_middle_tensor R B D F H).toLinearMap
   ∘ₗ (TensorProduct.map (TensorProduct.map f g)
     (TensorProduct.map h k))
    ∘ₗ (swap_middle_tensor R A C E G).symm.toLinearMap
  = TensorProduct.map (TensorProduct.map f h)
    (TensorProduct.map g k) :=
by
  apply TensorProduct.ext_fourfold'
  simp

lemma swap_middle_tensor_adjoint
  {𝕜 E F G H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
  [InnerProductSpace 𝕜 G] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]:
  LinearMap.adjoint (swap_middle_tensor 𝕜 E F G H).toLinearMap
    = (swap_middle_tensor 𝕜 E F G H).symm.toLinearMap :=
by
  apply TensorProduct.ext_fourfold'
  intros x y z w
  rw [TensorProduct.inner_ext_fourfold_iff']
  simp [LinearMap.adjoint_inner_left, mul_mul_mul_comm]
