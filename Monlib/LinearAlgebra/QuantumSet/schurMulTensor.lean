import Monlib.LinearAlgebra.QuantumSet.SchurMul
import Monlib.LinearAlgebra.QuantumSet.TensorProduct
import Mathlib.RingTheory.Coalgebra.TensorProduct

open scoped TensorProduct

lemma TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq_swap_middle_tensor
  {R A B C D : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D] :
  (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R R R A B C D) = swap_middle_tensor R A B C D :=
by
  rw [← LinearEquiv.toLinearMap_inj]
  apply TensorProduct.ext_fourfold'
  simp

theorem TensorProduct.map_schurMul {A B C D : Type*}
  [AddCommMonoid A] [Semiring B]
  [AddCommMonoid C] [Semiring D]
  [Module ℂ A] [Module ℂ B]
  [Module ℂ C] [Module ℂ D]
  [Coalgebra ℂ A] [Coalgebra ℂ C]
  [SMulCommClass ℂ B B]
  [SMulCommClass ℂ D D]
  [IsScalarTower ℂ B B]
  [IsScalarTower ℂ D D]
  {f h : A →ₗ[ℂ] B} {g k : C →ₗ[ℂ] D} :
  (map f g) •ₛ (map h k) = map (f •ₛ h) (g •ₛ k) :=
by
  rw [schurMul_apply_apply, TensorProduct.comul_def, LinearMap.mul'_tensorProduct,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq_swap_middle_tensor]
  simp only [LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ _ (swap_middle_tensor _ _ _ _ _).toLinearMap]
  nth_rw 2 [← LinearMap.comp_assoc, LinearMap.comp_assoc, ← swap_middle_tensor_symm]
  rw [swap_middle_tensor_map_conj]
  simp only [← LinearMap.comp_assoc, ← TensorProduct.map_comp,
    TensorProduct.AlgebraTensorModule.map_eq]
  rfl
