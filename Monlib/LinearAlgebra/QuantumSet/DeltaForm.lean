import Monlib.LinearAlgebra.QuantumSet.Basic

open scoped ComplexOrder
class QuantumSetDeltaForm (A : Type*) [starAlgebra A] [QuantumSet A] where
  delta : ℂ
  delta_pos : 0 < delta
  mul_comp_comul_eq : LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul = delta • 1

@[instance]
noncomputable def QuantumSet.DeltaForm.mul_comp_comul_isInvertible {A : Type*} [starAlgebra A]
  [QuantumSet A] [hA2 : QuantumSetDeltaForm A] :
  Invertible (LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul) :=
by
  apply IsUnit.invertible
  rw [LinearMap.isUnit_iff_ker_eq_bot, hA2.mul_comp_comul_eq, LinearMap.ker_smul, Module.End.one_eq_id,
    LinearMap.ker_id]
  exact ne_of_gt hA2.delta_pos
