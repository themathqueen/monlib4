import Monlib.LinearAlgebra.QuantumSet.Basic
import Monlib.LinearAlgebra.MyBimodule

noncomputable abbrev PhiMap {A B : Type*} [starAlgebra B] [starAlgebra A] [QuantumSet A]
  [QuantumSet B] :=
    (Upsilon (A := A) (B := B)).trans TensorProduct.toIsBimoduleMap

lemma PhiMap_apply {A B : Type*} [starAlgebra B] [starAlgebra A] [QuantumSet A]
  [QuantumSet B] (f : A →ₗ[ℂ] B) :
  PhiMap f = TensorProduct.toIsBimoduleMap (Upsilon f) :=
rfl

open scoped InnerProductSpace
lemma oneInner_map_one_eq_oneInner_PhiMap_map_one
  {A B : Type*} [starAlgebra B] [starAlgebra A] [hA : QuantumSet A] [hB : QuantumSet B]
  (f : A →ₗ[ℂ] B) :
  ⟪1, f 1⟫_ℂ = ⟪1, ((PhiMap f : (TensorProduct ℂ A B →ₗ[ℂ] TensorProduct ℂ A B)) 1)⟫_ℂ :=
by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  simp_rw [map_sum, LinearMap.IsBimoduleMap.sum_coe,
    LinearMap.sum_apply, inner_sum]
  congr
  ext1 i
  simp_rw [PhiMap_apply, Upsilon_rankOne, TensorProduct.toIsBimoduleMap_apply_coe,
    rmulMapLmul_apply_one, ContinuousLinearMap.coe_coe, rankOne_apply,
    Algebra.TensorProduct.one_def, TensorProduct.inner_tmul, inner_smul_right]
  rw [← one_mul (modAut _ _), ← QuantumSet.inner_conj_left, one_mul]
