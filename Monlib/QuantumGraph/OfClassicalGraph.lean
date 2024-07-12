import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Monlib.QuantumGraph.Basic
import Monlib.QuantumGraph.Example

noncomputable instance {n : Type*} [Fintype n] :
  starAlgebra (PiQ (λ _ : n => ℂ)) :=
piStarAlgebra
noncomputable instance {n : Type*} [Fintype n] :
  QuantumSet (PiQ (λ _ : n => ℂ)) :=
Pi.quantumSet (gns := Fact.mk (λ _ => rfl))

set_option synthInstance.maxHeartbeats 0 in
theorem EuclideanSpace.comul_eq {n : Type*} [Fintype n] [DecidableEq n] (x : PiQ (λ _ : n => ℂ))
  :
  let e : ∀ _ : n, (PiQ (λ _ : n => ℂ)) := λ i j => if i = j then 1 else 0
  (Coalgebra.comul : PiQ (λ _ : n => ℂ) →ₗ[ℂ] _) x
    = ∑ i, x i • (e i ⊗ₜ[ℂ] e i) :=
by
  intro e
  have : ∀ y i, ⟪e i, y⟫_ℂ = y i := λ _ _ => by
    simp only [PiLp.inner_apply, RCLike.inner_apply, e, starRingEnd_apply,
      star_ite, star_zero, star_one, boole_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  rw [TensorProduct.inner_ext_iff']
  intro a b
  simp only [TensorProduct.inner_tmul, Coalgebra.comul, LinearMap.adjoint_inner_left,
    LinearMap.mul'_apply, sum_inner, inner_smul_left, this]
  rfl

open scoped Matrix
/-- a finite simple graph is a quantum graph -/
theorem SimpleGraph.toQuantumGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  QuantumGraph _ (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G)) :=
by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let e : ∀ _ : V, (V → ℂ) := λ i j => if i = j then 1 else 0
  have he : ∀ i, e i = λ j => if i = j then 1 else 0 := λ _ => rfl
  have : ∀ (i : V) (a : Matrix V V ℂ),
    ((Matrix.toEuclideanLin a (e i)) : EuclideanSpace ℂ V) =
      (aᵀ i) := λ _ _ => by
    simp only [Matrix.toEuclideanLin_apply']
    ext
    simp only [Matrix.mulVec, Matrix.dotProduct, e, mul_boole, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rfl
  constructor
  ext1 x
  simp only [schurMul_apply_apply, LinearMap.coe_comp, Function.comp_apply,
    EuclideanSpace.comul_eq, ← he]
  simp_rw [map_sum, LinearMapClass.map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply,
    this]
  ext1
  rw [Finset.sum_apply, Matrix.toEuclideanLin_apply']
  simp_rw [PiLp.smul_apply, PiLp.mul_apply, Matrix.mulVec, Matrix.dotProduct,
    Matrix.transpose_apply,
    SimpleGraph.adjMatrix, Matrix.of_apply, boole_mul, smul_eq_mul,
    mul_ite,
    mul_one, mul_zero, ← ite_and, and_self]
