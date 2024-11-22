import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Monlib.QuantumGraph.Basic
import Monlib.QuantumGraph.Example
import Monlib.QuantumGraph.Grad

noncomputable instance {n : Type*} [Fintype n] :
  starAlgebra (PiQ (λ _ : n => ℂ)) :=
piStarAlgebra
noncomputable instance {n : Type*} [Fintype n] :
  QuantumSet (PiQ (λ _ : n => ℂ)) :=
Pi.quantumSet (gns := Fact.mk (λ _ => rfl))

open scoped InnerProductSpace

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

theorem quantumGraph_numOfEdges_of_classical
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  QuantumGraph.NumOfEdges (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G))
    = ∑ i, ∑ j, SimpleGraph.adjMatrix ℂ G i j :=
by
  simp only [QuantumGraph.NumOfEdges, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap,
    Matrix.toEuclideanLin_apply', Matrix.mulVec_one]
  rw [EuclideanSpace.inner_eq, star_one, Matrix.one_dotProduct]

theorem SimpleGraph.conjTranspose_adjMatrix {V α : Type*} (G : SimpleGraph V)
  [DecidableRel G.Adj] [NonAssocSemiring α] [StarRing α] :
  (SimpleGraph.adjMatrix α G)ᴴ = SimpleGraph.adjMatrix α G :=
by
  ext
  simp [star_ite, star_one, star_zero, adj_comm]

theorem SimpleGraph.adjMatrix_toEuclideanLin_isReal
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  LinearMap.IsReal (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G)) :=
by
  intro
  simp only [Matrix.toEuclideanLin_apply']
  rw [Matrix.star_mulVec, SimpleGraph.conjTranspose_adjMatrix]
  ext
  simp only [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.adjMatrix_vecMul_apply]

theorem SimpleGraph.adjMatrix_toEuclideanLin_symmMap
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  symmMap ℂ _ _ (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G))
    = Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G) :=
by
  simp only [symmMap_apply,
    LinearMap.real_of_isReal (SimpleGraph.adjMatrix_toEuclideanLin_isReal G),
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    SimpleGraph.conjTranspose_adjMatrix]

theorem SimpleGraph.adjMatrix_irreflexive
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G)) •ₛ 1 = 0 :=
by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  ext1 x
  simp only [schurMul_apply_apply, LinearMap.comp_apply]
  rw [EuclideanSpace.comul_eq]
  simp only [map_sum, map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Matrix.toEuclideanLin_apply', LinearMap.one_apply]
  ext
  rw [Finset.sum_apply]
  simp only [PiLp.smul_apply, PiLp.mul_apply, adjMatrix_mulVec_apply,
    mul_ite, mul_one, mul_zero, smul_ite, Finset.smul_sum, smul_zero]
  simp only [smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_eq, mem_neighborFinset, SimpleGraph.irrefl, ↓reduceIte,
    LinearMap.zero_apply, PiLp.zero_apply]
