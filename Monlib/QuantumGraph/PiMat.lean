import Monlib.QuantumGraph.Basic
import Monlib.QuantumGraph.Example
import Monlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

variable {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [Π i, Fintype (p i)] [Π i, DecidableEq (p i)]
  {φ : Π i, Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : Π i, (φ i).IsFaithfulPosMap]

open scoped Functional MatrixOrder ComplexOrder TensorProduct Matrix

set_option synthInstance.maxHeartbeats 0 in
private noncomputable def PiMatTensorTo (ι : Type*)
  (p : ι → Type*) [Fintype ι] [DecidableEq ι]
  [Π i, DecidableEq (p i)] [Π i, Fintype (p i)] :
  (PiMat ℂ ι p ⊗[ℂ] PiMat ℂ ι p) ≃⋆ₐ[ℂ] (i : ι × ι) → (Matrix (p i.1) (p i.1) ℂ ⊗[ℂ] Matrix (p i.2) (p i.2) ℂ) :=
StarAlgEquiv.ofAlgEquiv (directSumTensorAlgEquiv ℂ
    (fun i ↦ Matrix (p i) (p i) ℂ) (fun i ↦ Matrix (p i) (p i) ℂ))
  (λ x => x.induction_on
    (by simp only [star_zero, map_zero])
    (λ _ _ => by
      ext
      simp only [Pi.star_apply, TensorProduct.star_tmul,
        directSumTensorAlgEquiv_apply, directSumTensorToFun_apply])
    (λ _ _ h1 h2 => by simp only [star_add, AlgEquiv.map_add, h1, h2]))

@[simps]
noncomputable def PiMat.transposeStarAlgEquiv
  (ι : Type*) (p : ι → Type*) [Fintype ι] [DecidableEq ι]
  [Π i, DecidableEq (p i)] [Π i, Fintype (p i)] :
    PiMat ℂ ι p ≃⋆ₐ[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ where
  toFun x := MulOpposite.op (λ i => (x i)ᵀ)
  invFun x i := (MulOpposite.unop x i)ᵀ
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := by
    simp only [Pi.mul_apply, Matrix.transpose_mul]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by
    simp only [MulOpposite.op_inj, Matrix.transpose_smul]
    rfl
  map_star' _ := rfl

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
private noncomputable def homEuclideanTensor
  (p : ι → Type*)
  [Π i, Fintype (p i)] [Π i, DecidableEq (p i)]
  (i j : ι) :
  (EuclideanSpace ℂ (p i) →ₗ[ℂ] EuclideanSpace ℂ (p i))
     ⊗[ℂ] (EuclideanSpace ℂ (p j) →ₗ[ℂ] EuclideanSpace ℂ (p j))
    ≃⋆ₐ[ℂ]
    (EuclideanSpace ℂ (p i) ⊗[ℂ] EuclideanSpace ℂ (p j))
    →ₗ[ℂ]
    (EuclideanSpace ℂ (p i) ⊗[ℂ] EuclideanSpace ℂ (p j)) :=
let aux := homTensorHomEquiv ℂ
  (EuclideanSpace ℂ (p i)) (EuclideanSpace ℂ (p j))
  (EuclideanSpace ℂ (p i)) (EuclideanSpace ℂ (p j))
starAlgEquivOfLinearEquivTensorProduct
  (aux)
  (by simp only [Algebra.TensorProduct.tmul_mul_tmul,
    aux, homTensorHomEquiv_apply,
    TensorProduct.homTensorHomMap_apply, TensorProduct.map_mul, implies_true])
  (by simp only [aux, homTensorHomEquiv_apply,
      TensorProduct.homTensorHomMap_apply, TensorProduct.map_one])
  (λ x y => by
    simp only [aux, TensorProduct.star_tmul]
    simp only [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
    simp only [LinearMap.star_eq_adjoint, TensorProduct.map_adjoint])

private noncomputable def matToEuclideanStarAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
  (Matrix n n ℂ) ≃⋆ₐ[ℂ] EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n :=
StarAlgEquiv.ofAlgEquiv
(AlgEquiv.ofLinearEquiv (Matrix.toEuclideanLin)
  (by simp only [toEuclideanLin_one])
  (λ x y => by
    simp only [Matrix.toEuclideanLin_eq_toLin,
      Matrix.toLin_mul (PiLp.basisFun 2 ℂ n) (PiLp.basisFun 2 ℂ n)]
    rfl))
(λ _ => by
  simp only [AlgEquiv.ofLinearEquiv_apply, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose,
    Matrix.toLin_conjTranspose])

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
private noncomputable def mat_tensor_toEuclidean
  (ι : Type*) (p : ι → Type*) [Fintype ι] [DecidableEq ι]
  [Π i, Fintype (p i)] [Π i, DecidableEq (p i)] :
  (PiMat ℂ ι p ⊗[ℂ] PiMat ℂ ι p)
    ≃⋆ₐ[ℂ] Π i : ι × ι,
      ((fun j => EuclideanSpace ℂ (p j.1) ⊗[ℂ] EuclideanSpace ℂ (p j.2)) i)
      →ₗ[ℂ]
      ((fun j => EuclideanSpace ℂ (p j.1) ⊗[ℂ] EuclideanSpace ℂ (p j.2)) i) :=
(PiMatTensorTo ι p).trans
(StarAlgEquiv.piCongrRight
(fun i =>
  ((StarAlgEquiv.TensorProduct.map (matToEuclideanStarAlgEquiv)
    matToEuclideanStarAlgEquiv).trans
    (homEuclideanTensor p i.1 i.2))))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem QuantumGraph.Real.PiMat_isOrthogonalProjection
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real (PiMat ℂ ι p) A)
  (i : ι × ι) :
  ContinuousLinearMap.IsOrthogonalProjection
  (LinearMap.toContinuousLinearMap
  (((mat_tensor_toEuclidean ι p)
  ((StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm)
  (QuantumSet.Psi 0 (1/2) A))) i)) :=
by
  have this' : k (PiMat ℂ ι p) = 0 := by rfl
  rw [← zero_add (1 / 2 : ℝ)]
  nth_rw 2 [← this']
  letI : ∀ i : ι × ι, Module.Finite ℂ (EuclideanSpace ℂ (p i.1) ⊗[ℂ] EuclideanSpace ℂ (p i.2)) :=
  λ i => Module.Finite.tensorProduct ℂ _ _
  letI : ∀ i : ι × ι, Star (EuclideanSpace ℂ (p i.1) ⊗[ℂ] EuclideanSpace ℂ (p i.2) →ₗ[ℂ]
    EuclideanSpace ℂ (p i.1) ⊗[ℂ] EuclideanSpace ℂ (p i.2)) :=
  λ i => by exact LinearMap.instStarId
  simp only [LinearMap.isOrthogonalProjection_iff, IsIdempotentElem,
    ← Pi.mul_apply _ _ i, ← map_mul,
    IsSelfAdjoint, ← Pi.star_apply _ i, ← map_star]
  simp only [(quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp hA).1.eq,
    (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp hA).2.star_eq, and_self]

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 1000000 in
theorem QuantumGraph.Real.PiMat_existsSubmodule {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) :
  ∃ U : Π i : ι × ι, Submodule ℂ (EuclideanSpace ℂ (p i.1) ⊗[ℂ] EuclideanSpace ℂ (p i.2)),
  ∀ i : ι × ι,
  orthogonalProjection' (U i) =
  (LinearMap.toContinuousLinearMap
  (((mat_tensor_toEuclidean ι p)
  ((StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm)
  (QuantumSet.Psi 0 ((1/2)) A))) i)) :=
by
  have := λ i => hA.PiMat_isOrthogonalProjection i
  simp_rw [ContinuousLinearMap.isOrthogonalProjection_iff',
    @and_comm (IsIdempotentElem _), ← orthogonal_projection_iff] at this
  exact ⟨λ _ => (this _).choose, λ _ => (this _).choose_spec⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 0 in
noncomputable def QuantumGraph.Real.PiMat_submodule {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) :
  Π i : ι × ι, Submodule ℂ (EuclideanSpace ℂ (p i.1)
    ⊗[ℂ] EuclideanSpace ℂ (p i.2)) :=
by
  choose y _ using QuantumGraph.Real.PiMat_existsSubmodule hA
  exact y

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 1000 in
theorem QuantumGraph.Real.PiMat_submoduleOrthogonalProjection
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) (i : ι × ι) :
  (orthogonalProjection' (hA.PiMat_submodule i)) =
    (LinearMap.toContinuousLinearMap
    (((mat_tensor_toEuclidean ι p)
    ((StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm)
    (QuantumSet.Psi 0 (1/2) A))) i)) :=
QuantumGraph.Real.PiMat_submodule.proof_32 hA i

set_option synthInstance.maxHeartbeats 0 in
noncomputable def QuantumGraph.Real.PiMat_orthonormalBasis {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) (i : ι × ι) :
  OrthonormalBasis (Fin (FiniteDimensional.finrank ℂ (hA.PiMat_submodule i))) ℂ (hA.PiMat_submodule i) :=
stdOrthonormalBasis ℂ (hA.PiMat_submodule i)
