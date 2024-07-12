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
private noncomputable abbrev PiMatTensorTo (ι : Type*)
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

noncomputable abbrev Matrix.toEuclideanStarAlgEquiv
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
theorem Matrix.toEuclideanStarAlgEquiv_coe {n : Type*} [Fintype n] [DecidableEq n] :
  ⇑(Matrix.toEuclideanStarAlgEquiv : Matrix n n ℂ ≃⋆ₐ[ℂ] EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) =
    Matrix.toEuclideanLin := rfl

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 57020 in
@[simps!]
noncomputable def PiMatTensorProductEquiv
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)] :
    (PiMat ℂ ι₁ p₁) ⊗[ℂ] (PiMat ℂ ι₂ p₂) ≃⋆ₐ[ℂ]
      PiMat ℂ (ι₁ × ι₂) (fun i : ι₁ × ι₂ => p₁ i.1 × p₂ i.2) :=
StarAlgEquiv.ofAlgEquiv
  ((directSumTensorAlgEquiv ℂ _ _).trans
    (AlgEquiv.piCongrRight (λ i => tensorToKronecker)))
  (λ x => by
    ext1
    simp only [Pi.star_apply, TensorProduct.toKronecker_star]
    congr 1
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
    simp only [AlgEquiv.trans_apply, AlgEquiv.piCongrRight_apply, directSumTensorAlgEquiv_apply,
      tensorToKronecker_apply]
    simp only [TensorProduct.star_tmul, directSumTensor_apply, map_sum, Finset.sum_apply, star_sum,
      directSumTensorToFun_apply, Pi.star_apply, TensorProduct.toKronecker_star])

theorem PiMatTensorProductEquiv_tmul
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)]
  (x : PiMat ℂ ι₁ p₁) (y : PiMat ℂ ι₂ p₂) (r : ι₁ × ι₂)
  (a c : p₁ r.1) (b d : p₂ r.2) :
    (PiMatTensorProductEquiv (x ⊗ₜ[ℂ] y)) r (a, b) (c, d) = x r.1 a c * y r.2 b d := by
  simp_rw [PiMatTensorProductEquiv_apply, directSumTensorToFun_apply,
    TensorProduct.toKronecker_apply]
  rfl

open scoped FiniteDimensional in
noncomputable def ContinuousLinearMap.toLinearMapStarAlgEquiv {𝕜 B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B] :
    (B →L[𝕜] B) ≃⋆ₐ[𝕜] (B →ₗ[𝕜] B) :=
StarAlgEquiv.ofAlgEquiv ContinuousLinearMap.toLinearMapAlgEquiv
  (λ x => by simp only [toLinearMapAlgEquiv_apply]; rfl)

noncomputable abbrev PiMat_toEuclideanLM :
  (PiMat ℂ ι p) ≃⋆ₐ[ℂ] (Π i, EuclideanSpace ℂ (p i) →ₗ[ℂ] EuclideanSpace ℂ (p i)) :=
StarAlgEquiv.piCongrRight (λ _ => Matrix.toEuclideanStarAlgEquiv)

theorem isIdempotentElem_iff {M : Type*} [Mul M] {p : M} :
  IsIdempotentElem p ↔ p * p = p :=
Iff.rfl

@[simps!]
noncomputable abbrev PiMat.traceLinearMap :
    (PiMat ℂ ι p) →ₗ[ℂ] ℂ :=
Matrix.traceLinearMap _ _ _ ∘ₗ Matrix.blockDiagonal'AlgHom.toLinearMap

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem QuantumGraph.PiMat_existsSubmoduleIsProj {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph (PiMat ℂ ι p) f) (t r : ℝ) :
  ∃ u : Π i : ι × ι, Submodule ℂ (EuclideanSpace ℂ (p i.1 × p i.2)),
    ∀ i : ι × ι, LinearMap.IsProj (u i)
    (PiMat_toEuclideanLM (PiMatTensorProductEquiv
    ((StarAlgEquiv.lTensor _
      (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f))) i) :=
by
  have : ∀ i, IsIdempotentElem
     ((PiMat_toEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _ (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f)))) i) :=
  by
    rw [← isIdempotentElem_pi_iff (a := (((PiMat_toEuclideanLM
      (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
        (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f)))))))]
    simp_rw [IsIdempotentElem.mulEquiv, ← schurIdempotent_iff_Psi_isIdempotentElem,
      hf.isIdempotentElem]
  simp_rw [isIdempotentElem_iff,  LinearMap.mul_eq_comp, ← LinearMap.isProj_iff_idempotent] at this
  exact ⟨λ i => (this i).choose, λ i => (this i).choose_spec⟩


noncomputable def QuantumGraph.PiMat_submodule {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
    (hf : QuantumGraph (PiMat ℂ ι p) f) (t r : ℝ) :
  Π i : ι × ι, Submodule ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) :=
by
  choose u _ using QuantumGraph.PiMat_existsSubmoduleIsProj hf t r
  exact u

set_option maxRecDepth 1000 in
theorem QuantumGraph.PiMat_submoduleIsProj {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph (PiMat ℂ ι p) f) (t r : ℝ) (i : ι × ι) :
  LinearMap.IsProj (hf.PiMat_submodule t r i)
  (PiMat_toEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
    (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f))) i) :=
QuantumGraph.PiMat_submodule.proof_18 hf t r i

theorem QuantumGraph.PiMat_submoduleIsProj_codRestrict {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph (PiMat ℂ ι p) f) (t r : ℝ) (i : ι × ι) :
  (Submodule.subtype _).comp (QuantumGraph.PiMat_submoduleIsProj hf t r i).codRestrict
    = (PiMat_toEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
      (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f))) i) :=
rfl

noncomputable def QuantumGraph.NumOfEdges {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph _ f) : ℕ :=
∑ i : ι × ι, FiniteDimensional.finrank ℂ (hf.PiMat_submodule 0 (1 / 2) i)

theorem QuantumGraph.numOfEdges_eq_trace {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph _ f) :
  QuantumGraph.NumOfEdges hf =
    PiMat.traceLinearMap
    (PiMatTensorProductEquiv
    ((StarAlgEquiv.lTensor _ (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi 0 (1 / 2) f))) :=
by
  rw [PiMat.traceLinearMap_apply, Matrix.blockDiagonal'AlgHom_apply,
    Matrix.trace_blockDiagonal', NumOfEdges]
  simp only [Nat.cast_sum, PiMatTensorProductEquiv_apply]
  congr
  ext i
  rw [← LinearMap.IsProj.trace (QuantumGraph.PiMat_submoduleIsProj hf 0 (1 / 2) i)]
  simp only [StarAlgEquiv.piCongrRight_apply,
    StarAlgEquiv.trans_apply,
    Matrix.toEuclideanStarAlgEquiv_coe,
    PiMatTensorProductEquiv_apply, EuclideanSpace.trace_eq_matrix_trace',
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, LinearEquiv.symm_apply_apply]

theorem orthogonalProjection_of_top {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace ↥(⊤ : Submodule 𝕜 E)] :
    orthogonalProjection' (⊤ : Submodule 𝕜 E) = 1 :=
  by
  ext1
  simp_rw [ContinuousLinearMap.one_apply, orthogonalProjection'_apply]
  rw [orthogonalProjection_eq_self_iff]
  simp only [Submodule.mem_top]

theorem LinearMap.IsProj.top (S M : Type*) [Semiring S] [AddCommMonoid M]
  [Module S M] :
    LinearMap.IsProj (⊤ : Submodule S M) (LinearMap.id (R := S)) :=
⟨fun _ ↦ trivial, fun _ ↦ congrFun rfl⟩

theorem LinearMap.IsProj.codRestrict_of_top {S M : Type*} [Semiring S] [AddCommMonoid M]
  [Module S M] :
    (Submodule.subtype ⊤).comp (LinearMap.IsProj.top S M).codRestrict = LinearMap.id :=
rfl
theorem LinearMap.IsProj.subtype_comp_codRestrict {S M : Type*} [Semiring S] [AddCommMonoid M]
  [Module S M] {U : Submodule S M} {f : M →ₗ[S] M} (hf : LinearMap.IsProj U f) :
    (Submodule.subtype U).comp hf.codRestrict = f :=
rfl

theorem LinearMap.IsProj.codRestrict_eq_dim_iff {S M : Type*}
  [Semiring S] [AddCommMonoid M] [Module S M]
  {f : M →ₗ[S] M} {U : Submodule S M} (hf : LinearMap.IsProj U f) :
    U = (⊤ : Submodule S M)
    ↔ (Submodule.subtype _).comp hf.codRestrict = LinearMap.id :=
by
  rw[LinearMap.IsProj.subtype_comp_codRestrict]
  constructor
  . rintro rfl
    ext
    simp only [id_coe, id_eq, hf.2 _ Submodule.mem_top]
  . rintro rfl
    refine Submodule.eq_top_iff'.mpr ?mpr.a
    intro x
    rw [← id_apply (R := S) x]
    exact hf.map_mem x

theorem QuantumSet.Psi_apply_completeGraph {A : Type*} {B : Type*} [starAlgebra A]
    [starAlgebra B] [QuantumSet A] [QuantumSet B] (t r : ℝ) :
  QuantumSet.Psi t r (Qam.completeGraph A B) = 1 :=
by
  simp only [Qam.completeGraph, Psi_apply, Psi_toFun_apply]
  simp only [map_one, star_one, MulOpposite.op_one, Algebra.TensorProduct.one_def]
theorem QuantumSet.Psi_symm_one {A B : Type*} [starAlgebra A]
  [starAlgebra B] [QuantumSet A] [QuantumSet B] (t r : ℝ) :
  (QuantumSet.Psi t r).symm 1 = Qam.completeGraph A B :=
by rw [← QuantumSet.Psi_apply_completeGraph t r, LinearEquiv.symm_apply_apply]

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
theorem QuantumGraph.numOfEdges_eq_rank_top_iff
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hf : QuantumGraph _ f) :
  QuantumGraph.NumOfEdges hf = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2)
    ↔ f = Qam.completeGraph _ _ :=
by
  calc
    QuantumGraph.NumOfEdges hf = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2)
      ↔ ∑ i : ι × ι, FiniteDimensional.finrank ℂ ↥(hf.PiMat_submodule 0 (1 / 2) i)
        = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2) := by rfl
    _ ↔ ∀ i, FiniteDimensional.finrank ℂ ↥(hf.PiMat_submodule 0 (1 / 2) i)
      = Fintype.card (p i.1) * Fintype.card (p i.2) := by
        rw [← Nat.cast_inj (R := ℂ)]
        simp only [Nat.cast_sum]
        rw [eq_comm, ← sub_eq_zero, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_zero_iff_of_nonneg]
        simp_rw [sub_eq_zero, Nat.cast_inj, Finset.mem_univ, true_imp_iff,
          ← Fintype.card_prod, ← finrank_euclideanSpace (𝕜 := ℂ),
          @eq_comm _ _ (FiniteDimensional.finrank ℂ (hf.PiMat_submodule 0 (1/2) _))]
        . simp only [Finset.mem_univ, sub_nonneg, true_implies, Nat.cast_le]
          intro i
          calc FiniteDimensional.finrank ℂ (↥(hf.PiMat_submodule 0 (1 / 2) i))
            ≤ FiniteDimensional.finrank ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) :=
                Submodule.finrank_le _
            _ = Fintype.card (p i.1) * Fintype.card (p i.2) := by
              simp only [finrank_euclideanSpace, Fintype.card_prod]
    _ ↔
      ∀ i, hf.PiMat_submodule 0 (1 / 2) i = (⊤ : Submodule ℂ (EuclideanSpace ℂ (p i.1 × p i.2))) :=
        by
          simp_rw [← Fintype.card_prod, ← finrank_euclideanSpace (𝕜 := ℂ)]
          constructor
          . intro h i
            exact Submodule.eq_top_of_finrank_eq (h i)
          . intro h i
            rw [h]
            simp only [finrank_top]
    _ ↔
      ∀ i, (PiMat_toEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
    (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi 0 (1/2) f))) i)
      = LinearMap.id := by
        simp_rw [LinearMap.IsProj.codRestrict_eq_dim_iff (hf.PiMat_submoduleIsProj 0 (1/2) _),
          LinearMap.IsProj.subtype_comp_codRestrict]
    _
      ↔ (PiMat_toEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
    (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi 0 (1/2) f))))
      = 1 := by
        rw [Function.funext_iff]; exact Iff.rfl
    _ ↔ f = Qam.completeGraph _ _ :=
      by
        rw [eq_comm]
        simp_rw [StarAlgEquiv.eq_apply_iff_symm_eq, map_one]
        rw [← LinearEquiv.symm_apply_eq, QuantumSet.Psi_symm_one, eq_comm]

theorem QuantumGraph.CompleteGraph_numOfEdges :
  QuantumGraph.NumOfEdges
    (⟨Qam.Nontracial.CompleteGraph.qam⟩ : QuantumGraph _ (Qam.completeGraph (PiMat ℂ ι p) (PiMat ℂ ι p)))
      = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2) :=
by rw [QuantumGraph.numOfEdges_eq_rank_top_iff]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 0 in
theorem QuantumGraph.Real.PiMat_isOrthogonalProjection
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real (PiMat ℂ ι p) A)
  (i : ι × ι) :
  ContinuousLinearMap.IsOrthogonalProjection
  (LinearMap.toContinuousLinearMap
    (PiMat_toEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
    (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi 0 (1 / 2) A))) i)) :=
by
  have this' : k (PiMat ℂ ι p) = 0 := by rfl
  rw [← zero_add (1 / 2 : ℝ)]
  nth_rw 2 [← this']
  simp only [LinearMap.isOrthogonalProjection_iff, IsIdempotentElem,
    ← Pi.mul_apply _ _ i, ← map_mul,
    IsSelfAdjoint, ← Pi.star_apply _ i, ← map_star]
  simp only [(quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp hA).1.eq,
    (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp hA).2.star_eq, and_self]

set_option synthInstance.maxHeartbeats 0 in
noncomputable def QuantumGraph.Real.PiMat_submodule {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) :
  Π i : ι × ι, Submodule ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) :=
by
  intro i
  choose y _ using
    (orthogonal_projection_iff.mpr
    (And.comm.mp
    (ContinuousLinearMap.isOrthogonalProjection_iff'.mp
      (QuantumGraph.Real.PiMat_isOrthogonalProjection hA i))))
  exact y

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 1000 in
theorem QuantumGraph.Real.PiMat_submoduleOrthogonalProjection
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) (i : ι × ι) :
  (orthogonalProjection' (hA.PiMat_submodule i)) =
    (LinearMap.toContinuousLinearMap
    ((PiMat_toEuclideanLM (PiMatTensorProductEquiv
    ((StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm)
    (QuantumSet.Psi 0 (1/2) A))) i))) :=
QuantumGraph.Real.PiMat_submodule.proof_28 hA i

set_option synthInstance.maxHeartbeats 0 in
noncomputable def QuantumGraph.Real.PiMat_orthonormalBasis {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) (i : ι × ι) :
  OrthonormalBasis (Fin (FiniteDimensional.finrank ℂ (hA.PiMat_submodule i))) ℂ (hA.PiMat_submodule i) :=
stdOrthonormalBasis ℂ (hA.PiMat_submodule i)

set_option synthInstance.maxHeartbeats 0 in
theorem EuclideanSpace.prod_exists_finset {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  ∃ S : Finset ((EuclideanSpace ℂ n) × EuclideanSpace ℂ m),
    x = ∑ s in S, euclideanSpaceTensor' (s.1 ⊗ₜ[ℂ] s.2) :=
by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (euclideanSpaceTensor'.symm x)
  use S
  apply_fun euclideanSpaceTensor'.symm using LinearEquiv.injective _
  simp only [map_sum, LinearEquiv.symm_apply_apply, hS]

theorem QuantumSet.PiMat_n :
  n (PiMat ℂ ι p) = ((i : ι) × (p i × p i)) :=
rfl

open Kronecker

@[simp]
theorem Matrix.ite_kronecker {α n m p q : Type*} [MulZeroClass α] (x₁ : Matrix n m α)
  (x₂ : Matrix p q α) (P : Prop) [Decidable P] :
  (if P then x₁ else 0) ⊗ₖ x₂ = if P then x₁ ⊗ₖ x₂ else 0 :=
by
  split
  next h => simp_all only
  next h => simp_all only [zero_mul, implies_true, kroneckerMap_zero_left]
@[simp]
theorem Matrix.dite_kronecker {α n m p q : Type*} [MulZeroClass α]
  (P : Prop) [Decidable P]
  (x₁ : P → Matrix n m α) (x₂ : Matrix p q α) :
  (dite P (λ p => x₁ p) (λ _ => 0)) ⊗ₖ x₂ = dite P (λ p => x₁ p ⊗ₖ x₂) (λ _ => 0) :=
by
  split
  next h => simp_all only
  next h => simp_all only [zero_mul, implies_true, kroneckerMap_zero_left]

@[simp]
theorem Matrix.kronecker_ite {α n m p q : Type*} [MulZeroClass α] (x₁ : Matrix n m α)
  (x₂ : Matrix p q α) (P : Prop) [Decidable P] :
  x₁ ⊗ₖ (if P then x₂ else 0) = if P then x₁ ⊗ₖ x₂ else 0 :=
by
  split
  next h => simp_all only
  next h => simp_all only [mul_zero, implies_true, kroneckerMap_zero_right]
@[simp]
theorem Matrix.kronecker_dite {α n m p q : Type*} [MulZeroClass α]
  (x₁ : Matrix n m α) (P : Prop) [Decidable P] (x₂ : P → Matrix p q α) :
  x₁ ⊗ₖ (dite P (λ p => x₂ p) (λ _ => 0)) = dite P (λ p => x₁ ⊗ₖ x₂ p) (λ _ => 0) :=
by
  split
  next h => simp_all only
  next h => simp_all only [mul_zero, implies_true, kroneckerMap_zero_right]

theorem Matrix.vecMulVec_kronecker_vecMulVec {α n m p q : Type*} [CommSemiring α]
    (x : n → α) (y : m → α) (z : p → α) (w : q → α) :
  (vecMulVec x y) ⊗ₖ (vecMulVec z w) =
    vecMulVec (reshape (vecMulVec x z)) (reshape (vecMulVec y w)) :=
by
  ext
  simp only [kroneckerMap_apply, zero_apply, vecMulVec_apply, reshape_apply]
  ring_nf

@[simp]
theorem Matrix.vecMulVec_toEuclideanLin {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  toEuclideanLin (vecMulVec x y) = rankOne ℂ x (star y) :=
by
  apply_fun Matrix.toEuclideanLin.symm using LinearEquiv.injective _
  simp only [LinearEquiv.symm_apply_apply, rankOne.EuclideanSpace.toEuclideanLin_symm]
  simp only [conjTranspose_col, star_star]
  simp only [← vecMulVec_eq]

open Matrix in
theorem EuclideanSpaceTensor_apply_eq_reshape_vecMulVec {n m : Type*} [Fintype n]
  [DecidableEq n] [Fintype m] [DecidableEq m]
  (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  euclideanSpaceTensor' (x ⊗ₜ[ℂ] y) = reshape (vecMulVec x y) :=
by
  ext1
  simp only [euclideanSpaceTensor'_apply, reshape_apply, vecMulVec_apply]

theorem Matrix.vecMulVec_conj {α n m : Type*} [CommSemiring α] [StarMul α] (x : n → α) (y : m → α) :
  (vecMulVec x y)ᴴᵀ = vecMulVec (star x) (star y) :=
by
  ext
  simp only [conj_apply, vecMulVec_apply, Pi.star_apply, star_mul']

noncomputable def TensorProduct.chooseFinset {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  (x : TensorProduct R M N) :
    Finset (M × N) :=
by
  choose S _ using TensorProduct.exists_finset x
  exact S
theorem TensorProduct.chooseFinset_spec {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  (x : TensorProduct R M N) :
  x = ∑ s in (TensorProduct.chooseFinset x), s.1 ⊗ₜ s.2 :=
TensorProduct.chooseFinset.proof_1 x

noncomputable def EuclideanSpace.prod_chooseFinset {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  Finset ((EuclideanSpace ℂ n) × EuclideanSpace ℂ m) :=
by
  choose S _ using EuclideanSpace.prod_exists_finset x
  exact S
theorem EuclideanSpace.prod_chooseFinset_spec {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  x = ∑ s in (EuclideanSpace.prod_chooseFinset x), euclideanSpaceTensor' (s.1 ⊗ₜ s.2) :=
EuclideanSpace.prod_chooseFinset.proof_2 x

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
theorem QuantumGraph.Real.PiMat_eq {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) :
  let S : (i : ι × ι) →
    (j : (Fin (FiniteDimensional.finrank ℂ (hA.PiMat_submodule i)))) → Finset (((EuclideanSpace ℂ (p i.1)) × (EuclideanSpace ℂ (p i.2))))
    := λ i j => (hA.PiMat_orthonormalBasis i j : EuclideanSpace ℂ _).prod_chooseFinset
  A = ∑ i : ι × ι, ∑ j, ∑ s in S i j, ∑ p in S i j,
    rankOne ℂ (Matrix.includeBlock
      (Matrix.vecMulVec s.1 (star p.1)))
      (modAut (- (1 / 2)) (Matrix.includeBlock
        ((Matrix.vecMulVec s.2 (star p.2))ᴴᵀ))) :=
by
  intro S
  have hS : ∀ (i : ι × ι) j, (hA.PiMat_orthonormalBasis i j) = ∑ t in S i j,
    euclideanSpaceTensor' (t.1 ⊗ₜ[ℂ] t.2) :=
  λ i j => EuclideanSpace.prod_chooseFinset_spec _
  apply_fun (QuantumSet.Psi 0 (1/2)) using LinearEquiv.injective _
  apply_fun
    (StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm).trans
    (PiMatTensorProductEquiv.trans PiMat_toEuclideanLM)
  simp only [StarAlgEquiv.trans_apply]
  ext1 i
  apply_fun LinearMap.toContinuousLinearMap using LinearEquiv.injective _
  rw [← QuantumGraph.Real.PiMat_submoduleOrthogonalProjection hA i,
    OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne (hA.PiMat_orthonormalBasis i)]
  simp only [ContinuousLinearMap.coe_sum, map_sum,
    QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply,
    StarAlgEquiv.lTensor_tmul,
    PiMat_toEuclideanLM, PiMatTensorProductEquiv_apply]
  simp only [starAlgebra.modAut_zero, Matrix.conjTranspose_col, AlgEquiv.one_apply, one_div,
    starAlgebra.modAut_star, Finset.sum_apply, StarAlgEquiv.piCongrRight_apply,
    PiMatTensorProductEquiv_apply, StarAlgEquiv.ofAlgEquiv_coe, AlgEquiv.ofLinearEquiv_apply,
    Fintype.sum_prod_type, map_sum, directSumTensorToFun_apply,
    PiMat.transposeStarAlgEquiv_symm_apply,
    MulOpposite.unop_op]
  simp only [TensorProduct.toKronecker_apply, Matrix.toEuclideanLin_apply']
  simp only [QuantumSet.modAut_apply_modAut, add_neg_self, starAlgebra.modAut_zero]
  simp only [Matrix.includeBlock_conjTranspose, Matrix.conj_conjTranspose, Matrix.transpose_apply]
  simp_rw [hS, AlgEquiv.one_apply, Matrix.includeBlock_apply]
  simp only [ContinuousLinearMap.sum_apply, map_sum, Matrix.dite_kronecker,
    Matrix.kronecker_dite, apply_dite, Matrix.transpose_zero, map_zero,
    Matrix.transpose_transpose, Matrix.kronecker_zero]
  simp only [Finset.sum_dite_irrel, Finset.sum_const_zero,
    Finset.sum_dite_eq', Finset.sum_dite_eq,
    Finset.mem_univ, if_true]
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, eq_mp_eq_cast, cast_eq,
    Matrix.transpose_transpose, Matrix.vecMulVec_kronecker_vecMulVec,
    Matrix.vecMulVec_toEuclideanLin, EuclideanSpaceTensor_apply_eq_reshape_vecMulVec]
  simp only [Matrix.reshape_aux_star (R := ℂ), Matrix.vecMulVec_conj, star_star]
  congr 1
  ext1
  rw [Finset.sum_comm]
  rfl
