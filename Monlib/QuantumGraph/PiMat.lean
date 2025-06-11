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
    (λ _ _ h1 h2 => by simp only [star_add, map_add, h1, h2]))

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
    -- simp only [MulOpposite.op_inj, Matrix.transpose_smul]
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
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
    simp only [AlgEquiv.trans_apply, AlgEquiv.piCongrRight_apply, directSumTensorAlgEquiv_apply,
      tensorToKronecker_apply]
    simp only [TensorProduct.star_tmul, directSumTensor_apply, map_sum, Finset.sum_apply, star_sum,
      directSumTensorToFun_apply, Pi.star_apply, TensorProduct.toKronecker_star])

theorem PiMatTensorProductEquiv_tmul_apply
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)]
  (x : PiMat ℂ ι₁ p₁) (y : PiMat ℂ ι₂ p₂) (r : ι₁ × ι₂)
  (a b : p₁ r.1 × p₂ r.2) :
    (PiMatTensorProductEquiv (x ⊗ₜ[ℂ] y)) r a b = x r.1 a.1 b.1 * y r.2 a.2 b.2 := by
  simp_rw [PiMatTensorProductEquiv_apply, directSumTensorToFun_apply,
    TensorProduct.toKronecker_apply]
  rfl
open scoped Kronecker
theorem PiMatTensorProductEquiv_tmul
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)]
  (x : PiMat ℂ ι₁ p₁) (y : PiMat ℂ ι₂ p₂) :
    (PiMatTensorProductEquiv (x ⊗ₜ[ℂ] y)) = λ r : ι₁ × ι₂ => (x r.1 ⊗ₖ y r.2) := by
  ext; simp only [PiMatTensorProductEquiv_tmul_apply, Matrix.kronecker_apply]; rfl

theorem PiMatTensorProductEquiv_tmul_apply'
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)]
  (x : PiMat ℂ ι₁ p₁) (y : PiMat ℂ ι₂ p₂) (r : ι₁ × ι₂)
  (a c : p₁ r.1) (b d : p₂ r.2) :
    (PiMatTensorProductEquiv (x ⊗ₜ[ℂ] y)) r (a, b) (c, d) = x r.1 a c * y r.2 b d :=
PiMatTensorProductEquiv_tmul_apply _ _ _ _ _

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
  simp_rw [← LinearMap.isProj_iff_isIdempotentElem] at this
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
by
  rw [PiMat_submodule]
  generalize_proofs
  (expose_names; exact pf_23 i)
-- QuantumGraph.PiMat_submodule.proof_17 hf t r i

theorem QuantumGraph.PiMat_submoduleIsProj_codRestrict {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph (PiMat ℂ ι p) f) (t r : ℝ) (i : ι × ι) :
  (Submodule.subtype _).comp (QuantumGraph.PiMat_submoduleIsProj hf t r i).codRestrict
    = (PiMat_toEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
      (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f))) i) :=
rfl

noncomputable def QuantumGraph.dim_of_piMat_submodule {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph _ f) : ℕ :=
∑ i : ι × ι, Module.finrank ℂ (hf.PiMat_submodule 0 (1 / 2) i)

theorem PiMat.traceLinearMap_comp_piMatTensorProductEquiv_eq :
  (PiMat.traceLinearMap : (PiMat ℂ (ι × ι) fun i ↦ p i.1 × p i.2) →ₗ[ℂ] ℂ) ∘ₗ PiMatTensorProductEquiv.toLinearMap
    = LinearMap.mul' ℂ _ ∘ₗ (TensorProduct.map PiMat.traceLinearMap PiMat.traceLinearMap) :=
by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,  PiMatTensorProductEquiv_tmul,
    PiMat.traceLinearMap_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    AlgHom.toLinearMap_apply, Matrix.blockDiagonal'AlgHom_apply,
    Matrix.traceLinearMap_apply,
    Matrix.trace_blockDiagonal', Matrix.trace_kronecker,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_product_univ]
  rw [Finset.sum_comm]

lemma PiMat.transposeStarAlgEquiv_symm_is_tracePreserving (x : (PiMat ℂ ι p)ᵐᵒᵖ) :
  PiMat.traceLinearMap ((PiMat.transposeStarAlgEquiv ι p).symm x) = PiMat.traceLinearMap (MulOpposite.unop x) :=
rfl

lemma PiMat.traceLinearMap_comp_transposeStarAlgEquiv_symm :
  PiMat.traceLinearMap ∘ₗ (PiMat.transposeStarAlgEquiv ι p).symm.toLinearMap
    = PiMat.traceLinearMap ∘ₗ (unop ℂ (A := PiMat ℂ ι p)).toLinearMap :=
rfl

theorem QuantumGraph.dim_of_piMat_submodule_eq_trace {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph _ f) :
  QuantumGraph.dim_of_piMat_submodule hf =
    PiMat.traceLinearMap
    (PiMatTensorProductEquiv
    ((StarAlgEquiv.lTensor _ (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi 0 (1 / 2) f))) :=
by
  rw [PiMat.traceLinearMap_apply, Matrix.blockDiagonal'AlgHom_apply,
    Matrix.trace_blockDiagonal', dim_of_piMat_submodule]
  simp only [Nat.cast_sum, PiMatTensorProductEquiv_apply]
  congr
  ext i
  rw [← LinearMap.IsProj.trace (QuantumGraph.PiMat_submoduleIsProj hf 0 (1 / 2) i)]
  simp only [StarAlgEquiv.piCongrRight_apply,
    StarAlgEquiv.trans_apply,
    Matrix.toEuclideanStarAlgEquiv_coe,
    PiMatTensorProductEquiv_apply, EuclideanSpace.trace_eq_matrix_trace',
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, LinearEquiv.symm_apply_apply]

theorem Coalgebra.counit_mulOpposite {A : Type*}
  [Semiring A] [Algebra ℂ A] [CoalgebraStruct ℂ A] :
  Coalgebra.counit (R := ℂ) (A := Aᵐᵒᵖ) = Coalgebra.counit ∘ₗ (unop ℂ).toLinearMap :=
rfl

theorem StarAlgEquiv.lTensor_toLinearMap {R A B C : Type*}
  [RCLike R] [Ring A] [Ring B] [Ring C] [Algebra R A]
  [Algebra R B] [Algebra R C] [StarAddMonoid A] [StarAddMonoid B]
  [StarAddMonoid C] [StarModule R A] [StarModule R B]
  [StarModule R C] [Module.Finite R A] [Module.Finite R B]
  [Module.Finite R C] (f : A ≃⋆ₐ[R] B) :
  (StarAlgEquiv.lTensor C f).toLinearMap = LinearMap.lTensor C f.toLinearMap :=
rfl

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

-- noncomputable instance MulOppositeCoalgebra {A : Type*} [Semiring A] [Algebra ℂ A]
--   [Coalgebra ℂ A] :
--     Coalgebra ℂ Aᵐᵒᵖ where
--   coassoc := sorry
--   rTensor_counit_comp_comul := sorry
--   lTensor_counit_comp_comul := sorry

-- remove this...
noncomputable instance TensorProduct.instCoalgebraStruct'
  {R S A B : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [AddCommMonoid B]
    [Algebra R S] [Module R A] [Module S A] [Module R B] [CoalgebraStruct R B]
    [CoalgebraStruct S A] [IsScalarTower R S A] : CoalgebraStruct S (A ⊗[R] B) where
  comul :=
    AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
      AlgebraTensorModule.map CoalgebraStruct.comul CoalgebraStruct.comul
  counit := AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map CoalgebraStruct.counit CoalgebraStruct.counit

lemma TensorProduct.instCoalgebraStruct'_counit
  {R S A B : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [AddCommMonoid B]
  [Algebra R S] [Module R A] [Module S A] [Module R B] [CoalgebraStruct R B]
  [CoalgebraStruct S A] [IsScalarTower R S A] :
  (TensorProduct.instCoalgebraStruct' : CoalgebraStruct S (A ⊗[R] B)).counit =
    AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map CoalgebraStruct.counit CoalgebraStruct.counit :=
rfl

-- attribute [local instance] TensorProduct.instCoalgebraStruct'

-- instance :
--   Coalgebra ℂ (PiMat ℂ ι p ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) :=
-- Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ) (A := PiMat ℂ ι p ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ)

theorem QuantumGraph.dim_of_piMat_submodule_eq_trace_counit
  (hc : (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p)) = PiMat.traceLinearMap)
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph _ f) :
  QuantumGraph.dim_of_piMat_submodule hf =
    (Coalgebra.counit (R := ℂ)) (QuantumSet.Psi 0 (1 / 2) f) :=
by
  simp only [TensorProduct.instCoalgebraStruct'_counit,
    LinearMap.coe_comp, Function.comp_apply, hc, Coalgebra.counit_mulOpposite]
  rw [QuantumGraph.dim_of_piMat_submodule_eq_trace]
  simp only [← StarAlgEquiv.toLinearMap_apply, ← LinearMap.comp_apply,
    ← LinearMap.comp_assoc,
    PiMat.traceLinearMap_comp_piMatTensorProductEquiv_eq,
    StarAlgEquiv.lTensor_toLinearMap]
  rw [LinearMap.comp_assoc, LinearMap.map_comp_lTensor]
  simp
  congr 1
  ext; simp

-- set_option maxHeartbeats 500000 in
theorem Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one
  {A : Type*} [NormedAddCommGroupOfRing A]
  [InnerProductSpace ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [FiniteDimensional ℂ A] :
  Coalgebra.counit (R := ℂ) (A := A ⊗[ℂ] Aᵐᵒᵖ)
    = (bra ℂ (1 : A ⊗[ℂ] Aᵐᵒᵖ)).toLinearMap :=
by
  -- letI : FiniteDimensional ℂ (A ⊗[ℂ] Aᵐᵒᵖ) := by infer_instance
  -- -- letI
  -- letI := TensorProduct.instNormedAddCommGroupOfRing (R:= ℂ) (A := A) (B := Aᵐᵒᵖ)
  -- exact @Coalgebra.counit_eq_bra_one ℂ (A ⊗[ℂ] Aᵐᵒᵖ)
  --   _ _ _ _ _ _
  apply TensorProduct.ext'
  intro x y
  -- rw [TensorProduct.counit_def]
  simp only [TensorProduct.instCoalgebraStruct'_counit, LinearMap.coe_comp, Function.comp_apply,
    TensorProduct.map_tmul, LinearMap.mul'_apply, Algebra.TensorProduct.one_def,
    ContinuousLinearMap.coe_coe, innerSL_apply, TensorProduct.inner_tmul,
    Coalgebra.inner_eq_counit', Coalgebra.counit_mulOpposite_eq,
    MulOpposite.inner_eq, MulOpposite.unop_one,
    TensorProduct.AlgebraTensorModule.map_tmul]
  simp only [LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.rid_tmul, smul_eq_mul, mul_comm]

lemma QuantumGraph.NumOfEdges_apply {A : Type*} [starAlgebra A] [QuantumSet A]
  (f : A →ₗ[ℂ] A) : NumOfEdges f = inner ℂ 1 (f 1) :=
rfl

-- instance {A : Type*} [NormedAddCommGroupOfRing A] :
--   NormedAddCommGroupOfRing Aᵐᵒᵖ where
-- noncomputable instance {A : Type*} [NormedAddCommGroup A]
--   [InnerProductSpace ℂ A] : InnerProductSpace ℂ Aᵐᵒᵖ where
--   norm_sq_eq_re_inner _ := by
--     simp [MulOpposite.inner_eq, norm_eq_sqrt_re_inner (𝕜 := ℂ)]
--     rw [← RCLike.re_eq_complex_re]
--     exact Real.sq_sqrt (inner_self_nonneg)
--   conj_inner_symm _ _ := inner_conj_symm _ _
--   add_left _ _ _ := inner_add_left _ _ _
--   smul_left x y _ := inner_smul_left _ _ _
-- noncomputable instance {A : Type*} [NormedAddCommGroupOfRing A] [InnerProductSpace ℂ A]
--   [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
--   [FiniteDimensional ℂ A] :
--   NormedAddCommGroupOfRing (A ⊗[ℂ] Aᵐᵒᵖ) where

private lemma Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one_piMat :
  CoalgebraStruct.counit (R:= ℂ) (A:= PiMat ℂ ι p ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) = ((bra ℂ) (1 : PiMat ℂ ι p ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ)).toLinearMap :=
by
  apply TensorProduct.ext'
  intro _ _
  rw [Algebra.TensorProduct.one_def, bra_tmul, LinearMap.comp_apply,
    _root_.TensorProduct.map_tmul, TensorProduct.instCoalgebraStruct'_counit,
    LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.map_tmul]
  simp_rw [counit_mulOpposite_eq, Coalgebra.counit_eq_bra_one]
  rw [← MulOpposite.op_one]
  simp [mul_comm, MulOpposite.inner_eq]

set_option maxHeartbeats 400000 in
theorem QuantumGraph.dim_of_piMat_submodule_eq_numOfEdges_of_trace_counit
  (hc : (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p)) = PiMat.traceLinearMap)
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph _ f) :
  hf.dim_of_piMat_submodule = QuantumGraph.NumOfEdges f :=
by
  rw [QuantumGraph.dim_of_piMat_submodule_eq_trace_counit hc,
    NumOfEdges_apply, oneInner_map_one_eq_oneInner_Psi_map _ 0 (1/2)]
  simp only [Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one_piMat]
  rfl

  -- rw [Coalgebra.counit_eq_bra_one]
  -- rw [Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one]
  -- rfl

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
theorem QuantumGraph.dim_of_piMat_submodule_eq_rank_top_iff
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hf : QuantumGraph _ f) :
  QuantumGraph.dim_of_piMat_submodule hf = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2)
    ↔ f = Qam.completeGraph _ _ :=
by
  calc
    QuantumGraph.dim_of_piMat_submodule hf = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2)
      ↔ ∑ i : ι × ι, Module.finrank ℂ ↥(hf.PiMat_submodule 0 (1 / 2) i)
        = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2) := by rfl
    _ ↔ ∀ i, Module.finrank ℂ ↥(hf.PiMat_submodule 0 (1 / 2) i)
      = Fintype.card (p i.1) * Fintype.card (p i.2) := by
        rw [← Nat.cast_inj (R := ℂ)]
        simp only [Nat.cast_sum]
        rw [eq_comm, ← sub_eq_zero, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_zero_iff_of_nonneg]
        simp_rw [sub_eq_zero, Nat.cast_inj, Finset.mem_univ, true_imp_iff,
          ← Fintype.card_prod, ← finrank_euclideanSpace (𝕜 := ℂ),
          @eq_comm _ _ (Module.finrank ℂ (hf.PiMat_submodule 0 (1/2) _))]
        . simp only [Finset.mem_univ, sub_nonneg, true_implies, Nat.cast_le]
          intro i
          calc Module.finrank ℂ (↥(hf.PiMat_submodule 0 (1 / 2) i))
            ≤ Module.finrank ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) :=
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
        rw [funext_iff]; exact Iff.rfl
    _ ↔ f = Qam.completeGraph _ _ :=
      by
        rw [eq_comm]
        simp_rw [StarAlgEquiv.eq_apply_iff_symm_eq, map_one]
        rw [← LinearEquiv.symm_apply_eq, QuantumSet.Psi_symm_one, eq_comm]

theorem QuantumGraph.CompleteGraph_dim_of_piMat_submodule :
  QuantumGraph.dim_of_piMat_submodule
    (⟨Qam.Nontracial.CompleteGraph.qam⟩ : QuantumGraph _ (Qam.completeGraph (PiMat ℂ ι p) (PiMat ℂ ι p)))
      = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2) :=
by rw [QuantumGraph.dim_of_piMat_submodule_eq_rank_top_iff]

open scoped InnerProductSpace
theorem Algebra.linearMap_adjoint_eq_dual :
  LinearMap.adjoint (Algebra.linearMap ℂ (PiMat ℂ ι p))
    = Module.Dual.pi φ :=
by
  rw [← Module.Dual.pi.IsFaithfulPosMap.adjoint_eq, LinearMap.adjoint_adjoint]

theorem exists_dim_of_piMat_submodule_ne_inner_one_map_one_of_IsFaithfulState
  (hφ₂ : (Module.Dual.pi φ).IsUnital)
  (hB : 1 < Module.finrank ℂ (PiMat ℂ ι p)) :
  ∃ (A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p) (hA : QuantumGraph (PiMat ℂ ι p) A),
    QuantumGraph.NumOfEdges A ≠ QuantumGraph.dim_of_piMat_submodule hA :=
by
  use Qam.completeGraph _ _, ⟨Qam.Nontracial.CompleteGraph.qam⟩
  rw [QuantumGraph.CompleteGraph_dim_of_piMat_submodule, Qam.completeGraph,
    QuantumGraph.NumOfEdges]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_coe,
    rankOne_apply_apply_apply, ne_eq]
  have : ⟪(1 : PiMat ℂ ι p), 1⟫_ℂ = 1 :=
  by
    simp_rw [Coalgebra.inner_eq_counit', Coalgebra.counit_eq_unit_adjoint]
    rw [← hφ₂]
    congr
    rw [← Algebra.linearMap_adjoint_eq_dual]
    congr; ext; rfl
  simp_rw [ne_eq, this, one_smul, this]
  rw [← Nat.cast_one, Nat.cast_inj]
  simp [Module.finrank_pi_fintype, Module.finrank_matrix, ← pow_two] at hB
  have :=
    calc ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2)
      = ∑ i : ι, ∑ j : ι, Fintype.card (p i) * Fintype.card (p j) :=
        by simp_rw [Finset.sum_product_univ]
      _ = (∑ i : ι, Fintype.card (p i)) ^ 2 :=
        by simp_rw [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [this, eq_comm, ← one_pow 2, sq_eq_sq₀ (by simp) (by simp)]
  contrapose! hB
  calc ∑ x : ι, Fintype.card (p x) ^ 2 ≤ (∑ i : ι, Fintype.card (p i)) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (by simp)
    _ = 1 := by rw [hB, one_pow]

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
by
  rw [QuantumGraph.Real.PiMat_submodule]
  generalize_proofs
  (expose_names; exact pf_32)
-- QuantumGraph.Real.PiMat_submodule.proof_28 hA i

set_option synthInstance.maxHeartbeats 0 in
noncomputable def QuantumGraph.Real.PiMat_orthonormalBasis {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) (i : ι × ι) :
  OrthonormalBasis (Fin (Module.finrank ℂ (hA.PiMat_submodule i))) ℂ (hA.PiMat_submodule i) :=
stdOrthonormalBasis ℂ (hA.PiMat_submodule i)

set_option synthInstance.maxHeartbeats 0 in
theorem EuclideanSpace.prod_exists_finset {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  ∃ S : Finset ((EuclideanSpace ℂ n) × EuclideanSpace ℂ m),
    x = ∑ s ∈ S, euclideanSpaceTensor' (R := ℂ) (s.1 ⊗ₜ[ℂ] s.2) :=
by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset ((euclideanSpaceTensor' (R:=ℂ)).symm x)
  use S
  apply_fun (euclideanSpaceTensor' (R:=ℂ)).symm using LinearEquiv.injective _
  simp only [map_sum, LinearIsometryEquiv.symm_apply_apply, hS]

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
  simp only [conjTranspose_replicateCol, star_star]
  simp only [← vecMulVec_eq]

open Matrix in
theorem EuclideanSpaceTensor_apply_eq_reshape_vecMulVec {n m : Type*} [Fintype n]
  [DecidableEq n] [Fintype m] [DecidableEq m]
  (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  euclideanSpaceTensor' (R:=ℂ) (x ⊗ₜ[ℂ] y) = reshape (vecMulVec x y) :=
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
  x = ∑ s ∈ (TensorProduct.chooseFinset x), s.1 ⊗ₜ s.2 :=
by
  rw [TensorProduct.chooseFinset]
  generalize_proofs
  (expose_names; exact pf_2)
-- TensorProduct.chooseFinset.proof_1 x

-- changed from choosing some `Finset (_ × _)` like above to the following
noncomputable def EuclideanSpace.prod_choose {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  (n × m) → ((EuclideanSpace ℂ n) × EuclideanSpace ℂ m) :=
  let p₁ := (EuclideanSpace.basisFun n ℂ)
  let p₂ := (EuclideanSpace.basisFun m ℂ)
  let a := λ i : n × m => (((p₁.tensorProduct p₂).repr ((euclideanSpaceTensor' (R := ℂ)).symm x)) i • p₁ i.1)
  (λ (i : n × m) => (a i, p₂ i.2))

theorem EuclideanSpace.sum_apply {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]
  {ι : Type*} (s : Finset ι)
  (x : ι → EuclideanSpace 𝕜 n) (j : n) :
  (∑ i ∈ s, x i) j = ∑ i ∈ s, (x i j) :=
Finset.sum_apply _ _ _

theorem Basis.tensorProduct_repr_tmul_apply' {R M N ι κ : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (b : Basis ι R M)
  (c : Basis κ R N) (m : M) (n : N) (i : ι × κ) :
  ((b.tensorProduct c).repr (m ⊗ₜ[R] n)) i = (c.repr n) i.2 * (b.repr m) i.1 :=
Basis.tensorProduct_repr_tmul_apply _ _ _ _ _ _

-- theorem PiLp.ext_iff {p : ENNReal} {ι : Type*} {α : ι → Type*} {x : PiLp p α}
--   {y : PiLp p α} :
--   x = y ↔ (∀ (i : ι), x i = y i) :=
-- by simp [← funext_iff]

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
theorem EuclideanSpace.prod_choose_spec {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  x = ∑ s : n × m, euclideanSpaceTensor' (R:=ℂ) ((x.prod_choose s).1 ⊗ₜ (x.prod_choose s).2) :=
by
  have := TensorProduct.of_basis_eq_span ((euclideanSpaceTensor' (R := ℂ)).symm x) (EuclideanSpace.basisFun n ℂ).toBasis (EuclideanSpace.basisFun m ℂ).toBasis
  apply_fun (euclideanSpaceTensor' (R := ℂ)).symm using LinearIsometryEquiv.injective _
  simp only [map_sum, LinearIsometryEquiv.symm_apply_apply]
  rw [this, ← Finset.sum_product']
  simp only [Finset.univ_product_univ, ← TensorProduct.tmul_smul]
  simp only [← TensorProduct.smul_tmul]
  let p₁ := (EuclideanSpace.basisFun n ℂ).toBasis
  let p₂ := (EuclideanSpace.basisFun m ℂ).toBasis
  let a := λ i : n × m => (((p₁.tensorProduct p₂).repr ((euclideanSpaceTensor' (R := ℂ)).symm x)) i • p₁ i.1)
  have ha : ∀ i, a i = (((p₁.tensorProduct p₂).repr ((euclideanSpaceTensor' (R := ℂ)).symm x)) i • p₁ i.1) := λ i => rfl
  simp only [p₁, p₂, ← ha]
  rfl

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
theorem QuantumGraph.Real.PiMat_eq {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) :
  let S : (i : ι × ι) →
    (j : (Fin (Module.finrank ℂ (hA.PiMat_submodule i))))
      → (((p i.1) × (p i.2)) → (((EuclideanSpace ℂ (p i.1)) × (EuclideanSpace ℂ (p i.2)))))
    := λ i j => (hA.PiMat_orthonormalBasis i j : EuclideanSpace ℂ _).prod_choose
  A = ∑ i : ι × ι, ∑ j, ∑ s : (p i.1 × p i.2), ∑ l : (p i.1 × p i.2),
    --  in S i j, ∑ p in S i j,
    rankOne ℂ (Matrix.includeBlock
      (Matrix.vecMulVec (S i j s).1 (star (S i j l).1)))
      (modAut (- (1 / 2)) (Matrix.includeBlock
        ((Matrix.vecMulVec (S i j s).2 (star (S i j l).2))ᴴᵀ))) :=
by
  intro S
  have hS : ∀ (i : ι × ι) j, (hA.PiMat_orthonormalBasis i j)
     = ∑ t, euclideanSpaceTensor' (R:=ℂ) ((S i j t).1 ⊗ₜ[ℂ] (S i j t).2) :=
  λ i j => EuclideanSpace.prod_choose_spec _
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
  simp only [starAlgebra.modAut_zero, Matrix.conjTranspose_replicateCol, AlgEquiv.one_apply, one_div,
    starAlgebra.modAut_star, Finset.sum_apply, StarAlgEquiv.piCongrRight_apply,
    PiMatTensorProductEquiv_apply, StarAlgEquiv.ofAlgEquiv_coe, AlgEquiv.ofLinearEquiv_apply,
    Fintype.sum_prod_type, map_sum, directSumTensorToFun_apply,
    PiMat.transposeStarAlgEquiv_symm_apply,
    MulOpposite.unop_op]
  simp only [TensorProduct.toKronecker_apply, Matrix.toEuclideanLin_apply']
  simp only [QuantumSet.modAut_apply_modAut, add_neg_cancel, starAlgebra.modAut_zero]
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
  simp only [Finset.sum_product_univ, Finset.univ_product_univ]
  rfl

section deltaForm
variable {d : ℂ} [Nonempty ι] [hφ₂ : Fact (∀ i, (φ i).matrix⁻¹.trace = d)]
  [Π i, Nontrivial (p i)]

theorem QuantumGraph.trivialGraph :
  QuantumGraph _ (Qam.trivialGraph (PiMat ℂ ι p)) :=
⟨Qam.Nontracial.TrivialGraph.qam⟩

omit [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [∀ (i : ι), Nontrivial (p i)] in
theorem PiMat.piAlgEquiv_trace_apply
  (f : (i : ι) → (Matrix (p i) (p i) ℂ ≃ₐ[ℂ] Matrix (p i) (p i) ℂ))
  (x : PiMat ℂ ι p) (a : ι) :
  ((AlgEquiv.piCongrRight f x) a).trace = (x a).trace :=
by
  calc (((AlgEquiv.piCongrRight f) x) a).trace
      = ((f a) (x a)).trace := rfl
    _ = (x a).trace := AlgEquiv.apply_matrix_trace _ _
omit [DecidableEq ι]
  [Nonempty ι] [∀ (i : ι), Nontrivial (p i)] in
theorem PiMat.modAut_trace_apply (r : ℝ) (x : PiMat ℂ ι p) (a : ι) :
  (modAut r x a).trace = (x a).trace :=
PiMat.piAlgEquiv_trace_apply _ _ _

omit [Nonempty ι] [∀ (i : ι), Nontrivial (p i)] in
theorem PiMat.orthonormalBasis_trace (a : n (PiMat ℂ ι p)) (i : ι) :
  (QuantumSet.onb (A := (PiMat ℂ ι p)) a i).trace =
    if a.1 = i then (hφ a.1).matrixIsPosDef.rpow (-(1 / 2)) a.2.2 a.2.1 else 0 :=
by
  calc (QuantumSet.onb (A := (PiMat ℂ ι p)) a i).trace
      = ∑ j, QuantumSet.onb (A := PiMat ℂ ι p) a i j j := rfl
    _ = ∑ j, (Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hφ) a i j j := rfl
    _ = ∑ j, Matrix.includeBlock (Matrix.single a.2.1 a.2.2 1
      * (hφ a.1).matrixIsPosDef.rpow (-(1 / 2))) i j j
      := by simp only [Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis_apply]
    _ = if a.1 = i then (hφ a.1).matrixIsPosDef.rpow (-(1 / 2)) a.2.2 a.2.1 else 0 :=
      by
        split
        next h =>
          subst h
          simp only [Matrix.includeBlock_apply, dif_pos]
          simp only [one_div, eq_mp_eq_cast, cast_eq]
          simp only [← Matrix.trace_iff, Matrix.single_hMul_trace]
        next h =>
          simp_all only [one_div, Matrix.includeBlock_apply, h, dif_neg]
          simp only [↓reduceDIte, Matrix.zero_apply, Finset.sum_const_zero]

open QuantumSet in
set_option synthInstance.maxHeartbeats 0 in
theorem QuantumGraph.trivialGraph_dim_of_piMat_submodule :
  (QuantumGraph.trivialGraph : QuantumGraph _ (Qam.trivialGraph (PiMat ℂ ι p))).dim_of_piMat_submodule
    = Fintype.card ι :=
by
  rw [← Nat.cast_inj (R := ℂ)]
  rw [QuantumGraph.dim_of_piMat_submodule_eq_trace, Qam.trivialGraph_eq]
  simp_rw [map_smul]
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm (QuantumSet.onb)]
  simp only [map_sum, Psi_apply, Psi_toFun_apply, StarAlgEquiv.lTensor_tmul,
    ]
  simp only [starAlgebra.modAut_zero, AlgEquiv.one_apply, one_div, starAlgebra.modAut_star,
    LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, Matrix.traceLinearMap_apply,
    smul_eq_mul]
  simp only [Matrix.blockDiagonal'AlgHom_apply, Matrix.trace_blockDiagonal']
  simp only [PiMatTensorProductEquiv_tmul, Matrix.trace_kronecker,
    PiMat.transposeStarAlgEquiv_symm_apply, MulOpposite.unop_op]
  simp only [Matrix.trace_transpose (R:=ℂ), AlgEquiv.apply_matrix_trace,
    PiMat.orthonormalBasis_trace, PiMat.modAut_trace_apply]
  simp only [Pi.star_apply, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,
    PiMat.orthonormalBasis_trace]
  simp only [ite_mul, zero_mul, star_ite, star_zero, star_one, mul_ite, mul_zero]
  simp only [Finset.sum_product_univ, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Matrix.conjTranspose_apply, (Matrix.PosDef.rpow.isPosDef _ _).1.eq]
  simp only [QuantumSet.n, Finset.sum_sigma_univ, Finset.sum_product_univ]
  calc
    (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
      ∑ x, ∑ x_1, ∑ x_2, (hφ x).matrixIsPosDef.rpow (-(1 / 2)) x_2 x_1
        * (hφ x).matrixIsPosDef.rpow (-(1 / 2)) x_1 x_2
    = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
      ∑ x, ∑ x_1, ∑ x_2, (hφ x).matrixIsPosDef.rpow (-(1 / 2)) x_1 x_2
        * (hφ x).matrixIsPosDef.rpow (-(1 / 2)) x_2 x_1 := by simp only [mul_comm]
  _ = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
      ∑ x, ∑ x_1, ((hφ x).matrixIsPosDef.rpow (-(1 / 2)) * (hφ x).matrixIsPosDef.rpow (-(1 / 2))) x_1 x_1 := by simp only [← Matrix.mul_apply]
  _ = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
        ∑ x, (φ x).matrix⁻¹.trace := by
      simp only [Matrix.PosDef.rpow_mul_rpow, Matrix.trace_iff]
      ring_nf
      simp only [Matrix.PosDef.rpow_neg_one_eq_inv_self]
  _ = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
    ∑ _ : ι, (QuantumSetDeltaForm.delta (PiMat ℂ ι p)) := by simp only [hφ₂.out]; rfl
  _ = Fintype.card ι := by
    rw [Finset.sum_const, mul_smul_comm, inv_mul_cancel₀ (ne_of_gt QuantumSetDeltaForm.delta_pos)]
    rw [nsmul_eq_mul, mul_one]
    rfl

end deltaForm

theorem StarAlgEquiv.piCongrRight_symm {R ι : Type*} {A₁ A₂ : ι → Type*}
  [(i : ι) → Add (A₁ i)] [(i : ι) → Add (A₂ i)] [(i : ι) → Mul (A₁ i)] [(i : ι) → Mul (A₂ i)]
  [(i : ι) → Star (A₁ i)] [(i : ι) → Star (A₂ i)] [(i : ι) → SMul R (A₁ i)] [(i : ι) → SMul R (A₂ i)]
  (e : (i : ι) → A₁ i ≃⋆ₐ[R] A₂ i) :
  (StarAlgEquiv.piCongrRight e).symm = StarAlgEquiv.piCongrRight (λ i => (e i).symm) :=
rfl

theorem Matrix.k {n : Type*} [Fintype n] [DecidableEq n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} [φ.IsFaithfulPosMap] :
  k (Matrix n n ℂ) = 0 :=
rfl

theorem unitary.mul_inv_eq_iff {A : Type*} [Monoid A] [StarMul A] (U : ↥(unitary A))
    (x : A) (y : A) : x * (U⁻¹ : unitary A) = y ↔ x = y * U :=
  by
    rw [unitary.inj_hMul (U : unitary A), mul_assoc]
    rw [← unitary.star_eq_inv]
    simp only [coe_star, SetLike.coe_mem, star_mul_self_of_mem, mul_one]

noncomputable abbrev piInnerAut (U : (i : ι) → Matrix.unitaryGroup (p i) ℂ) :
  PiMat ℂ ι p ≃⋆ₐ[ℂ] PiMat ℂ ι p :=
(StarAlgEquiv.piCongrRight (λ i => Matrix.innerAutStarAlg (U i)))

omit hφ in
theorem piInnerAut_apply_dualMatrix_iff' {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} :
  piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ ↔
  ∀ i, Matrix.innerAutStarAlg (U i) (φ i).matrix = (φ i).matrix :=
by
  simp only [funext_iff, StarAlgEquiv.piCongrRight_apply,
    Module.Dual.pi.matrixBlock_apply]

omit hφ in
theorem piInnerAut_apply_dualMatrix_iff {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} :
  piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ ↔
    ∀ (a : ι), (U a) * (φ a).matrix = (φ a).matrix * (U a) :=
by
  simp only [piInnerAut_apply_dualMatrix_iff', Matrix.innerAutStarAlg_apply']
  simp_rw [unitary.mul_inv_eq_iff]

example
  {f : PiMat ℂ ι p ≃⋆ₐ[ℂ] PiMat ℂ ι p} :
  @Isometry (PiMat ℂ ι p) (PiMat ℂ ι p)
      (@EMetricSpace.toPseudoEMetricSpace (PiMat ℂ ι p)
        (@MetricSpace.toEMetricSpace (PiMat ℂ ι p) InnerProductAlgebra.toMetricSpace))
      (@EMetricSpace.toPseudoEMetricSpace (PiMat ℂ ι p)
        (@MetricSpace.toEMetricSpace (PiMat ℂ ι p) InnerProductAlgebra.toMetricSpace))
      f ↔
    LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap
  :=
QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm

theorem innerAutStarAlg_adjoint_eq_symm_of {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ}
  (hU : piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ) :
  LinearMap.adjoint (piInnerAut U).toLinearMap = (piInnerAut U).symm.toLinearMap :=
by
  apply LinearMap.ext
  intro
  apply ext_inner_left ℂ
  intro
  simp only [LinearMap.adjoint_inner_right, StarAlgEquiv.toLinearMap_apply]
  simp only [PiLp.inner_apply (𝕜 := ℂ), StarAlgEquiv.piCongrRight_apply (R := ℂ),
    StarAlgEquiv.piCongrRight_symm, Matrix.innerAutStarAlg_apply,
    Matrix.innerAutStarAlg_symm_apply]
  congr
  ext i
  rw [mul_assoc, QuantumSet.inner_star_left, Matrix.k, neg_zero, starAlgebra.modAut_zero,
    AlgEquiv.one_apply, QuantumSet.inner_conj_left, Matrix.k, neg_zero, zero_sub,
    ← Matrix.unitaryGroup.star_coe_eq_coe_star, star_star]
  rw [piInnerAut_apply_dualMatrix_iff] at hU
  simp_rw [modAut, sig_apply, neg_neg, Matrix.PosDef.rpow_one_eq_self,
    Matrix.PosDef.rpow_neg_one_eq_inv_self, ← hU]
  letI := (hφ i).matrixIsPosDef.invertible
  rw [Matrix.mul_inv_cancel_right_of_invertible]

def QuantumGraph.Real.piMat_conj_unitary
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real (PiMat ℂ ι p) A)
  {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ}
  (hU : piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ) :
  QuantumGraph.Real _ ((piInnerAut U).toLinearMap ∘ₗ A ∘ₗ LinearMap.adjoint (piInnerAut U).toLinearMap) :=
QuantumGraph.Real_conj_starAlgEquiv hA
  (QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm.mpr
    (innerAutStarAlg_adjoint_eq_symm_of hU))

noncomputable abbrev Matrix.UnitaryGroup.toEuclideanLinearEquiv {n : Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) :
    EuclideanSpace ℂ n ≃ₗ[ℂ] EuclideanSpace ℂ n :=
Matrix.UnitaryGroup.toLinearEquiv A
theorem Matrix.UnitaryGroup.toEuclideanLinearEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) (v : EuclideanSpace ℂ n) :
  (Matrix.UnitaryGroup.toEuclideanLinearEquiv A) v = (A : Matrix n n ℂ) *ᵥ v :=
rfl

noncomputable def Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv {n : Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) :
    EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n where
  toLinearEquiv := Matrix.UnitaryGroup.toEuclideanLinearEquiv A
  norm_map' x := by
    rw [toEuclideanLinearEquiv_apply]
    calc ‖((EuclideanSpace.equiv n ℂ).symm ((A : Matrix n n ℂ) *ᵥ x) : EuclideanSpace ℂ n)‖
        = √ (RCLike.re ((star ((A : Matrix n n ℂ) *ᵥ x)) ⬝ᵥ ((A : Matrix n n ℂ) *ᵥ x))) := ?_
      _ = √ (RCLike.re ((star x) ⬝ᵥ (((star (A : Matrix n n ℂ) * (A : Matrix n n ℂ)) *ᵥ x)))) := ?_
      _ = ‖x‖ := ?_
    . rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), dotProduct_eq_inner]
      rfl
    . rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
      rfl
    . rw [star_mul_self, one_mulVec, norm_eq_sqrt_re_inner (𝕜 := ℂ), dotProduct_eq_inner]
      rfl

theorem Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) (x : EuclideanSpace ℂ n) :
  (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv A) x = (A : Matrix n n ℂ) *ᵥ x :=
rfl
theorem Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_symm_apply {n : Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) (x : EuclideanSpace ℂ n) :
  (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv A).symm x = ((A⁻¹ : unitaryGroup n ℂ) : Matrix n n ℂ) *ᵥ x :=
rfl
theorem Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_apply' {n : Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) (x : EuclideanSpace ℂ n) :
  (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv A).symm x = (A : Matrix n n ℂ)ᴴ *ᵥ x :=
rfl

noncomputable abbrev unitaryTensorEuclidean (U : (i : ι) → Matrix.unitaryGroup (p i) ℂ) (i : ι × ι) :=
(euclideanSpaceTensor'.symm.trans
    ((LinearIsometryEquiv.TensorProduct.map (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv (U i.1))
      (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv (Matrix.unitaryGroup.conj (U i.2)))).trans
    euclideanSpaceTensor'))

omit [Fintype ι] [DecidableEq ι] in
theorem unitaryTensorEuclidean_apply {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} (i : ι × ι) (x : EuclideanSpace ℂ (p i.1)) (y : EuclideanSpace ℂ (p i.2)) :
  (unitaryTensorEuclidean U i) (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ y))
    = euclideanSpaceTensor' (R := ℂ)
      (((U i.1 : Matrix _ _ ℂ) *ᵥ x) ⊗ₜ ((U i.2 : Matrix _ _ ℂ)ᴴᵀ *ᵥ y)) :=
by
  rw [unitaryTensorEuclidean, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem unitaryTensorEuclidean_apply' {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} (i : ι × ι) (x : EuclideanSpace ℂ (p i.1 × p i.2)) :
  (unitaryTensorEuclidean U i) x
    = ∑ j : p i.1 × p i.2, euclideanSpaceTensor' (R := ℂ)
      ((((U i.1 : Matrix _ _ ℂ) *ᵥ (x.prod_choose j).1) ⊗ₜ[ℂ] ((U i.2 : Matrix _ _ ℂ)ᴴᵀ *ᵥ (x.prod_choose j).2))) :=
by
  simp only [← unitaryTensorEuclidean_apply]
  rw [← map_sum, ← EuclideanSpace.prod_choose_spec]

omit [Fintype ι] [DecidableEq ι] in
theorem unitaryTensorEuclidean_symm_apply {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} (i : ι × ι) (x : EuclideanSpace ℂ (p i.1)) (y : EuclideanSpace ℂ (p i.2)) :
  (unitaryTensorEuclidean U i).symm (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ y))
    = euclideanSpaceTensor' (R := ℂ)
      (((((U i.1)ᴴ : Matrix _ _ ℂ) *ᵥ x)
        ⊗ₜ (((U i.2)ᵀ : Matrix _ _ ℂ) *ᵥ y))) :=
by
  simp_rw [unitaryTensorEuclidean, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]
  simp only [LinearIsometryEquiv.piLpCongrRight_symm, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.TensorProduct.map_symm_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv,
    PiLp_tensorEquiv_apply,
    EmbeddingLike.apply_eq_iff_eq,
    directSumTensorToFun_apply,
    Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_symm_apply,
    Matrix.UnitaryGroup.inv_apply, Matrix.star_eq_conjTranspose, Matrix.unitaryGroup.conj_coe,
    Matrix.conj_conjTranspose]

theorem QuantumGraph.Real.PiMat_submodule_eq_submodule_iff
  {A B : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real (PiMat ℂ ι p) A)
    (hB : QuantumGraph.Real (PiMat ℂ ι p) B) :
  (∀ i, hA.PiMat_submodule i = hB.PiMat_submodule i)
    ↔
  A = B :=
by
  simp_rw [Submodule.eq_iff_orthogonalProjection_eq, ← ContinuousLinearMap.coe_inj,
    QuantumGraph.Real.PiMat_submoduleOrthogonalProjection]
  simp only [StarAlgEquiv.piCongrRight_apply,
    PiMatTensorProductEquiv_apply, StarAlgEquiv.ofAlgEquiv_coe, AlgEquiv.ofLinearEquiv_apply,
    LinearMap.coe_toContinuousLinearMap, EmbeddingLike.apply_eq_iff_eq,
    ← tensorToKronecker_apply, ← directSumTensor_apply]
  simp only [← funext_iff, EmbeddingLike.apply_eq_iff_eq]

theorem Matrix.kronecker_mulVec_euclideanSpaceTensor' {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] (A : Matrix n n ℂ) (B : Matrix m m ℂ) (x : EuclideanSpace ℂ n)
  (y : EuclideanSpace ℂ m) :
  (A ⊗ₖ B) *ᵥ ((WithLp.equiv 2 _) (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] y)))
    = WithLp.equiv 2 _ (euclideanSpaceTensor' (R := ℂ) ((A *ᵥ x) ⊗ₜ (B *ᵥ y))) :=
by
  ext a
  simp only [Matrix.mulVec, dotProduct, kroneckerMap_apply, WithLp.equiv,
    euclideanSpaceTensor'_apply]

  calc
    ∑ x_1 : n × m,
    A a.1 x_1.1 * B a.2 x_1.2 * (Equiv.refl (WithLp 2 (n × m → ℂ))) (euclideanSpaceTensor' (R:=ℂ) (x ⊗ₜ[ℂ] y)) x_1
      = ∑ x_1, A a.1 x_1.1 * B a.2 x_1.2 * ((euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] y)) x_1) := rfl
    _ = ∑ x_1 : n × m, A a.1 x_1.1 * B a.2 x_1.2 * (x x_1.1 * y x_1.2) := by simp only [euclideanSpaceTensor'_apply]
    _ = (euclideanSpaceTensor' (R := ℂ) ((A *ᵥ x) ⊗ₜ[ℂ] (B *ᵥ y))) a := ?_
    _ = (Equiv.refl (WithLp 2 (n × m → ℂ))) (euclideanSpaceTensor' (R := ℂ) ((A *ᵥ x) ⊗ₜ[ℂ] (B *ᵥ y))) a := rfl
  rw [euclideanSpaceTensor'_apply]
  simp_rw [mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, Finset.sum_product_univ, mul_assoc]
  congr; ext; congr; ext
  ring_nf

theorem StarAlgEquiv.piCongrRight_apply_includeBlock {ι : Type*}
  {p : ι → Type*} [∀ i, Fintype (p i)] [DecidableEq ι]
  (f : Π i, Matrix (p i) (p i) ℂ ≃⋆ₐ[ℂ] Matrix (p i) (p i) ℂ)
  (i : ι) (x : Matrix (p i) (p i) ℂ) :
  (StarAlgEquiv.piCongrRight (λ a => f a)) (Matrix.includeBlock x)
    = Matrix.includeBlock ((f i) x) :=
by
  ext
  simp only [piCongrRight_apply, Matrix.includeBlock_apply]
  aesop

theorem Matrix.mul_vecMulVec {n m R : Type*} [Fintype m] [Semiring R]
  (A : Matrix n m R) (x : m → R) (y : n → R) :
  A * (vecMulVec x y) = vecMulVec (A *ᵥ x) y :=
by
  ext
  simp only [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem Matrix.vecMulVec_mul {n m R : Type*} [Fintype n] [CommSemiring R]
  (x : m → R) (y : n → R) (A : Matrix n m R) :
  (vecMulVec x y) * A = vecMulVec x (Aᵀ *ᵥ y) :=
by
  ext
  simp only [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc,
    Matrix.transpose_apply]
  simp_rw [mul_comm]

theorem Matrix.innerAutStarAlg_apply_vecMulVec {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec x y) = vecMulVec (U *ᵥ x) (Uᴴᵀ *ᵥ y) :=
by
  simp only [innerAutStarAlg_apply, unitary.coe_star, mul_vecMulVec, vecMulVec_mul,
    star_eq_conjTranspose]
  rfl
theorem Matrix.innerAutStarAlg_apply_vecMulVec_star {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec x (star y))
    = vecMulVec (U *ᵥ x) (star (U *ᵥ y)) :=
by
  simp only [innerAutStarAlg_apply, unitary.coe_star, mul_vecMulVec, vecMulVec_mul,
    star_eq_conjTranspose, star_mulVec, conj]
  simp_rw [← vecMul_transpose]
  rfl
theorem Matrix.innerAutStarAlg_apply_star_vecMulVec {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec (star x) y)
    = (vecMulVec (Uᴴᵀ *ᵥ x) (star (Uᴴᵀ *ᵥ y)))ᴴᵀ :=
by
  rw [innerAutStarAlg_apply_vecMulVec, vecMulVec_conj, star_star, star_mulVec]
  rw [← vecMul_transpose, conj_conjTranspose]

theorem Matrix.PosSemidef.eq_iff_sq_eq_sq {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
  [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) {B : Matrix n n 𝕜}
  (hB : B.PosSemidef) :
    A ^ 2 = B ^ 2 ↔ A = B :=
⟨λ h => hA.eq_of_sq_eq_sq hB h, λ h => by rw [h]⟩

omit [Fintype ι] [DecidableEq ι] in
theorem innerAutStarAlg_apply_dualMatrix_eq_iff_eq_sqrt {i : ι}
  (U : Matrix.unitaryGroup (p i) ℂ) :
  (Matrix.innerAutStarAlg U) (φ i).matrix = (φ i).matrix
    ↔ (Matrix.innerAutStarAlg U) ((hφ i).matrixIsPosDef.rpow (1 / 2))
      = (hφ i).matrixIsPosDef.rpow (1 / 2) :=
by
  simp_rw [Matrix.innerAutStarAlg_apply_eq_innerAut_apply]
  rw [← Matrix.PosSemidef.eq_iff_sq_eq_sq (Matrix.PosDef.innerAut
      (Matrix.PosDef.rpow.isPosDef _ _) _).posSemidef
      (Matrix.PosDef.rpow.isPosDef _ _).posSemidef,
    Matrix.innerAut.map_pow]
  simp_rw [pow_two, Matrix.PosDef.rpow_mul_rpow, add_halves, Matrix.PosDef.rpow_one_eq_self]

omit [DecidableEq _] in
theorem PiMat.modAut {r : ℝ} :
  (modAut r : PiMat ℂ ι p ≃ₐ[ℂ] PiMat ℂ ι p) =
    AlgEquiv.piCongrRight (λ _ => modAut r) :=
rfl

theorem Matrix.counit_eq_dual {n : Type*} [Fintype n] [DecidableEq n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} [φ.IsFaithfulPosMap] :
  Coalgebra.counit (R := ℂ) (A := Matrix n n ℂ) = φ :=
by
  ext
  simp only [← Coalgebra.inner_eq_counit']
  rw [@Module.Dual.IsFaithfulPosMap.inner_eq, conjTranspose_one, one_mul]

theorem PiMat.counit_eq_dual :
  (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p)) = Module.Dual.pi φ :=
by
  apply LinearMap.ext
  intro
  simp only [← Coalgebra.inner_eq_counit']
  rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq, star_one, one_mul]

theorem modAut_eq_id_iff (r : ℝ) :
    (modAut r : PiMat ℂ ι p ≃ₐ[ℂ] PiMat ℂ ι p) = 1
      ↔ r = 0 ∨ Module.Dual.IsTracial (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p)) :=
by
  rw [PiMat.counit_eq_dual]
  calc (modAut r : PiMat ℂ ι p ≃ₐ[ℂ] PiMat ℂ ι p) = 1
      ↔ ∀ i, (modAut r : Mat ℂ (p i) ≃ₐ[ℂ] Mat ℂ (p i)) = 1 :=
      by
        simp [PiMat.modAut, AlgEquiv.ext_iff, funext_iff]
        refine ⟨λ h i a => ?_, λ h a i => h i (a i)⟩
        simpa only [Matrix.includeBlock_apply_same] using h (Matrix.includeBlock a) i
    _ ↔ ∀ i, sig (hφ i) r = 1 := by simp only [modAut]
  simp_rw [sig_eq_id_iff, forall_or_left, Module.Dual.pi_isTracial_iff]

theorem unitary.mul_inj {A : Type*} [Monoid A] [StarMul A] (U : ↥(unitary A)) (x y : A) :
  ↑U * x = ↑U * y ↔ x = y :=
by
  rw [← unitary.val_toUnits_apply]
  exact (Units.mul_right_inj (toUnits U))

omit [DecidableEq _] in
theorem piInnerAut_modAut_commutes_of {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} {r : ℝ}
  (h : ∀ i, (Matrix.innerAutStarAlg (U i)) ((hφ i).matrixIsPosDef.rpow r)
      = (hφ i).matrixIsPosDef.rpow r) :
  ∀ x, (piInnerAut U) ((modAut (-r)) x) = (modAut (-r)) ((piInnerAut U) x) :=
by
  simp only [funext_iff, Function.comp_apply, piInnerAut,
    Pi.modAut, AlgEquiv.Pi_apply,
    StarAlgEquiv.piCongrRight_apply, AlgEquiv.piCongrRight_apply,
    modAut, sig_apply, Matrix.innerAutStarAlg_apply', unitary.mul_inv_eq_iff] at h ⊢
  simp only [mul_assoc, neg_neg]
  simp only [Matrix.PosDef.rpow_neg_eq_inv_rpow, inv_inv]
  simp only [← unitary.star_eq_inv, unitary.coe_star, ← mul_assoc, ← h]
  intro _ i
  letI := (Matrix.PosDef.rpow.isPosDef (hφ i).matrixIsPosDef r).invertible
  simp only [mul_assoc, unitary.mul_inj, Matrix.mul_right_inj_of_invertible]
  rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  simp only [mul_assoc, h]
  simp only [Matrix.inv_mul_cancel_left_of_invertible, unitary.coe_star_mul_self, mul_one]

theorem QuantumGraph.Real.PiMat_applyConjInnerAut
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real (PiMat ℂ ι p) A)
  {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ}
  (hU : piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ) :
  let S : (i : ι × ι) →
    (j : (Fin (Module.finrank ℂ (hA.PiMat_submodule i))))
      → (((p i.1) × (p i.2)) → (((EuclideanSpace ℂ (p i.1)) × (EuclideanSpace ℂ (p i.2)))))
    := λ i j => (hA.PiMat_orthonormalBasis i j : EuclideanSpace ℂ _).prod_choose
  (piInnerAut U).toLinearMap ∘ₗ A ∘ₗ LinearMap.adjoint (piInnerAut U).toLinearMap
    = ∑ i : ι × ι, ∑ j, ∑ s : (p i.1 × p i.2), ∑ l : (p i.1 × p i.2),
    rankOne ℂ (Matrix.includeBlock
      (Matrix.vecMulVec ((U i.1 : Matrix (p i.1) (p i.1) ℂ) *ᵥ (S i j s).1)
        (star ((U i.1 : Matrix (p i.1) (p i.1) ℂ) *ᵥ (S i j l).1))))
      (modAut (- (1 / 2)) (Matrix.includeBlock
        ((Matrix.vecMulVec ((U i.2 : Matrix (p i.2) (p i.2) ℂ)ᴴᵀ *ᵥ (S i j s).2)
          (star ((U i.2 : Matrix (p i.2) (p i.2) ℂ)ᴴᵀ *ᵥ (S i j l).2)))ᴴᵀ)))
     :=
by
  intro S
  simp_rw [piInnerAut_apply_dualMatrix_iff', innerAutStarAlg_apply_dualMatrix_eq_iff_eq_sqrt] at hU
  have hU₂ := piInnerAut_modAut_commutes_of hU
  nth_rw 1 [QuantumGraph.Real.PiMat_eq hA]
  simp only [piInnerAut] at hU₂ ⊢
  simp only [ContinuousLinearMap.coe_sum, LinearMap.sum_comp, LinearMap.comp_sum,
    LinearMap.rankOne_comp', LinearMap.comp_rankOne, StarAlgEquiv.toLinearMap_apply, hU₂]
  repeat apply Finset.sum_congr rfl; intro _ _
  congr 2
  . rw [StarAlgEquiv.piCongrRight_apply_includeBlock, Matrix.innerAutStarAlg_apply_vecMulVec_star]
  . rw [StarAlgEquiv.piCongrRight_apply_includeBlock, Matrix.vecMulVec_conj, star_star,
    Matrix.innerAutStarAlg_apply_star_vecMulVec]

open QuantumSet in
set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000 in
theorem QuantumGraph.Real.PiMat_conj_unitary_submodule_eq_map
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real (PiMat ℂ ι p) A)
  {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ}
  (hU : piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ) (i : ι × ι) :
  QuantumGraph.Real.PiMat_submodule (hA.piMat_conj_unitary hU) i
    = Submodule.map (unitaryTensorEuclidean U i) (hA.PiMat_submodule i)
     :=
by
  rw [Submodule.eq_iff_orthogonalProjection_eq, ← ContinuousLinearMap.coe_inj]
  rw [orthogonalProjection_submoduleMap]
  nth_rw 1 [OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne (hA.PiMat_orthonormalBasis i)]
  simp_rw [QuantumGraph.Real.PiMat_submoduleOrthogonalProjection]
  rw [QuantumGraph.Real.PiMat_applyConjInnerAut hA hU]
  simp only [ContinuousLinearMap.coe_sum, map_sum, Psi_apply, Psi_toFun_apply,
    Finset.sum_apply, StarAlgEquiv.lTensor_tmul, PiMatTensorProductEquiv_tmul,
    TensorProduct.map_tmul, PiMat_toEuclideanLM, StarAlgEquiv.piCongrRight_apply]
  simp only [LinearMap.sum_comp, LinearMap.comp_sum]
  simp only [modAut_apply_modAut, add_neg_cancel, starAlgebra.modAut_zero, AlgEquiv.one_apply,
    PiMat.transposeStarAlgEquiv_symm_apply, MulOpposite.unop_op]
  simp only [LinearMap.comp_rankOne, LinearMap.rankOne_comp, LinearIsometryEquiv.linearMap_adjoint,
    LinearIsometryEquiv.symm_symm]
  simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_toLinearMap,
    LinearMap.coe_toContinuousLinearMap, unitaryTensorEuclidean_apply', EuclideanSpaceTensor_apply_eq_reshape_vecMulVec]
  simp only [Matrix.reshape_aux_star, Matrix.includeBlock_apply, Matrix.dite_kronecker, Pi.star_apply,
    star_dite, star_zero, apply_dite, Matrix.kronecker_dite, Matrix.transpose_zero,
    map_zero, Matrix.kronecker_zero]
  simp only [Finset.sum_dite_irrel, Finset.sum_const_zero, Finset.sum_product_univ,
    Finset.sum_dite_eq', Finset.sum_dite_eq, Finset.mem_univ, if_true]
  simp only [
    eq_mp_eq_cast, cast_eq,
    Matrix.star_eq_conjTranspose, Matrix.conj_conjTranspose, Matrix.transpose_conj_eq_conjTranspose,
    Matrix.transpose_transpose, Matrix.vecMulVec_kronecker_vecMulVec,
    Matrix.toEuclideanStarAlgEquiv_coe, Matrix.vecMulVec_toEuclideanLin]
  congr
  ext
  nth_rw 3 [← Finset.sum_product']
  nth_rw 2 [← Finset.sum_product']
  simp only [Finset.univ_product_univ, rankOne_lm_sum_sum]
  simp only [Finset.sum_product_univ, Matrix.reshape_aux_star (R := ℂ),
    Matrix.vecMulVec_conj, star_star]

theorem orthogonalProjection'_bot {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] :
  orthogonalProjection' (⊥ : Submodule 𝕜 E) = 0 :=
by simp

omit [Fintype ι] [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)] in
lemma LinearMap.proj_apply_includeBlock
  (i j : ι) (x : Matrix (p j) (p j) ℂ) :
  LinearMap.proj (R := ℂ) i (Matrix.includeBlock (i := j) x) =
    if h : j = i then by rw [← h]; exact x else 0 :=
by simp [Matrix.includeBlock_apply]

lemma _root_.PiMat.modAut_includeBlock
  (r : ℝ) (j : ι) (x : Matrix (p j) (p j) ℂ) :
  (modAut r) (Matrix.includeBlock x)
    = Matrix.includeBlock (modAut r x) :=
by
  simp only [PiMat.modAut]
  ext
  simp only [AlgEquiv.piCongrRight_apply,
    modAut, sig_apply, Matrix.includeBlock_apply, mul_dite, mul_zero,
    dite_mul, zero_mul]
  aesop

omit [DecidableEq ι] in
lemma _root_.PiMat.modAut_proj
  (r : ℝ) (j : ι) (x : PiMat ℂ ι p) :
  (modAut r) (LinearMap.proj (R := ℂ) j x)
    = LinearMap.proj (R := ℂ) j (modAut r x) :=
by
  simp only [PiMat.modAut]
  ext
  simp only [AlgEquiv.piCongrRight_apply,
    modAut, sig_apply, Matrix.includeBlock_apply, mul_dite, mul_zero,
    dite_mul, zero_mul]
  aesop

lemma EuclideanSpace.prod_choose_zero_fst
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  (i : n × m) :
  ((0 : EuclideanSpace ℂ (n × m)).prod_choose i).1 = 0 :=
by
  simp only [Pi.zero_apply, Prod.fst_zero, PiLp.zero_apply,
    prod_choose, LinearIsometryEquiv.map_zero, zero_smul]

lemma
  Matrix.vecMulVec_zero {m n α : Type*} [MulZeroClass α] (w : m → α) :
  vecMulVec w (0 : n → α) = 0 :=
by
  ext
  simp only [zero_apply, vecMulVec_apply, Pi.zero_apply, mul_zero]
lemma
  Matrix.zero_vecMulVec {m n α : Type*} [MulZeroClass α] (w : n → α) :
  vecMulVec (0 : m → α) w = 0 :=
by
  ext
  simp only [zero_apply, vecMulVec_apply, Pi.zero_apply, zero_mul]

open scoped Kronecker

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 400000 in
theorem QuantumGraph.Real.PiMat_submodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real _ A)
  {i : ι × ι} :
  hA.PiMat_submodule i = ⊥ ↔
    LinearMap.proj i.1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i.2) = 0 :=
by
  rw [Submodule.eq_iff_orthogonalProjection_eq, orthogonalProjection'_bot,
    QuantumGraph.Real.PiMat_submoduleOrthogonalProjection]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp only [map_sum, Finset.sum_apply, QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply,
    StarAlgEquiv.lTensor_tmul, PiMatTensorProductEquiv_tmul, PiMat_toEuclideanLM, StarAlgEquiv.piCongrRight_apply]
  rw [← map_sum, LinearEquiv.map_eq_zero_iff,
    ← map_sum, StarAlgEquiv.map_eq_zero_iff]
  simp only [PiMat.transposeStarAlgEquiv_symm_apply, MulOpposite.unop_op]
  rw [← Function.Injective.eq_iff (QuantumSet.Psi 0 (1/2)).injective,
    ← Function.Injective.eq_iff (AlgEquiv.lTensor _ (Matrix.transposeAlgEquiv _ _ _).symm).injective,
    ← Function.Injective.eq_iff tensorToKronecker.injective]
  simp only [LinearMap.sum_comp, LinearMap.comp_sum,
    LinearMap.rankOne_comp', LinearMap.comp_rankOne, map_sum,
    QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply, AlgEquiv.lTensor_tmul,
    Matrix.transposeAlgEquiv_symm_op_apply, PiMat.modAut_proj,
    tensorToKronecker_apply, TensorProduct.toKronecker_apply, map_zero]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 400000 in
theorem QuantumGraph.Real.PiMat_submodule_eq_top_iff_proj_comp_adjoint_proj_eq_rankOne_one_one
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real _ A) {i : ι × ι} :
  hA.PiMat_submodule i = ⊤ ↔
    LinearMap.proj i.1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i.2)
      = (rankOne ℂ (1 : Mat ℂ (p i.1)) (1 : Mat ℂ (p i.2))) :=
by
  rw [Submodule.eq_iff_orthogonalProjection_eq, orthogonalProjection_of_top,
    QuantumGraph.Real.PiMat_submoduleOrthogonalProjection]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp only [map_sum, Finset.sum_apply, QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply,
    StarAlgEquiv.lTensor_tmul, PiMatTensorProductEquiv_tmul, PiMat_toEuclideanLM, StarAlgEquiv.piCongrRight_apply]
  rw [← map_sum, ← ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply,
    map_eq_one_iff _ (AlgEquiv.injective _),
    ← map_sum, map_eq_one_iff _ (StarAlgEquiv.injective _)]
  simp only [PiMat.transposeStarAlgEquiv_symm_apply, MulOpposite.unop_op]
  rw [← Function.Injective.eq_iff (QuantumSet.Psi 0 (1/2)).injective,
    ← Function.Injective.eq_iff (AlgEquiv.lTensor _ (Matrix.transposeAlgEquiv _ _ _).symm).injective,
    ← Function.Injective.eq_iff tensorToKronecker.injective]
  simp only [LinearMap.sum_comp, LinearMap.comp_sum,
    LinearMap.rankOne_comp', LinearMap.comp_rankOne, map_sum,
    QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply, AlgEquiv.lTensor_tmul,
    Matrix.transposeAlgEquiv_symm_op_apply, PiMat.modAut_proj,
    tensorToKronecker_apply, TensorProduct.toKronecker_apply, map_one,
    star_one, Matrix.transpose_one, Matrix.one_kronecker_one]
  rfl

theorem Matrix.trace_eq_linearMap_trace
  {n : Type*} [Fintype n] [DecidableEq n]
  (y : Matrix n n ℂ) :
  Matrix.trace y = LinearMap.trace ℂ (EuclideanSpace ℂ n)
    (Matrix.toEuclideanLin y) :=
by
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ n)]
  simp only [Matrix.toEuclideanLin_eq_toLin, LinearMap.toMatrix_toLin]

lemma Matrix.trace_piMatTensorProductEquiv_apply_lTensor_transpose
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {p : ι → Type*} [∀ i, Fintype (p i)] [∀ i, DecidableEq (p i)]
  (x : (PiMat ℂ ι p) ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) (i : ι × ι) :
  Matrix.trace
    (PiMatTensorProductEquiv
      ((StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm) x) i)
    = Matrix.trace (PiMatTensorProductEquiv (LinearMap.lTensor _ (unop ℂ).toLinearMap x) i) :=
by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  simp_rw [hS, map_sum, Finset.sum_apply, Matrix.trace_sum,
    StarAlgEquiv.lTensor_tmul, LinearMap.lTensor_tmul,
    PiMatTensorProductEquiv_tmul, Matrix.trace_kronecker,
    PiMat.transposeStarAlgEquiv_symm_apply]
  rfl

lemma Matrix.trace_piMatTensorProductEquiv_lTensor_unop_map_modAut
  (x : (PiMat ℂ ι p) ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) (i : ι × ι) :
  Matrix.trace
    (PiMatTensorProductEquiv
      (LinearMap.lTensor _ (unop ℂ).toLinearMap
        ((TensorProduct.map (modAut (0 - 1 / 2)).toLinearMap (AlgEquiv.op (modAut (0 - 1 / 2))).toLinearMap) x)) i)
  = Matrix.trace
    (PiMatTensorProductEquiv
      (LinearMap.lTensor _ (unop ℂ).toLinearMap x) i) :=
by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  simp_rw [hS, map_sum, Finset.sum_apply, Matrix.trace_sum,
    TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    PiMatTensorProductEquiv_tmul, Matrix.trace_kronecker,
    AlgEquiv.toLinearMap_apply]
  congr 1
  ext
  rw [AlgEquiv.op_apply_apply, LinearEquiv.coe_coe, unop_apply, MulOpposite.unop_op]
  simp_rw [PiMat.modAut_trace_apply]
  rfl

lemma Matrix.trace_piMatTensorProductEquiv_lTensor_unop_tenSwap
  (x : (PiMat ℂ ι p) ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) (i : ι × ι) :
  (Matrix.trace
      (PiMatTensorProductEquiv
        ((LinearMap.lTensor (PiMat ℂ ι p) (unop ℂ).toLinearMap) ((tenSwap ℂ) x)) i))
  = Matrix.trace (PiMatTensorProductEquiv
        ((LinearMap.lTensor (PiMat ℂ ι p) (unop ℂ).toLinearMap) x) i.swap) :=
by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  rw [← LinearEquiv.coe_toLinearMap]
  simp_rw [hS, map_sum, Finset.sum_apply, Matrix.trace_sum,
    LinearEquiv.coe_coe, tenSwap_apply,
    LinearMap.lTensor_tmul, PiMatTensorProductEquiv_tmul, Matrix.trace_kronecker,
    LinearEquiv.coe_coe, unop_apply]
  congr 1
  ext
  rw [mul_comm]
  rfl

def LinearIsometryEquiv.of_linearEquiv
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (f : E ≃ₗ[𝕜] F) (hf : LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap) :
    E ≃ₗᵢ[𝕜] F where
  toLinearEquiv := f
  norm_map' := by
    rw [← isometry_iff_norm, isometry_iff_inner]
    intro _ _
    rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.adjoint_inner_left]
    simp only [hf, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]

lemma LinearIsometryEquiv.of_linearEquiv_apply {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (f : E ≃ₗ[𝕜] F) (hf : LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap) (x : E) :
  (LinearIsometryEquiv.of_linearEquiv f hf) x = f x :=
rfl

noncomputable def TensorProduct.comm_linearIsometryEquiv
  (𝕜 E F : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] (F ⊗[𝕜] E) :=
LinearIsometryEquiv.of_linearEquiv (TensorProduct.comm 𝕜 E F) TensorProduct.comm_adjoint

lemma TensorProduct.comm_linearIsometryEquiv_apply
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (x : E) (y : F) :
  (TensorProduct.comm_linearIsometryEquiv 𝕜 E F) (x ⊗ₜ y) = y ⊗ₜ x :=
rfl

noncomputable def
  EuclideanSpace.tensor_comm {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :
  EuclideanSpace ℂ (n × m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (m × n) :=
(euclideanSpaceTensor'.symm.trans (TensorProduct.comm_linearIsometryEquiv ℂ _ _)).trans
  (euclideanSpaceTensor')
lemma EuclideanSpace.tensor_comm_apply {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  tensor_comm (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] y))
    = euclideanSpaceTensor' (R := ℂ) (y ⊗ₜ[ℂ] x) :=
by
  simp only [tensor_comm]
  rw [LinearIsometryEquiv.trans_apply]
  nth_rw 2 [LinearIsometryEquiv.trans_apply]
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem QuantumGraph.Real.piMat_submodule_finrank_eq_swap_of_adjoint
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph.Real _ f)
  (hf₂ : LinearMap.adjoint f = f)
  (i : ι × ι) :
  Module.finrank ℂ (hf.PiMat_submodule i)
    = Module.finrank ℂ (hf.PiMat_submodule i.swap) :=
by
  rw [← Nat.cast_inj (R := ℂ)]
  nth_rw 2 [← Complex.conj_natCast]
  simp_rw [← orthogonalProjection_trace,
    QuantumGraph.Real.PiMat_submoduleOrthogonalProjection,
    LinearMap.coe_toContinuousLinearMap,
    PiMat_toEuclideanLM, StarAlgEquiv.piCongrRight_apply,
    Matrix.toEuclideanStarAlgEquiv_coe,
    ← Matrix.trace_eq_linearMap_trace]
  nth_rw 2 [← hf₂]
  rw [Psi.adjoint_apply]
  simp_rw [Matrix.trace_piMatTensorProductEquiv_apply_lTensor_transpose,
    Matrix.trace_piMatTensorProductEquiv_lTensor_unop_map_modAut,
    Matrix.trace_piMatTensorProductEquiv_lTensor_unop_tenSwap,
    ← Matrix.trace_piMatTensorProductEquiv_apply_lTensor_transpose,
    map_star, starRingEnd_apply, Matrix.trace_star, Pi.star_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rfl

theorem QuantumGraph.Real.PiMat_submodule_eq_bot_iff_swap_eq_bot_of_adjoint
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real _ A)
  (hA₂ : LinearMap.adjoint A = A)
  (i : ι × ι) :
  hA.PiMat_submodule i = ⊥
    ↔ hA.PiMat_submodule i.swap = ⊥ :=
by
  simp only [← Submodule.finrank_eq_zero]
  rw [hA.piMat_submodule_finrank_eq_swap_of_adjoint hA₂]

lemma Submodule.finrank_eq_iff_eq_top {K V : Type*} [DivisionRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {S : Submodule K V} :
  Module.finrank K ↥S = Module.finrank K V ↔ S = ⊤ :=
by
  refine ⟨Submodule.eq_top_of_finrank_eq, ?_⟩
  rintro rfl
  simp only [finrank_top]

theorem QuantumGraph.Real.PiMat_submodule_eq_top_iff_swap_eq_top_of_adjoint
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real _ A)
  (hA₂ : LinearMap.adjoint A = A)
  (i : ι × ι) :
  hA.PiMat_submodule i = ⊤
    ↔ hA.PiMat_submodule i.swap = ⊤ :=
by
  simp only [← Submodule.finrank_eq_iff_eq_top]
  rw [hA.piMat_submodule_finrank_eq_swap_of_adjoint hA₂]
  simp only [Prod.fst_swap, Prod.snd_swap, finrank_euclideanSpace, Fintype.card_prod,
    mul_comm]
