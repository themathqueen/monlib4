import Monlib.QuantumGraph.PiMatFinTwo

open scoped Functional MatrixOrder ComplexOrder TensorProduct Matrix

open scoped Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap]

theorem lmul_toMatrix (x : Matrix n n ℂ) :
  onb.toMatrix (lmul x) = x ⊗ₖ (1 : Matrix n n ℂ) :=
by
  simp only [← Matrix.ext_iff, QuantumSet.n]
  intro i j
  simp_rw [OrthonormalBasis.toMatrix_apply, lmul_apply, Matrix.kroneckerMap_apply,
    onb, Module.Dual.IsFaithfulPosMap.inner_coord hφ,
    hφ.orthonormalBasis_apply, mul_assoc, Matrix.PosDef.rpow_mul_rpow,
    neg_add_cancel, Matrix.PosDef.rpow_zero, mul_one, Matrix.mul_apply,
    Matrix.single_eq, Matrix.one_apply, mul_boole, ite_and, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, eq_comm]

theorem rmul_toMatrix (x : Matrix n n ℂ) :
  onb.toMatrix (rmul x) = (1 : Matrix n n ℂ) ⊗ₖ (modAut (1 / 2) x)ᵀ :=
by
  simp only [← Matrix.ext_iff, QuantumSet.n]
  intro i j
  simp_rw [OrthonormalBasis.toMatrix_apply, rmul_apply, Matrix.kroneckerMap_apply,
    onb, Module.Dual.IsFaithfulPosMap.inner_coord hφ,
    hφ.orthonormalBasis_apply, mul_assoc,
    modAut, ← mul_assoc (Matrix.PosDef.rpow _ _), ← sig_apply, Matrix.mul_apply,
    Matrix.single_eq, Matrix.one_apply, boole_mul, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, eq_comm]
  rfl

open Matrix

theorem Matrix.single_transpose {R n p : Type*} [DecidableEq n] [DecidableEq p]
    [Zero R] {i : n} {j : p} {α : R} :
    (single i j α)ᵀ = single j i α :=
by ext; simp_rw [transpose_apply, single, of_apply,  and_comm]

lemma Module.Dual.IsFaithfulPosMap.inner_coord'
  (y : Matrix n n ℂ) (i j : n) :
  inner ℂ (onb (i, j)) y = (y * hφ.matrixIsPosDef.rpow (1 / 2)) i j :=
hφ.inner_coord _ _

abbrev Matrix.transposeStarAlgEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
  Matrix ι ι ℂ ≃⋆ₐ[ℂ] (Matrix ι ι ℂ)ᵐᵒᵖ :=
StarAlgEquiv.ofAlgEquiv (transposeAlgEquiv ι ℂ ℂ) (λ _ => rfl)
theorem Matrix.transposeStarAlgEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
  (x : Matrix ι ι ℂ) :
  Matrix.transposeStarAlgEquiv ι x = MulOpposite.op (xᵀ) :=
rfl
theorem Matrix.transposeStarAlgEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
  (x : (Matrix ι ι ℂ)ᵐᵒᵖ) :
  (Matrix.transposeStarAlgEquiv ι).symm x = x.unopᵀ :=
rfl

set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 350000 in
theorem QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne
  (x y : Matrix n n ℂ) :
  (QuantumSet.Psi 0 (1 / 2)).symm
      ((StarAlgEquiv.lTensor _ (transposeStarAlgEquiv n))
        (kroneckerToTensor
          (onb.toMatrix ((rankOne ℂ x y) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)))) =
    lmul (x * φ.matrix) * (LinearMap.adjoint (rmul (φ.matrix * y))) :=
by
  simp only [← StarAlgEquiv.coe_toAlgEquiv,
    ← orthonormalBasis_toMatrix_eq_basis_toMatrix,
    LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
    rankOne_toMatrix_of_onb, conjTranspose_replicateCol, ← vecMulVec_eq]
  rw [kmul_representation (vecMulVec _ _)]
  simp only [map_sum, _root_.map_smul, kroneckerToTensor, tensorToKronecker_symm_apply,
    kroneckerToTensorProduct_apply, StarAlgEquiv.coe_toAlgEquiv,
    StarAlgEquiv.lTensor_tmul, QuantumSet.Psi_symm_apply,
    QuantumSet.Psi_invFun_apply, vecMulVec_apply, neg_zero, starAlgebra.modAut_zero,
    transposeStarAlgEquiv_apply, MulOpposite.unop_op, AlgEquiv.one_apply]
  simp_rw [← rankOne_lm_smul_smul, Pi.star_apply, star_star,
    single_transpose, star_eq_conjTranspose, single_conjTranspose,
    star_one]
  ext1
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, inner_smul_left, QuantumSet.modAut_isSymmetric,
    Module.End.mul_apply, rmul_adjoint, rmul_apply, lmul_apply,
    OrthonormalBasis.repr_apply_apply, inner_single_left,
    Module.Dual.IsFaithfulPosMap.inner_coord' (hφ := hφ)]
  simp_rw [starRingEnd_apply, smul_smul, mul_assoc,
    ← mul_comm _ ((modAut (-(1/2)) (_ : Matrix n n ℂ) * φ.matrix) _ _),
    ]
  rw [Finset.sum_sum_comm_sum]
  simp only [← Finset.sum_smul, ← Finset.mul_sum, ← mul_apply]
  simp_rw [mul_comm (star _), ← conjTranspose_apply, ← mul_apply, ← smul_single',
    QuantumSet.k, conjTranspose_apply, modAut, sig_apply,
    star_eq_conjTranspose, conjTranspose_mul,
    (PosDef.rpow.isPosDef _ _).1.eq, hφ.matrixIsPosDef.1.eq]
  rw [← matrix_eq_sum_single]
  simp_rw [← mul_assoc]
  nth_rw 1 [mul_assoc _ (PosDef.rpow _ _) (PosDef.rpow _ _)]
  rw [PosDef.rpow_mul_rpow]
  simp only [mul_assoc]
  nth_rw 5 [← mul_assoc]
  nth_rw 3 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw 5 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw 7 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  simp_rw [PosDef.rpow_mul_rpow]
  nth_rw 4 [← mul_assoc]
  rw [PosDef.rpow_mul_rpow]
  ring_nf
  simp only [PosDef.rpow_zero, mul_one]

set_option maxHeartbeats 300000 in
theorem QuantumGraph.Real.matrix_isOrthogonalProjection
  {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hA : QuantumGraph.Real _ A) :
  (ContinuousLinearMap.toLinearMapAlgEquiv.symm
  ((onb.toMatrix.symm (tensorToKronecker
  ((StarAlgEquiv.lTensor _ (transposeStarAlgEquiv n).symm)
    ((QuantumSet.Psi 0 (1 / 2)) A))))
      : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)).IsOrthogonalProjection :=
by
  rw [ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply,
    LinearMap.isOrthogonalProjection_iff]
  rw [IsIdempotentElem, ← _root_.map_mul, ← map_mul tensorToKronecker,
    ← map_mul (StarAlgEquiv.lTensor _ _), ← Psi.schurMul, hA.1]
  refine ⟨rfl, ?_⟩
  rw [isSelfAdjoint_iff, ← map_star]
  simp_rw [tensorToKronecker, AlgEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [TensorProduct.toKronecker_star, ← map_star]
  congr
  simpa [QuantumSet.k] using
    (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp hA).2

noncomputable def QuantumGraph.Real.matrix_submodule
  {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hA : QuantumGraph.Real _ A) :
  Submodule ℂ (Matrix n n ℂ) :=
by
  choose U hU using orthogonal_projection_iff.mpr ((And.comm.mp
    (ContinuousLinearMap.isOrthogonalProjection_iff'.mp
    hA.matrix_isOrthogonalProjection)))
  exact U

lemma QuantumGraph.Real.matrix_orthogonalProjection_eq
  {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hA : QuantumGraph.Real _ A) :
  orthogonalProjection' hA.matrix_submodule =
    ContinuousLinearMap.toLinearMapAlgEquiv.symm ((onb.toMatrix.symm
    (tensorToKronecker
      ((StarAlgEquiv.lTensor (Matrix n n ℂ)
        (transposeStarAlgEquiv n).symm)
        ((QuantumSet.Psi 0 (1 / 2)) A))))) :=
by
  rw [matrix_submodule]
  generalize_proofs
  (expose_names; exact pf_22)
-- QuantumGraph.Real.matrix_submodule.proof_19 hA

theorem StarAlgEquiv.lTensor_symm {R A B C : Type*}
  [RCLike R] [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid C] [StarModule R A]
  [StarModule R B] [StarModule R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
  (f : A ≃⋆ₐ[R] B) :
  (StarAlgEquiv.lTensor C f).symm = StarAlgEquiv.lTensor C f.symm :=
rfl

set_option synthInstance.maxHeartbeats 50000 in
theorem QuantumGraph.Real.matrix_eq_of_orthonormalBasis
  {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hA : QuantumGraph.Real _ A)
  {ι : Type*} [DecidableEq ι] [Fintype ι]
  (u : OrthonormalBasis ι ℂ hA.matrix_submodule) :
  A = ∑ i, lmul (u i * φ.matrix) * (LinearMap.adjoint (rmul (φ.matrix * u i))) :=
by
  simp_rw [← QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne,
    ← map_sum, ← map_sum onb.toMatrix, ← ContinuousLinearMap.coe_sum,
    ← OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne u,
    hA.matrix_orthogonalProjection_eq]
  simp only [ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply]
  simp only [tensorToKronecker_apply, LinearMap.coe_toContinuousLinearMap,
    StarAlgEquiv.apply_symm_apply, kroneckerToTensor, tensorToKronecker]
  simp only [AlgEquiv.symm_mk, AlgEquiv.coe_mk, Equiv.coe_fn_mk,
    TensorProduct.toKronecker_to_tensorProduct, ← StarAlgEquiv.lTensor_symm,
    StarAlgEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

theorem QuantumGraph.Real.matrix_submodule_exists_orthonormalBasis
  {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hA : QuantumGraph.Real _ A) :
  ∃ u : OrthonormalBasis (Fin (Module.finrank ℂ hA.matrix_submodule)) ℂ hA.matrix_submodule,
    A = ∑ i, lmul (u i * φ.matrix) * (LinearMap.adjoint (rmul (φ.matrix * u i))) :=
⟨stdOrthonormalBasis ℂ _, (hA.matrix_eq_of_orthonormalBasis _)⟩

noncomputable abbrev QuantumGraph.Real.of_norm_one_matrix
  (u : { x : Matrix n n ℂ // ‖x‖ = 1 }) :
  Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
lmul (u * φ.matrix) * (LinearMap.adjoint (rmul (φ.matrix * u)))

-- theorem OrthonormalBasis.norm_eq_one
--   {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
--   [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
--   (u : OrthonormalBasis ι 𝕜 E) (i : ι) :
--     ‖u i‖ = 1 :=
-- by
--   rw [@norm_eq_sqrt_inner 𝕜, Real.sqrt_eq_one]
--   simp_rw [orthonormal_iff_ite.mp u.orthonormal, if_true, RCLike.one_re]

theorem orthogonalProjection'_of_finrank_eq_one
  {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] {U : Submodule 𝕜 E} (hU : Module.finrank 𝕜 U = 1) :
  letI : Module.Finite 𝕜 U := Module.finite_of_finrank_eq_succ hU;
  ∃ v : { x : E // ‖x‖ = 1 },
    orthogonalProjection' U = rankOne 𝕜 (v : E) (v : E) :=
by
  letI : Module.Finite 𝕜 U := Module.finite_of_finrank_eq_succ hU
  let u : OrthonormalBasis (Fin 1) 𝕜 U := by
    rw [← hU]; exact stdOrthonormalBasis 𝕜 U
  rw [u.orthogonalProjection'_eq_sum_rankOne, Fin.sum_univ_one]
  refine' ⟨⟨u 0, u.norm_eq_one _⟩, rfl⟩

set_option synthInstance.maxHeartbeats 50000 in
theorem QuantumSet.Psi_apply_matrix_one {n : Type*} [DecidableEq n] [Fintype n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap] :
    QuantumSet.Psi 0 (1 / 2) (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      (StarAlgEquiv.lTensor _ (transposeStarAlgEquiv n))
        (kroneckerToTensor
           (onb.toMatrix ((rankOne ℂ (φ.matrix⁻¹) (φ.matrix⁻¹) : Matrix n n ℂ →ₗ[ℂ] _)))) :=
by
  nth_rw 1 [←
    rankOne.sum_orthonormalBasis_eq_id_lm
      (@Module.Dual.IsFaithfulPosMap.orthonormalBasis n _ _ φ _)]
  simp only [map_sum, QuantumSet.Psi_apply, QuantumSet.Psi_toFun_apply,
    ← StarAlgEquiv.coe_toAlgEquiv,
    ← orthonormalBasis_toMatrix_eq_basis_toMatrix,
    LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
    rankOne_toMatrix_of_onb,
    ]
  simp_rw [StarAlgEquiv.coe_toAlgEquiv, StarAlgEquiv.eq_apply_iff_symm_eq,
    AlgEquiv.eq_apply_iff_symm_eq, map_sum, StarAlgEquiv.lTensor_symm_tmul, kroneckerToTensor_symm_apply,
    TensorProduct.toKronecker_apply, transposeStarAlgEquiv_symm_apply,
    MulOpposite.unop_op, starAlgebra.modAut_zero, AlgEquiv.one_apply,
    conjTranspose_replicateCol, ← vecMulVec_eq]
  have : ∀ x, modAut (1 / 2) (hφ.orthonormalBasis x)
    = (hφ.orthonormalBasis x.swap)ᴴ :=
  by
    intro x
    simp only [modAut, sig_apply, hφ.orthonormalBasis_apply, conjTranspose_mul,
      mul_assoc, PosDef.rpow_mul_rpow, neg_add_cancel, PosDef.rpow_zero,
      mul_one, (PosDef.rpow.isPosDef _ _).1.eq, single_conjTranspose,
      star_one]
    rfl
  simp only [this, star_eq_conjTranspose, conjTranspose_conjTranspose]
  ext
  simp only [sum_apply, kroneckerMap_apply, vecMulVec_apply,
    Pi.star_apply, OrthonormalBasis.repr_apply_apply, transpose_apply,
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, mul_apply,
    single_eq, boole_mul]
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul,
    Prod.swap, mul_ite, mul_zero, Finset.sum_product_univ, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Module.Dual.IsFaithfulPosMap.inner_coord',
    Module.Dual.IsFaithfulPosMap.inner_coord' (hφ := hφ),
    ← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef]
  simp only [PosDef.rpow_mul_rpow, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  rw [← conjTranspose_apply, (PosDef.rpow.isPosDef _ _).1.eq]

theorem
  Module.Dual.IsFaithfulPosMap.inner_dualMatrix_right
  (x : Matrix n n ℂ) :
    inner ℂ x φ.matrix⁻¹ = star (x : Matrix n n ℂ).trace :=
by
  simp only [hφ.inner_eq']
  letI := hφ.matrixIsPosDef.invertible
  rw [trace_mul_cycle, inv_mul_of_invertible, one_mul, trace_conjTranspose]

set_option synthInstance.maxHeartbeats 50000 in
theorem QuantumGraph.Real.of_norm_one_matrix_is_irreflexive_iff
  [Nontrivial n] (x : { x : Matrix n n ℂ // ‖x‖ = 1 }) :
    of_norm_one_matrix x •ₛ 1 = 0 ↔ (x : Matrix n n ℂ).trace = 0 :=
by
  simp_rw [of_norm_one_matrix,
    ← QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne,
    ←
    Function.Injective.eq_iff (QuantumSet.Psi 0 (1 / 2)).injective,
    Psi.schurMul, LinearEquiv.apply_symm_apply, QuantumSet.Psi_apply_matrix_one,
    ← _root_.map_mul, ← _root_.map_mul onb.toMatrix, LinearEquiv.map_zero]
  simp only [map_eq_zero_iff _ (StarAlgEquiv.injective _),
    map_eq_zero_iff _ (AlgEquiv.injective _)]
  rw [map_eq_zero_iff _ (StarAlgEquiv.injective onb.toMatrix)]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_rankOne,
    ContinuousLinearMap.coe_coe, rankOne_apply,
    ContinuousLinearMap.coe_eq_zero, rankOne.eq_zero_iff, smul_eq_zero,
    hφ.inner_dualMatrix_right, star_eq_zero]
  letI := hφ.matrixIsPosDef.invertible
  simp only [Invertible.ne_zero, or_false, ne_zero_of_norm_ne_zero
      (a := (x : Matrix n n ℂ))
      (by simp only [x.property, ne_eq, one_ne_zero, not_false_eq_true])]

noncomputable def normalize_of_ne_zero {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {a : E} (ha : a ≠ 0) :
  { x : E // ‖x‖ = 1 } :=
by
  use ((1 / ‖a‖) : ℂ) • a
  rw [norm_smul, norm_div]
  simp only [norm_one, Complex.norm_real, norm_norm, one_div]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)

theorem Module.Dual.IsFaithfulPosMap.norm_sq_dualMatrix_inv :
  (‖φ.matrix⁻¹‖ : ℂ) ^ 2 = (φ.matrix⁻¹).trace :=
by
  rw [← Complex.ofReal_pow, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex]
  rw [hφ.inner_dualMatrix_right, ← trace_conjTranspose,
    hφ.matrixIsPosDef.inv.1.eq]
  refine Complex.conj_eq_iff_re.mp ?_
  simp only [starRingEnd_apply, ← trace_conjTranspose, hφ.matrixIsPosDef.inv.1.eq]

theorem QuantumGraph.Real.of_norm_one_matrix_eq_trivialGraph
  [Nontrivial n] :
    of_norm_one_matrix (hφ := hφ)
      (normalize_of_ne_zero
        (hφ.matrixIsPosDef.inv.invertible.ne_zero))
    = Qam.trivialGraph (Matrix n n ℂ) :=
by
  letI := hφ.matrixIsPosDef.invertible
  simp only [of_norm_one_matrix, normalize_of_ne_zero,
    Qam.trivialGraph_eq, smul_mul_assoc,
    inv_mul_of_invertible, rmul_adjoint, StarMul.star_mul, star_smul,
    _root_.map_smul]
  simp only [← StarMul.star_mul, mul_inv_of_invertible, star_one, _root_.map_one,
    rmul_one, lmul_one, one_mul, smul_smul, star_div₀]
  simp only [one_div, RCLike.star_def, Complex.conj_ofReal, ← pow_two]
  simp only [inv_pow]
  simp only [QuantumSetDeltaForm.delta, ← hφ.norm_sq_dualMatrix_inv]

theorem QuantumGraph.Real.of_norm_one_matrix_is_reflexive_iff
  [Nontrivial n] (x : { x : Matrix n n ℂ // ‖x‖ = 1 }) :
    of_norm_one_matrix x •ₛ 1 = 1 ↔
      ∃ α : ℂˣ,
      (x : Matrix n n ℂ) = (α : ℂ) • φ.matrix⁻¹ :=
by
  simp_rw [of_norm_one_matrix,
    ← QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne,
    ← Function.Injective.eq_iff (QuantumSet.Psi 0 (1 / 2)).injective,
    Psi.schurMul, LinearEquiv.apply_symm_apply, QuantumSet.Psi_apply_matrix_one,
    ← _root_.map_mul, ← _root_.map_mul onb.toMatrix,
    (StarAlgEquiv.injective _).eq_iff, (AlgEquiv.injective _).eq_iff,
    (StarAlgEquiv.injective onb.toMatrix).eq_iff]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_rankOne, ContinuousLinearMap.coe_coe,
    rankOne_apply, ContinuousLinearMap.coe_inj, hφ.inner_dualMatrix_right]
  rw [← sub_eq_zero]
  simp_rw [← LinearMap.sub_apply, ← map_sub]
  letI : Invertible (φ.matrix) := hφ.matrixIsPosDef.invertible
  rw [rankOne.eq_zero_iff, sub_eq_zero]
  simp only [Invertible.ne_zero, or_false, ← trace_conjTranspose]
  constructor
  . intro h
    rw [← h]
    let α := Units.mk0 (((x : Matrix n n ℂ)ᴴ).trace) ?_
    have hα : α = ((x : Matrix n n ℂ)ᴴ).trace := rfl
    use α⁻¹
    simp only [← hα, smul_smul, Units.inv_mul, one_smul]
    . intro hx
      rw [hx, zero_smul, eq_comm] at h
      simp only [Invertible.ne_zero] at h
  . intro ⟨α, hα⟩
    simp_rw [hα, conjTranspose_smul, trace_smul, hφ.matrixIsPosDef.inv.1.eq,
      smul_smul, smul_eq_mul]
    rw [mul_rotate _ _ (α : ℂ), mul_assoc _ _ (star (α : ℂ)), Complex.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← hφ.norm_sq_dualMatrix_inv, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← mul_pow, mul_comm,
      ← norm_smul, ← hα, x.property, one_pow, Complex.ofReal_one, one_smul]

theorem Matrix.traceLinearMap_comp_tensorToKronecker {n : Type*} [DecidableEq n] [Fintype n] :
  Matrix.traceLinearMap (n × n) ℂ ℂ ∘ₗ TensorProduct.toKronecker
    = LinearMap.mul' ℂ _
       ∘ₗ (TensorProduct.map
         (Matrix.traceLinearMap n ℂ ℂ) (Matrix.traceLinearMap n ℂ ℂ)) :=
by ext; simp [TensorProduct.toKronecker_apply, trace_kronecker]

theorem traceLinearMap_comp_transposeStarAlgEquiv_symm
  {n : Type*} [DecidableEq n] [Fintype n] :
  traceLinearMap n ℂ ℂ ∘ₗ (transposeStarAlgEquiv n).symm.toLinearMap
    = traceLinearMap n ℂ ℂ ∘ₗ (unop ℂ).toLinearMap :=
by rfl

open scoped InnerProductSpace
theorem QuantumGraph.NumOfEdges_eq {A : Type*} [starAlgebra A] [QuantumSet A]
  (B : A →ₗ[ℂ] A) :
  QuantumGraph.NumOfEdges B = ⟪1, B 1⟫_ℂ :=
rfl

set_option maxHeartbeats 0 in
theorem QuantumGraph.Real.matrix_submodule_finrank_eq_numOfEdges_of_counit_eq_trace
  (hc : Coalgebra.counit (R := ℂ) (A := Matrix n n ℂ) = Matrix.traceLinearMap n ℂ ℂ)
  {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
  (hA : QuantumGraph.Real _ A) :
  (Module.finrank ℂ hA.matrix_submodule : ℂ) = QuantumGraph.NumOfEdges A :=
by
  simp only [← _root_.orthogonalProjection_trace, hA.matrix_orthogonalProjection_eq]
  simp only [ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply]
  simp only [tensorToKronecker_apply,
    LinearMap.coe_toContinuousLinearMap, OrthonormalBasis.toMatrix_symm_apply',
    LinearMap.trace_conj', ← Matrix.trace_eq_linearMap_trace, QuantumSet.n]
  rw [← Matrix.traceLinearMap_apply _ ℂ, ← LinearMap.comp_apply,
    Matrix.traceLinearMap_comp_tensorToKronecker,
    ← StarAlgEquiv.toLinearMap_apply,
    StarAlgEquiv.lTensor_toLinearMap, ← LinearMap.comp_apply,
    LinearMap.comp_assoc, LinearMap.map_comp_lTensor,
    traceLinearMap_comp_transposeStarAlgEquiv_symm]
  simp only [QuantumGraph.NumOfEdges_eq]
  rw [oneInner_map_one_eq_oneInner_Psi_map _ 0 (1 / 2)]
  rw [← bra_apply_apply ℂ (1 : Matrix n n ℂ ⊗[ℂ] (Matrix n n ℂ)ᵐᵒᵖ),
    ← ContinuousLinearMap.coe_coe,
    ← Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one]
  simp only [TensorProduct.counit_def, hc, Coalgebra.counit_mulOpposite]

theorem Matrix.traceLinearMap_dualMatrix_eq
  {n : Type*} [DecidableEq n] [Fintype n] :
  -- {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap]
  -- (hc : Coalgebra.counit (R := ℂ) (A := Matrix n n ℂ) = Matrix.traceLinearMap n ℂ ℂ) :
  -- φ.matrix = 1 :=
  Module.Dual.matrix (Matrix.traceLinearMap n ℂ ℂ) = 1 :=
by
  refine Eq.symm (Module.Dual.apply_eq_of _ 1 (λ _ => ?_))
  simp only [← counit_eq_dual, one_mul]
  rfl

theorem QuantumGraph.Real.of_norm_one_matrix_eq_of_norm_one_matrix_iff
  {x y : { x : Matrix n n ℂ // ‖x‖ = 1 }} :
  of_norm_one_matrix x = of_norm_one_matrix y
    ↔ ∃ α : ℂˣ, (x : Matrix n n ℂ) = (α : ℂ) • (y : Matrix n n ℂ) :=
by
  simp only [of_norm_one_matrix]
  simp only [← @QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne,
    (LinearEquiv.injective _).eq_iff,
    (StarAlgEquiv.injective _).eq_iff, (AlgEquiv.injective _).eq_iff,
    (StarAlgEquiv.injective onb.toMatrix).eq_iff]
  constructor
  . simp_rw [ContinuousLinearMap.coe_inj];
    exact colinear_of_rankOne_self_eq_rankOne_self _ _
  . rintro ⟨α, hα⟩
    have := x.property
    simp only [hα, norm_smul, y.property, mul_one] at this
    simp only [hα, _root_.map_smul, map_smulₛₗ, RingHom.id_apply,
      ContinuousLinearMap.smul_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_smul]
    rw [smul_smul, RCLike.conj_mul, this, RCLike.ofReal_one, one_pow, one_smul]

theorem QuantumGraph.Real.reflexive_matrix_numOfEdges_eq_one_iff_eq_trivialGraph_of_counit_eq_trace
  [Nontrivial n]
  (hc : Coalgebra.counit (R := ℂ) (A := Matrix n n ℂ) = Matrix.traceLinearMap n ℂ ℂ)
  {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hA : QuantumGraph.Real _ A) (hA₂ : A •ₛ 1 = 1) :
  QuantumGraph.NumOfEdges A = 1 ↔ A = Qam.trivialGraph _ :=
by
  constructor
  · rw [← matrix_submodule_finrank_eq_numOfEdges_of_counit_eq_trace hc hA]
    simp only [Nat.cast_eq_one]
    letI := hφ.matrixIsPosDef.invertible
    intro h
    -- obtain ⟨u, hu⟩ := orthogonalProjection'_of_finrank_eq_one h
    let u : OrthonormalBasis (Fin 1) ℂ _ :=
      by rw [← h]; exact stdOrthonormalBasis ℂ hA.matrix_submodule
    let u' : { x : Matrix n n ℂ // ‖x‖ = 1 } := ⟨u 0, u.norm_eq_one _⟩
    have : A = of_norm_one_matrix u' :=
      by
        rw [hA.matrix_eq_of_orthonormalBasis u]
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
        rfl
    rw [this, ← of_norm_one_matrix_eq_trivialGraph, of_norm_one_matrix_eq_of_norm_one_matrix_iff,
      normalize_of_ne_zero]
    simp only [this] at *
    rw [of_norm_one_matrix_is_reflexive_iff u'] at hA₂
    obtain ⟨α, hα⟩ := hA₂
    simp only [u'] at *
    let α' : ℂˣ := Units.mk0 ‖φ.matrix⁻¹‖ (by simp only [inv_ne_zero,
      ne_eq, Complex.ofReal_eq_zero,
      norm_eq_zero, Invertible.ne_zero, not_false_eq_true])
    have hα' : α' = (‖φ.matrix⁻¹‖ : ℂ) := rfl
    use α * α'
    rw [hα]
    simp only [Units.val_mul, α', Units.val_mk0, smul_smul, one_div]
    simp only [← hα']
    simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
      IsUnit.mul_inv_cancel_right]
  · rintro rfl
    rw [QuantumGraph.NumOfEdges_eq, Qam.trivialGraph_eq,
      LinearMap.smul_apply, inner_smul_right, LinearMap.one_apply]
    have : φ = Matrix.traceLinearMap n ℂ ℂ := by
      rw [← hc]; exact Eq.symm counit_eq_dual
    simp only [QuantumSetDeltaForm.delta, this,
      Matrix.traceLinearMap_dualMatrix_eq, inv_one,
      hφ.inner_eq', one_mul, conjTranspose_one]
    rw [inv_mul_cancel₀]
    simp only [trace_one, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]

theorem counit_eq_traceLinearMap_of_counit_eq_piMat_traceLinearMap
  {ι : Type*} [DecidableEq ι] [Fintype ι] {p : ι → Type*} [Π i, Fintype (p i)]
  [Π i, DecidableEq (p i)]
  {φ : Π i, Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : Π i, (φ i).IsFaithfulPosMap]
  (hc : Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p) = PiMat.traceLinearMap)
  (i : ι) :
  Coalgebra.counit (R := ℂ) (A := Mat ℂ (p i)) = traceLinearMap (p i) ℂ ℂ :=
by
  simp only [PiMat.counit_eq_dual, counit_eq_dual, LinearMap.ext_iff] at hc ⊢
  intro x
  specialize hc (includeBlock ((includeBlock x) i))
  rw [Module.Dual.pi.apply_single_block, includeBlock_apply_same] at hc
  rw [hc]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    traceLinearMap_apply, blockDiagonal'AlgHom_apply, blockDiagonal'_includeBlock_trace']

theorem QuantumGraph.Real.PiMatFinTwo_same_isSelfAdjoint_reflexive_and_numOfEdges_eq_one
  {φ : Π i, Module.Dual ℂ (Matrix (PiFinTwo_same n i) (PiFinTwo_same n i) ℂ)}
  [hφ : Π i, (φ i).IsFaithfulPosMap]
  [Nontrivial n]
  {A : PiMat ℂ (Fin 2) (PiFinTwo_same n) →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n)}
  (hc : Coalgebra.counit (R := ℂ) (A := PiMat ℂ (Fin 2) (PiFinTwo_same n)) = PiMat.traceLinearMap)
  (hA : QuantumGraph.Real _ A) (hA₂ : LinearMap.adjoint A = A) (hA₃ : A •ₛ 1 = 1)
  (hA₄ : QuantumGraph.NumOfEdges A = 1) :
  A = LinearMap.adjoint (LinearMap.proj 0)
    ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwo_same n 0))
    ∘ₗ LinearMap.proj 0
  ∨
  A = LinearMap.adjoint (LinearMap.proj 1)
    ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwo_same n 1))
    ∘ₗ LinearMap.proj 1 :=
by
  obtain (hf | hf) := hA.piFinTwo_same_exists_matrix_map_eq_map_of_adjoint_and_dim_eq_one hA₂
    (by rw [← Nat.cast_inj (R := ℂ),
      QuantumGraph.dim_of_piMat_submodule_eq_numOfEdges_of_trace_counit (hφ := hφ) hc, hA₄,
      Nat.cast_one])
  on_goal 1 =>
    let f := LinearMap.proj 0 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj 0)
    left
  on_goal 2 =>
    let f := LinearMap.proj 1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj 1)
    right
  all_goals
    have hf₁ : f = LinearMap.proj _ ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj _) := rfl
    have hf₂ : QuantumGraph.Real _ f := QuantumGraph.Real.conj_proj_isReal hA _
    have hf₃ : f •ₛ 1 = 1 := by
      simp only [f]
      simp only [LinearMap.one_eq_id]
      nth_rw 1 [← LinearMap.proj_comp_single_same ℂ (φ := λ r => Mat ℂ (PiFinTwo_same n r)) _]
      nth_rw 3 [← LinearMap.comp_one (LinearMap.proj _)]
      simp only [LinearMap.comp_assoc, schurMul_proj_comp]
      rw [← LinearMap.proj_adjoint (hφ := hφ),
        schurMul_comp_proj_adjoint, hA₃, LinearMap.one_comp,
        LinearMap.proj_adjoint, LinearMap.proj_comp_single_same]
    have hf₄ : QuantumGraph.NumOfEdges f = 1 := by
      rw [QuantumGraph.NumOfEdges_eq, ← hf] at hA₄
      simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right] at hA₄
      simp only [← LinearMap.comp_apply, ← LinearMap.comp_assoc] at hA₄
      rw [LinearMap.comp_assoc _ A _, ← hf₁, LinearMap.comp_apply, LinearMap.proj_apply,
        Pi.one_apply] at hA₄
      exact hA₄
    rw [reflexive_matrix_numOfEdges_eq_one_iff_eq_trivialGraph_of_counit_eq_trace
      (counit_eq_traceLinearMap_of_counit_eq_piMat_traceLinearMap hc _) hf₂ (by rw [hf₃])] at hf₄
    rw [← hf₄, hf₁]
    simp only [LinearMap.comp_assoc, hf]

class QuantumGraph.equiv
    {A B : Type*} [starAlgebra A] [QuantumSet A] [starAlgebra B] [QuantumSet B]
    (x : A →ₗ[ℂ] A) (y : B →ₗ[ℂ] B) (f : A ≃⋆ₐ[ℂ] B) : Prop where
  isIsometry : Isometry f
  prop : f.toLinearMap ∘ₗ x = y ∘ₗ f.toLinearMap

lemma QuantumGraph.equiv_prop {A B : Type*} [starAlgebra A] [QuantumSet A]
  [starAlgebra B] [QuantumSet B]
  (x : A →ₗ[ℂ] A) (y : B →ₗ[ℂ] B) {f : A ≃⋆ₐ[ℂ] B} (hf : QuantumGraph.equiv x y f) :
    f.toLinearMap ∘ₗ x = y ∘ₗ f.toLinearMap :=
hf.prop

lemma QuantumGraph.equiv_prop' {A B : Type*} [starAlgebra A] [QuantumSet A]
  [starAlgebra B] [QuantumSet B]
  (x : A →ₗ[ℂ] A) (y : B →ₗ[ℂ] B) {f : A ≃⋆ₐ[ℂ] B} (hf : QuantumGraph.equiv x y f) :
    f.toLinearMap ∘ₗ x ∘ₗ LinearMap.adjoint f.toLinearMap = y :=
by
  rw [← LinearMap.comp_assoc, hf.prop,
    QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm.mp hf.isIsometry,
    eq_comm, ← StarAlgEquiv.comp_eq_iff]

lemma Pi.eq_sum_single_proj (R : Type*) {ι : Type*} [Semiring R]
  [Fintype ι] [DecidableEq ι]
  {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)]
  [(i : ι) → Module R (φ i)]
  (x : Π i, φ i) :
  x = ∑ i, Pi.single (i : ι) (x i) :=
by
  simp_rw [← LinearMap.proj_apply (R := R) (φ := φ), ← LinearMap.single_apply (R:=R),
    ← LinearMap.comp_apply, ← LinearMap.sum_apply, LinearMap.sum_single_comp_proj]
  rfl

def PiMat_finTwo_same_swapStarAlgEquiv {n : Type*} [Fintype n] [DecidableEq n] :
  PiMat ℂ (Fin 2) (PiFinTwo_same n) ≃⋆ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n) :=
StarAlgEquiv.ofAlgEquiv (PiMat_finTwo_same_swapAlgEquiv (n := n))
(λ x => by
  rw [Pi.eq_sum_single_proj ℂ x]
  simp only [Fin.sum_univ_two, Fin.isValue, star_add, map_add, ← Pi.single_star,
    PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_one,
    PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_zero])

lemma PiMat_finTwo_same_swapStarAlgEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
  (x : PiMat ℂ (Fin 2) (PiFinTwo_same n)) :
  PiMat_finTwo_same_swapStarAlgEquiv x =
    Pi.single (0 : Fin 2) (x 1) + Pi.single (1 : Fin 2) (x 0) :=
by
  nth_rw 1 [Pi.eq_sum_single_proj ℂ x]
  simp only [Fin.sum_univ_two, Fin.isValue, star_add, map_add, ← Pi.single_star,
    PiMat_finTwo_same_swapStarAlgEquiv, StarAlgEquiv.ofAlgEquiv_coe,
    PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_one,
    PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_zero, add_comm]

lemma PiMat_finTwo_same_swapStarAlgEquiv_toAlgEquiv {n : Type*} [Fintype n] [DecidableEq n] :
  (PiMat_finTwo_same_swapStarAlgEquiv (n := n)).toAlgEquiv = PiMat_finTwo_same_swapAlgEquiv :=
rfl

theorem PiMat_finTwo_same_swapStarAlgEquiv_symm {n : Type*} [Fintype n] [DecidableEq n] :
  (PiMat_finTwo_same_swapStarAlgEquiv (n := n)).symm
    = PiMat_finTwo_same_swapStarAlgEquiv :=
rfl

lemma PiMat_finTwo_same_swapStarAlgEquiv_isometry :
  LinearMap.adjoint PiMat_finTwo_same_swapStarAlgEquiv.toLinearMap
    = (PiMat_finTwo_same_swapStarAlgEquiv (n := n)).symm.toLinearMap :=
by
  simp only [PiMat_finTwo_same_swapStarAlgEquiv_symm]
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [LinearMap.adjoint_inner_right, StarAlgEquiv.toLinearMap_apply,
    PiMat_finTwo_same_swapStarAlgEquiv_apply]
  nth_rw 1 [Pi.eq_sum_single_proj ℂ x]
  nth_rw 3 [Pi.eq_sum_single_proj ℂ y]
  simp only [Fin.isValue, Fin.sum_univ_two]
  simp only [inner, Fin.isValue, Pi.add_apply, Fin.sum_univ_two,
    Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true,
    Pi.single_eq_of_ne, add_comm, zero_add, one_ne_zero]

theorem PiMat_finTwo_same_swapStarAlgEquiv_comp_linearMapSingle_zero
  {n : Type*} [Fintype n] [DecidableEq n] :
  (PiMat_finTwo_same_swapStarAlgEquiv (n := n)).toLinearMap
    ∘ₗ (LinearMap.single ℂ (fun (j : Fin 2) => Mat ℂ (PiFinTwo_same n j)) 0)
    = LinearMap.single ℂ (fun (j : Fin 2) => Mat ℂ (PiFinTwo_same n j)) 1 :=
PiMat_finTwo_same_swapAlgEquiv_comp_linearMapSingle_zero
theorem PiMat_finTwo_same_swapStarAlgEquiv_comp_linearMapSingle_one
  {n : Type*} [Fintype n] [DecidableEq n] :
  (PiMat_finTwo_same_swapStarAlgEquiv (n := n)).toLinearMap
    ∘ₗ (LinearMap.single ℂ (fun (j : Fin 2) => Mat ℂ (PiFinTwo_same n j)) 1)
    = LinearMap.single ℂ (fun (j : Fin 2) => Mat ℂ (PiFinTwo_same n j)) 0 :=
PiMat_finTwo_same_swapAlgEquiv_comp_linearMapSingle_one
theorem PiMat_finTwo_same_proj_zero_comp_swapStarAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
  LinearMap.proj 0 ∘ₗ (PiMat_finTwo_same_swapStarAlgEquiv (n := n)).toLinearMap
    = LinearMap.proj 1 :=
rfl
theorem PiMat_finTwo_same_proj_one_comp_swapStarAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
  LinearMap.proj 1 ∘ₗ (PiMat_finTwo_same_swapStarAlgEquiv (n := n)).toLinearMap
    = LinearMap.proj 0 :=
rfl

set_option maxHeartbeats 500000 in
theorem
  QuantumGraph.Real.piMatFinTwo_same_eq_zero_of_isSelfAdjoint_and_reflexive_and_numOfEdges_eq_one
  [Nontrivial n]
  (hc : Coalgebra.counit (R := ℂ) (A := PiMat ℂ (Fin 2) (PiFinTwo_same n)) = PiMat.traceLinearMap)
  {A : PiMat ℂ (Fin 2) (PiFinTwo_same n) →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n)}
  (hA : QuantumGraph.Real _ A) (hA₂ : LinearMap.adjoint A = A) (hA₃ : A •ₛ 1 = 1)
  (hA₄ : QuantumGraph.NumOfEdges A = 1) :
  A = 0 :=
by
  rw [← QuantumGraph.dim_of_piMat_submodule_eq_numOfEdges_of_trace_counit hc hA.toQuantumGraph,
    Nat.cast_eq_one] at hA₄
  obtain ⟨i, hi, hf⟩ := hA.exists_unique_includeMap_of_adjoint_and_dim_ofPiMat_submodule_eq_one hA₂ hA₄
  let p : _ → PiMat ℂ _ (PiFinTwo_same n) →ₗ[ℂ] Mat ℂ _ := λ j => LinearMap.proj j
  have hp : ∀ j, p j = LinearMap.proj j := λ j => rfl
  have : ∀ j, p j ∘ₗ LinearMap.adjoint (p j) = 1 :=
  λ j => by
    simp only [LinearMap.proj_adjoint, p, LinearMap.one_eq_id, LinearMap.proj_comp_single_same]
  have this' : ∀ j, (p j ∘ₗ A ∘ₗ LinearMap.adjoint (p j)) •ₛ 1 = 1 :=
  λ j => by
    calc (p j ∘ₗ A ∘ₗ LinearMap.adjoint (p j)) •ₛ 1
        = (p j ∘ₗ A ∘ₗ LinearMap.adjoint (p j) ∘ₗ 1) •ₛ (p j ∘ₗ 1 ∘ₗ LinearMap.adjoint (p j)) :=
          by simp only [LinearMap.one_comp, LinearMap.comp_one, this]
      _ = p j ∘ₗ ((A ∘ₗ LinearMap.adjoint (p j)) •ₛ (1 ∘ₗ LinearMap.adjoint (p j))) :=
          schurMul_proj_comp (hφ := λ _ => hφ) _ _ _
      _ = p j ∘ₗ (A •ₛ 1) ∘ₗ LinearMap.adjoint (p j) :=
          by rw [schurMul_comp_proj_adjoint (hφ := λ _ => hφ)]
      _ = 1 := by simp only [hA₃, LinearMap.one_comp, this]
  have :=
  calc
    LinearMap.adjoint (p i) ∘ₗ p i + ∑ j ∈ Finset.univ \ {i}, LinearMap.adjoint (p j) ∘ₗ p j
      = ∑ j, LinearMap.adjoint (p j) ∘ₗ p j :=
        by
          simp only [Finset.subset_univ, Finset.sum_sdiff_eq_sub, Fin.sum_univ_two, Fin.isValue,
            Finset.sum_singleton, add_sub_cancel, p]
    _ = 1 :=
        by
          rw [LinearMap.one_eq_id, ← LinearMap.sum_single_comp_proj]
          simp only [p, LinearMap.proj_adjoint]
    _ = A •ₛ 1 := hA₃.symm
    _ = ∑ j, (LinearMap.adjoint (p i) ∘ₗ (p i) ∘ₗ A ∘ₗ LinearMap.adjoint (p i) ∘ₗ (p i))
        •ₛ (LinearMap.adjoint (p j) ∘ₗ 1 ∘ₗ p j) :=
        by
          simp only [p, hi]
          simp_rw [← map_sum,
            LinearMap.one_comp]
          congr
          rw [LinearMap.one_eq_id, ← LinearMap.sum_single_comp_proj]
          simp only [p, LinearMap.proj_adjoint, map_sum]
    _ = (LinearMap.adjoint (p i) ∘ₗ (p i) ∘ₗ A ∘ₗ LinearMap.adjoint (p i) ∘ₗ (p i))
        •ₛ (LinearMap.adjoint (p i) ∘ₗ 1 ∘ₗ p i)
        + ∑ j ∈ Finset.univ \ {i},
          (LinearMap.adjoint (p i) ∘ₗ (p i) ∘ₗ A ∘ₗ LinearMap.adjoint (p i) ∘ₗ (p i))
          •ₛ (LinearMap.adjoint (p j) ∘ₗ 1 ∘ₗ p j) :=
        by
          simp only [schurMul_apply_apply, Fin.sum_univ_two, Fin.isValue, Finset.subset_univ,
            Finset.sum_sdiff_eq_sub, Finset.sum_singleton, add_sub_cancel,]
    _ = LinearMap.adjoint (p i) ∘ₗ p i :=
        by
          simp only [map_add, LinearMap.add_apply, p, schurMul_proj_adjoint_comp]
          simp only [← LinearMap.comp_assoc, schurMul_comp_proj]
          simp only [LinearMap.comp_assoc, ← hp, this']
          simp only [LinearMap.one_comp, add_right_eq_self]
          apply Finset.sum_eq_zero
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
          push_neg
          intro j hj
          rw [schurMul_proj_adjoint_comp_of_ne_eq_zero (hφ := λ _ => hφ) hj.symm]
  simp only [Finset.subset_univ, Finset.sum_sdiff_eq_sub, Fin.sum_univ_two, Fin.isValue,
    Finset.sum_singleton, add_sub_cancel, LinearMap.ext_iff, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.proj_adjoint_apply, funext_iff,
    Pi.add_apply, p] at this
  have hii : i = 0 ∨ i = 1 := Fin.exists_fin_two.mp ⟨i, rfl⟩
  specialize this 1 (if i = 0 then 1 else 0)
  rcases hii with (hii | hii)
  <;> rw [hii] at this
  <;> simp only [add_right_eq_self, add_left_eq_self, includeBlock_apply,
      LinearMap.single_apply, dite_eq_right_iff] at this
  <;> simp only [Fin.isValue, ↓reduceIte, ↓dreduceIte, Pi.one_apply, eq_mp_eq_cast, cast_eq,
    one_ne_zero, imp_false, not_true_eq_false, p] at this

-- theorem QuantumGraph.Real.piMatFinTwo_same_isSelfAdjoint_reflexive_and_numOfEdges_eq_one_equiv
--   [Nontrivial n]
--   (hc : Coalgebra.counit (R := ℂ) (A := PiMat ℂ (Fin 2) (PiFinTwo_same n)) = PiMat.traceLinearMap)
--   {A B : PiMat ℂ (Fin 2) (PiFinTwo_same n) →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n)}
--   (hA : QuantumGraph.Real _ A) (hA₂ : LinearMap.adjoint A = A) (hA₃ : A •ₛ 1 = 1)
--   (hA₄ : QuantumGraph.NumOfEdges A = 1)
--   (hB : QuantumGraph.Real _ B) (hB₂ : LinearMap.adjoint B = B) (hB₃ : B •ₛ 1 = 1)
--   (hB₄ : QuantumGraph.NumOfEdges B = 1) :
--   ∃ f : PiMat ℂ (Fin 2) (PiFinTwo_same n) ≃⋆ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n),
--     QuantumGraph.equiv A B f :=
-- by
--   have hA₅ := hA.PiMatFinTwo_same_isSelfAdjoint_reflexive_and_numOfEdges_eq_one hc hA₂ hA₃ hA₄
--   have hB₅ := hB.PiMatFinTwo_same_isSelfAdjoint_reflexive_and_numOfEdges_eq_one hc hB₂ hB₃ hB₄
--   have H1 : ∀ i : Fin 2, (A = LinearMap.adjoint (LinearMap.proj i)
--     ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwo_same n i)) ∘ₗ LinearMap.proj i
--     ∧ B = LinearMap.adjoint (LinearMap.proj i)
--     ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwo_same n i)) ∘ₗ LinearMap.proj i)
--     →
--     QuantumGraph.equiv A B (StarAlgEquiv.refl) :=
--   by
--     intro i h
--     refine ⟨fun x1 ↦ congrFun rfl, ?_⟩
--     apply LinearMap.ext
--     simp only [h, Fin.isValue, LinearMap.coe_comp, LinearMap.coe_proj, Function.comp_apply,
--       Function.eval, StarAlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_refl, id_eq, implies_true]
--   have H2 :
--     ((A = LinearMap.adjoint (LinearMap.proj 0)
--       ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwo_same n 0)) ∘ₗ LinearMap.proj 0
--     ∧ B = LinearMap.adjoint (LinearMap.proj 1)
--       ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwo_same n 1)) ∘ₗ LinearMap.proj 1)
--     ∨
--     (A = LinearMap.adjoint (LinearMap.proj 1)
--       ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwo_same n 1)) ∘ₗ LinearMap.proj 1
--     ∧ B = LinearMap.adjoint (LinearMap.proj 0)
--       ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwo_same n 0)) ∘ₗ LinearMap.proj 0))
--     → QuantumGraph.equiv A B (PiMat_finTwo_same_swapStarAlgEquiv) :=
--   by
--     rintro (h | h)
--     all_goals
--       constructor
--       . rw [QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm]
--         exact PiMat_finTwo_same_swapStarAlgEquiv_isometry
--       . simp_rw [h.1, h.2, LinearMap.comp_assoc]
--         simp only [PiMat_finTwo_same_proj_one_comp_swapStarAlgEquiv,
--           PiMat_finTwo_same_proj_zero_comp_swapStarAlgEquiv,
--           ← LinearMap.comp_assoc, LinearMap.proj_adjoint,
--           PiMat_finTwo_same_swapStarAlgEquiv_comp_linearMapSingle_zero,
--           PiMat_finTwo_same_swapStarAlgEquiv_comp_linearMapSingle_one]
--   obtain (hf | hf) := hA₅
--   . obtain (hg | hg) := hB₅
--     . exact ⟨_, H1 _ ⟨hf, hg⟩⟩
--     . exact ⟨_, H2 (Or.inl ⟨hf, hg⟩)⟩
--   . obtain (hg | hg) := hB₅
--     . exact ⟨_, H2 (Or.inr ⟨hf, hg⟩)⟩
--     . exact ⟨_, H1 _ ⟨hf, hg⟩⟩
