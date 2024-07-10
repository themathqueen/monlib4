import Monlib.LinearAlgebra.Ips.MinimalProj
import Monlib.LinearAlgebra.TensorProduct.OrthonormalBasis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Monlib.LinearAlgebra.QuantumSet.SchurMul
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Monlib.LinearAlgebra.PiDirectSum
import Monlib.LinearAlgebra.Matrix.Reshape

open scoped TensorProduct

noncomputable def Submodule.tensorProduct {R : Type*} {E F : Type*} [CommSemiring R]
  [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
  (V : Submodule R E) (W : Submodule R F) :
    Submodule R (E ⊗[R] F) :=
LinearMap.range (TensorProduct.mapIncl V W : V ⊗[R] W →ₗ[R] E ⊗[R] F)

theorem Submodule.tensorProduct_mem {R : Type*} {E F : Type*} [CommSemiring R]
  [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
  {V : Submodule R E} {W : Submodule R F} (x : V ⊗[R] W) :
  (TensorProduct.mapIncl V W) x ∈ V.tensorProduct W :=
⟨_, rfl⟩

noncomputable def Submodule.mem_tensorProduct {R : Type*} {E F : Type*} [CommSemiring R]
  [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
  {V : Submodule R E} {W : Submodule R F} (vw : V.tensorProduct W) :
  V ⊗[R] W :=
vw.property.choose
theorem Submodule.mem_tensorProduct_eq {R : Type*} {E F : Type*} [CommSemiring R]
  [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
  {V : Submodule R E} {W : Submodule R F} (vw : V.tensorProduct W) :
  (TensorProduct.mapIncl V W) (mem_tensorProduct vw) = vw :=
Set.apply_rangeSplitting (fun x ↦ (TensorProduct.mapIncl V W) x) vw

theorem TensorProduct.mapIncl_isInjective {R : Type*} {E F : Type*} [RCLike R]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace R E] [InnerProductSpace R F]
  [FiniteDimensional R E] [FiniteDimensional R F]
  {V : Submodule R E} {W : Submodule R F} :
  Function.Injective (TensorProduct.mapIncl V W : V ⊗[R] W → E ⊗[R] F) :=
by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := TensorProduct.exists_finset a
  simp only [TensorProduct.mapIncl, map_tmul, map_sum, map_smul, Submodule.coeSubtype] at ha ⊢
  rw [TensorProduct.inner_ext_iff'] at ha ⊢
  intro v w
  specialize ha (↑v) (↑w)
  simp_rw [inner_zero_left, sum_inner, TensorProduct.inner_tmul,
    Submodule.coe_inner] at ha ⊢
  exact ha

theorem Submodule.mapIncl_mem_tensorProduct {R : Type*} {E F : Type*} [RCLike R]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace R E] [InnerProductSpace R F]
  [FiniteDimensional R E] [FiniteDimensional R F]
  {V : Submodule R E} {W : Submodule R F} (v : V ⊗[R] W) :
  Submodule.mem_tensorProduct (⟨_, Submodule.tensorProduct_mem v⟩ : V.tensorProduct W) = v :=
by
  apply_fun (TensorProduct.mapIncl V W) using TensorProduct.mapIncl_isInjective
  rw [Submodule.mem_tensorProduct_eq]

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

theorem norm_tmul {𝕜 B C : Type _} [RCLike 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] (x : B) (y : C) : ‖x ⊗ₜ[𝕜] y‖ = ‖x‖ * ‖y‖ := by
  symm
  calc
    ‖x‖ * ‖y‖ = Real.sqrt (RCLike.re (inner x x : 𝕜)) * Real.sqrt (RCLike.re (inner y y : 𝕜)) := by
      simp_rw [@norm_eq_sqrt_inner 𝕜]
    _ = Real.sqrt (RCLike.re (inner x x : 𝕜) * RCLike.re (inner y y : 𝕜)) := by
      rw [Real.sqrt_mul inner_self_nonneg]
    _ = Real.sqrt (RCLike.re ((inner x x : 𝕜) * (inner y y : 𝕜))) :=
      by
      congr 1
      simp only [RCLike.mul_re, @inner_self_im 𝕜, MulZeroClass.zero_mul, sub_zero]
    _ = Real.sqrt (RCLike.re (inner (x ⊗ₜ[𝕜] y) (x ⊗ₜ[𝕜] y) : 𝕜)) := by
      rw [TensorProduct.inner_tmul]
    _ = ‖x ⊗ₜ[𝕜] y‖ := by rw [@norm_eq_sqrt_inner 𝕜]

noncomputable def Submodule.tensorProduct_linearIsometryEquiv
  (V : Submodule 𝕜 E) (W : Submodule 𝕜 F) :
    (V ⊗[𝕜] W) ≃ₗᵢ[𝕜] (V.tensorProduct W) where
  toFun x := ⟨(TensorProduct.mapIncl V W) x, ⟨_, rfl⟩⟩
  invFun x := Submodule.mem_tensorProduct x
  left_inv x := by simp only [Submodule.mapIncl_mem_tensorProduct]
  right_inv x := by
    refine SetCoe.ext ?_
    exact Submodule.mem_tensorProduct_eq x
  map_add' _ _ := by
    simp only [TensorProduct.mapIncl, map_add, AddSubmonoid.mk_add_mk]
  map_smul' _ _ := by
    simp only [TensorProduct.mapIncl, LinearMapClass.map_smul, RingHom.id_apply, SetLike.mk_smul_mk]
  norm_map' x := by
    simp only [LinearEquiv.coe_mk, Submodule.coe_norm]
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
    simp only [TensorProduct.mapIncl, map_sum, TensorProduct.map_tmul, Submodule.coeSubtype]
    simp_rw [@norm_eq_sqrt_inner 𝕜]
    congr 2
    simp only [inner_sum, sum_inner, TensorProduct.inner_tmul]
    rfl

noncomputable def Submodule.tensorProduct_orthonormalBasis {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  (v : OrthonormalBasis ι₁ 𝕜 V) (w : OrthonormalBasis ι₂ 𝕜 W) :
  OrthonormalBasis (ι₁ × ι₂) 𝕜 (V.tensorProduct W) :=
OrthonormalBasis.map (v.tensorProduct w) (Submodule.tensorProduct_linearIsometryEquiv V W)

theorem Submodule.tensorProduct_orthonormalBasis_apply {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  (v : OrthonormalBasis ι₁ 𝕜 V) (w : OrthonormalBasis ι₂ 𝕜 W) (i : ι₁ × ι₂) :
  Submodule.tensorProduct_orthonormalBasis v w i =
    (v i.1).val ⊗ₜ[𝕜] (w i.2).val :=
by
  simp only [Submodule.tensorProduct_orthonormalBasis, OrthonormalBasis.map_apply]
  simp only [OrthonormalBasis.tensorProduct_apply']
  rfl

theorem Submodule.tensorProduct_finrank {V : Submodule 𝕜 E} {W : Submodule 𝕜 F}
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] :
  FiniteDimensional.finrank 𝕜 (V.tensorProduct W) = FiniteDimensional.finrank 𝕜 V * FiniteDimensional.finrank 𝕜 W :=
by
  simp only [← FiniteDimensional.finrank_tensorProduct]
  refine Eq.symm (LinearEquiv.finrank_eq ?f)
  exact (Submodule.tensorProduct_linearIsometryEquiv V W).toLinearEquiv

theorem orthogonalProjection_map_orthogonalProjection (V : Submodule 𝕜 E) (W : Submodule 𝕜 F) :
  TensorProduct.map
  (orthogonalProjection' V).toLinearMap (orthogonalProjection' W).toLinearMap =
  orthogonalProjection' (V.tensorProduct W) :=
by
  let v := stdOrthonormalBasis 𝕜 V
  let w := stdOrthonormalBasis 𝕜 W
  rw [OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne
    (Submodule.tensorProduct_orthonormalBasis v w),
    OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne v,
    OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne w]
  simp_rw [ContinuousLinearMap.coe_sum, TensorProduct.sum_map, TensorProduct.map_sum,
    ← rankOne_tmul, Submodule.tensorProduct_orthonormalBasis_apply]
  rw [← Finset.sum_product']
  simp only [Finset.univ_product_univ]

theorem TensorProduct.submodule_exists_le_tensorProduct {R M N : Type*}
  [Field R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  (U : Submodule R (M ⊗[R] N)) (hU : Module.Finite R ↥U) :
  ∃ (M' : Submodule R M) (N' : Submodule R N)
    (_ : Module.Finite R ↥M') (_ : Module.Finite R ↥N'),
  U ≤ M'.tensorProduct N' :=
by
  let e := Basis.ofVectorSpace R U
  let e'' : Set U := (Set.range e)
  let e' : Set (M ⊗[R] N) := e''
  let he' : e'.Finite := Set.toFinite e'
  obtain ⟨M', N', hM', hN', hS⟩ := TensorProduct.exists_finite_submodule_of_finite e' he'
  have : Submodule.span R e'' = ⊤ := Basis.span_eq e
  have : Submodule.span R e' = U := by
    simp only [e']
    calc Submodule.span R (Subtype.val '' e'')
        = Submodule.map (U.subtype) (Submodule.span R e'') := ?_
      _ = Submodule.map (U.subtype) (⊤ : Submodule R ↥U) := by rw [this]
      _ = U := by simp only [Submodule.map_top, Submodule.range_subtype]
    rw [← Submodule.span_image]
    rfl
  have :=
    calc U = Submodule.span R e' := this.symm
        _ ≤ Submodule.span R (LinearMap.range (TensorProduct.mapIncl M' N')) :=
      by
          exact Submodule.span_mono hS
  use M', N', hM', hN'
  simp_all only [Submodule.mem_top, iff_true, TensorProduct.mapIncl,
    Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  exact this

theorem orthogonalProjection'_ortho_eq {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E)
  [HasOrthogonalProjection K] :
  orthogonalProjection' Kᗮ = ContinuousLinearMap.id 𝕜 _ - orthogonalProjection' K :=
by
  simp_rw [id_eq_sum_orthogonalProjection_self_orthogonalComplement K,
    ← orthogonalProjection'_eq, add_sub_cancel_left]

theorem TensorProduct.submodule_exists_le_tensorProduct_ofFiniteDimensional
  {R M N : Type*}
  [Field R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [Module.Finite R M] [Module.Finite R N]
  (U : Submodule R (M ⊗[R] N)) :
  ∃ (M' : Submodule R M) (N' : Submodule R N),
  U ≤ M'.tensorProduct N' :=
by
  obtain ⟨V, W, _, _, hVW⟩ := TensorProduct.submodule_exists_le_tensorProduct U
    (FiniteDimensional.finiteDimensional_submodule U)
  refine ⟨V, W, hVW⟩

theorem orthogonalProjection_of_tensorProduct {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℂ E]
  [InnerProductSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  {A : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F}
  (hA : ∃ (U : Submodule ℂ E) (V : Submodule ℂ F),
    (orthogonalProjection' (U.tensorProduct V)).toLinearMap = A) :
  ∃ (U : Submodule ℂ (E ⊗[ℂ] F)), (orthogonalProjection' U).toLinearMap = A :=
by
  obtain ⟨U, V, hUV⟩ := hA
  exact ⟨U.tensorProduct V, hUV⟩

local notation x" ⊗ₘ "y => TensorProduct.map x y

open Matrix

def piProdUnitEquivPi {R n : Type _} [Semiring R] : (n × Unit → R) ≃ₗ[R] n → R
    where
  toFun x i := x (i, PUnit.unit)
  invFun x i := x i.1
  left_inv x := by
    ext; simp
  right_inv x := by ext1; simp only [col_apply]
  map_add' x y := by simp only [Pi.add_apply]; rfl
  map_smul' r x := by simp only [Pi.smul_apply, RingHom.id_apply]; rfl

/-- `matrix.col` written as a linear equivalence -/
def Matrix.ofCol {R n : Type _} [Semiring R] : Matrix n Unit R ≃ₗ[R] n → R :=
  (reshape : Matrix n Unit R ≃ₗ[R] n × Unit → R).trans piProdUnitEquivPi

def matrixProdUnitRight {R n m : Type _} [Semiring R] : Matrix n (m × Unit) R ≃ₗ[R] Matrix n m R
    where
  toFun x i j := x i (j, PUnit.unit)
  invFun x i j := x i j.1
  left_inv x := by
    ext; simp
  right_inv x := by ext1; simp only [col_apply]
  map_add' x y := by simp only [Pi.add_apply]; rfl
  map_smul' r x := by simp only [Pi.smul_apply, RingHom.id_apply]; rfl

open Kronecker
/-- `vec_mulVec x y` written as a kronecker product -/
theorem col_hMul_col_conjTranspose_is_kronecker_of_vectors {R m n : Type _} [Semiring R]
    (x : m → R) (y : n → R) :
    vecMulVec x y =
      reshape.symm
        (Matrix.ofCol (matrixProdUnitRight (col Unit x ⊗ₖ col Unit y))) :=
by
  ext
  simp_rw [reshape_symm_apply, Matrix.ofCol, matrixProdUnitRight, piProdUnitEquivPi,
    LinearEquiv.trans_apply, LinearEquiv.coe_mk, reshape_apply, kronecker_apply, col_apply,
    vecMulVec_apply]

noncomputable def euclideanSpaceTensor {R : Type _} [RCLike R] {ι₁ ι₂ : Type _}
  [Fintype ι₁] [Fintype ι₂]
  [DecidableEq ι₁] [DecidableEq ι₂] :
   (EuclideanSpace R ι₁ ⊗[R] EuclideanSpace R ι₂) ≃ₗ[R]
   EuclideanSpace (R ⊗[R] R) (ι₁ × ι₂) :=
directSumTensor

lemma euclideanSpaceTensor_apply {R : Type _} [RCLike R] {ι₁ ι₂ : Type _}
  [Fintype ι₁] [Fintype ι₂]
  [DecidableEq ι₁] [DecidableEq ι₂] (x : EuclideanSpace R ι₁) (y : EuclideanSpace R ι₂)
  (i : ι₁ × ι₂) :
  euclideanSpaceTensor (x ⊗ₜ y) i = x i.1 ⊗ₜ y i.2 :=
rfl

theorem euclideanSpaceTensor_norm_map {R : Type _} [RCLike R] {ι₁ ι₂ : Type _}
  [Fintype ι₁] [Fintype ι₂]
  [DecidableEq ι₁] [DecidableEq ι₂] (x : EuclideanSpace R ι₁) (y : EuclideanSpace R ι₂) :
  ‖euclideanSpaceTensor (x ⊗ₜ[R] y)‖ = ‖x ⊗ₜ[R] y‖ :=
by
  rw [PiLp.norm_eq_of_L2]
  simp_rw [euclideanSpaceTensor_apply, norm_tmul]
  rw [Finset.sum_product_univ]
  simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul,
    Real.sqrt_mul (Finset.sum_nonneg (λ _ _ => (sq_nonneg _))),
    ← PiLp.norm_eq_of_L2]

theorem TensorProduct.ring_tmul {R : Type*} [CommRing R] (x : R ⊗[R] R) :
  ∃ (a b : R), x = a ⊗ₜ[R] b :=
TensorProduct.singleton_tmul x (Basis.singleton _ _) (Basis.singleton _ _)

theorem submodule_neq_tensorProduct_of {R : Type*} [RCLike R]
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace R E] [InnerProductSpace R F]
  [FiniteDimensional R E] [FiniteDimensional R F]
  (U : Submodule R (E ⊗[R] F))
  {p : ℕ} (hp : Nat.Prime p)
  (hU : FiniteDimensional.finrank R U = p) :
  ¬ ∃ (V : Submodule R E) (W : Submodule R F)
      (_ : 1 < FiniteDimensional.finrank R V)
      (_ : 1 < FiniteDimensional.finrank R W),
      U = V.tensorProduct W :=
by
  push_neg
  intro V W hVW₁ hVW₂ hVW
  have : FiniteDimensional.finrank R (V.tensorProduct W) =
    FiniteDimensional.finrank R V * FiniteDimensional.finrank R W := Submodule.tensorProduct_finrank
  rw [← hVW, hU] at this
  exact
    (Nat.not_prime_mul' this.symm (Ne.symm (Nat.ne_of_lt hVW₁)) (Ne.symm (Nat.ne_of_lt hVW₂)))
    hp
