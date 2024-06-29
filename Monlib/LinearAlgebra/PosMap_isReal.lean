import Monlib.LinearAlgebra.InnerAut
import Monlib.LinearAlgebra.Matrix.IncludeBlock
import Monlib.LinearAlgebra.InvariantSubmodule
import Monlib.LinearAlgebra.Ips.MinimalProj
import Monlib.LinearAlgebra.Nacgor
import Mathlib.Analysis.NormedSpace.Star.Matrix
import Monlib.LinearAlgebra.OfNorm
import Monlib.LinearAlgebra.Matrix.StarOrderedRing
import Monlib.LinearAlgebra.Matrix.PosDefRpow
import Monlib.LinearAlgebra.ToMatrixOfEquiv
import Mathlib.Analysis.InnerProductSpace.Positive

variable {A : Type _} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [PartialOrder A]
  [_root_.StarOrderedRing A]

/-- we say a map $f \colon M_1 \to M_2$ is a positive map
  if for all positive $x \in M_1$, we also get $f(x)$ is positive -/
def LinearMap.IsPosMap
  {M₁ M₂ : Type*} [Zero M₁] [Zero M₂] [PartialOrder M₁] [PartialOrder M₂]
  {F : Type*} [FunLike F M₁ M₂] (f : F) : Prop :=
∀ ⦃x : M₁⦄, 0 ≤ x → 0 ≤ f x

noncomputable abbrev selfAdjointDecomposition_left (a : A) :=
(1 / 2 : ℂ) • (a + star a)
local notation "aL" => selfAdjointDecomposition_left

noncomputable abbrev selfAdjointDecomposition_right (a : A) :=
(RCLike.I : ℂ) • ((1 / 2 : ℂ) • (star a - a))
local notation "aR" => selfAdjointDecomposition_right

theorem selfAdjointDecomposition_left_isSelfAdjoint (a : A) : IsSelfAdjoint (aL a) :=
by simp [selfAdjointDecomposition_left, isSelfAdjoint_iff, star_smul, add_comm]

theorem selfAdjointDecomposition_right_isSelfAdjoint (a : A) : IsSelfAdjoint (aR a) :=
by
  simp [selfAdjointDecomposition_right, isSelfAdjoint_iff, star_smul, smul_smul]
  rw [← neg_sub, ← neg_smul, neg_smul_neg]

theorem selfAdjointDecomposition (a : A) :
  a = aL a + (RCLike.I : ℂ) • (aR a) :=
by
  simp_rw [selfAdjointDecomposition_left, selfAdjointDecomposition_right,
    smul_smul, ← mul_assoc, RCLike.I, Complex.I_mul_I, smul_add, smul_sub,
    neg_mul, one_mul, neg_smul, neg_sub_neg]
  simp only [one_div, add_add_sub_cancel]
  simp_rw [← two_smul ℂ, smul_smul]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel, one_smul]

noncomputable
def ContinuousLinearMap.toLinearMapAlgEquiv
  {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B] :
  (B →L[𝕜] B) ≃ₐ[𝕜] (B →ₗ[𝕜] B) :=
AlgEquiv.ofLinearEquiv LinearMap.toContinuousLinearMap.symm rfl (λ _ _ => rfl)

lemma ContinuousLinearMap.toLinearMapAlgEquiv_apply
  {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B]
  (f : B →L[𝕜] B) :
  ContinuousLinearMap.toLinearMapAlgEquiv f = f.toLinearMap :=
rfl

lemma ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply
  {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B]
  (f : B →ₗ[𝕜] B) :
  ContinuousLinearMap.toLinearMapAlgEquiv.symm f = LinearMap.toContinuousLinearMap f :=
rfl

theorem ContinuousLinearMap.spectrum_coe {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B] (T : B →L[𝕜] B) :
  spectrum 𝕜 T.toLinearMap = spectrum 𝕜 T :=
by rw [← ContinuousLinearMap.toLinearMapAlgEquiv_apply, AlgEquiv.spectrum_eq]

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [FiniteDimensional ℂ B]

open scoped MatrixOrder ComplexOrder FiniteDimensional
-- set_option synthInstance.checkSynthOrder false in
-- attribute [instance] FiniteDimensional.complete
theorem ContinuousLinearMap.nonneg_iff_isSelfAdjoint_and_nonneg_spectrum
  (T : B →L[ℂ] B) :
  0 ≤ T ↔ IsSelfAdjoint T ∧ spectrum ℂ T ⊆ {a : ℂ | 0 ≤ a} :=
by
  rw [nonneg_iff_isPositive, ← ContinuousLinearMap.IsPositive.toLinearMap,
    LinearMap.isPositive_iff_isSymmetric_and_nonneg_spectrum,
    isSelfAdjoint_iff_isSymmetric, spectrum_coe]

theorem ContinuousLinearMap.nonneg_iff_exists
  (T : B →L[ℂ] B) :
  0 ≤ T ↔ ∃ f, T = star f * f :=
by rw [nonneg_iff_isPositive]; exact isPositive_iff_exists_adjoint_hMul_self _

def ContinuousLinearMap.StarOrderedRing :
  _root_.StarOrderedRing (B →L[ℂ] B) :=
StarOrderedRing.of_nonneg_iff'
  (λ hxy z => by simp_rw [le_def, add_sub_add_left_eq_sub]; exact hxy)
  (λ x => by
    rw [nonneg_iff_isPositive]
    exact ContinuousLinearMap.isPositive_iff_exists_adjoint_hMul_self _)
attribute [local instance] ContinuousLinearMap.StarOrderedRing

private lemma auxaux {T S : B →L[ℂ] B} (h : T * S = 0) :
  orthogonalProjection' (LinearMap.ker T) * S = S :=
by
  have : LinearMap.range S ≤ LinearMap.ker T := by
    intro x ⟨y, hy⟩
    rw [← hy, LinearMap.mem_ker, ← ContinuousLinearMap.mul_apply, h,
      ContinuousLinearMap.zero_apply]
  rw [← orthogonalProjection.range (LinearMap.ker T)] at this
  rw [← ContinuousLinearMap.coe_inj, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.coe_comp, IsIdempotentElem.comp_idempotent_iff]
  . simp only [Submodule.map_top, ContinuousLinearMap.range_toLinearMap]
    exact this
  . simp only [← ContinuousLinearMap.IsIdempotentElem.toLinearMap]
    exact orthogonalProjection.isIdempotentElem _

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- matrix of orthogonalProjection -/
noncomputable def Matrix.orthogonalProjection (U : Submodule ℂ (EuclideanSpace ℂ n)) :
  Matrix n n ℂ :=
toEuclideanCLM.symm.toFun (orthogonalProjection' U)

lemma Matrix.isIdempotentElem_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n]
  (x : Matrix n n ℂ) :
  IsIdempotentElem x ↔ IsIdempotentElem (toEuclideanCLM.toFun x) :=
by
  simp_rw [IsIdempotentElem]
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm,
    StarAlgEquiv.toRingEquiv_eq_coe, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, ← _root_.map_mul]
  rw [Function.Injective.eq_iff (RingEquiv.injective _)]

lemma Matrix.CLM_apply_orthogonalProjection {U : Submodule ℂ (EuclideanSpace ℂ n)} :
  Matrix.toEuclideanCLM.toFun (Matrix.orthogonalProjection U)
    = orthogonalProjection' U :=
by
  ext1
  simp [orthogonalProjection', orthogonalProjection]

lemma StarAlgEquiv.toFun_eq {R A B : Type*} [Add A] [Add B] [Mul A] [Mul B]
  [SMul R A] [SMul R B] [Star A] [Star B] (f : A ≃⋆ₐ[R] B) (a : A) :
  f.toFun a = f a :=
rfl

lemma Matrix.orthogonalProjection_ortho_eq {U : Submodule ℂ (EuclideanSpace ℂ n)} :
  Matrix.orthogonalProjection Uᗮ = 1 - Matrix.orthogonalProjection U :=
by
  apply_fun Matrix.toEuclideanCLM.toFun
  simp only [StarAlgEquiv.toFun_eq, _root_.map_mul, map_sub, _root_.map_one]
  simp only [← StarAlgEquiv.toFun_eq, Matrix.CLM_apply_orthogonalProjection]
  exact orthogonalProjection.orthogonal_complement_eq U

lemma Matrix.orthogonalProjection_isPosSemidef {U : Submodule ℂ (EuclideanSpace ℂ n)} :
  (Matrix.orthogonalProjection U).PosSemidef :=
by
  rw [posSemidef_eq_linearMap_positive, ← coe_toEuclideanCLM_eq_toEuclideanLin,
    ← StarAlgEquiv.toFun_eq, Matrix.CLM_apply_orthogonalProjection,
    ContinuousLinearMap.IsPositive.toLinearMap,
    ← ContinuousLinearMap.nonneg_iff_isPositive]
  exact orthogonalProjection.is_positive

lemma Matrix.IsHermitian.orthogonalProjection_ker_apply_self {x : Matrix n n ℂ}
  (hx : x.IsHermitian) :
  Matrix.orthogonalProjection (LinearMap.ker (toEuclideanCLM.toFun x)) * x = 0 :=
by
  apply_fun Matrix.toEuclideanCLM.toFun
  simp only [StarAlgEquiv.toFun_eq, _root_.map_mul, map_zero]
  simp only [← StarAlgEquiv.toFun_eq, Matrix.CLM_apply_orthogonalProjection]
  simp only [StarAlgEquiv.toFun_eq]
  ext1
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply]
  simp only [orthogonalProjection'_eq, ContinuousLinearMap.coe_comp', Submodule.coe_subtypeL',
    Submodule.coeSubtype, Function.comp_apply, ZeroMemClass.coe_eq_zero,
    orthogonalProjection_eq_zero_iff]
  rw [ContinuousLinearMap.ker_eq_ortho_adjoint_range, Submodule.orthogonal_orthogonal,
    ← ContinuousLinearMap.star_eq_adjoint]
  simp only [← StarAlgEquiv.toFun_eq, ← StarAlgEquiv.map_star', star_eq_conjTranspose,
    hx.eq]
  exact LinearMap.mem_range_self _ _

private lemma auxaux_2 {T S : Matrix n n ℂ} (h : T * S = 0) :
  Matrix.orthogonalProjection (LinearMap.ker (Matrix.toEuclideanCLM.toFun T)) * S = S :=
by
  apply_fun Matrix.toEuclideanCLM.toFun at h ⊢
  simp only [StarAlgEquiv.toFun_eq, _root_.map_mul, map_zero] at h ⊢
  simp only [← StarAlgEquiv.toFun_eq, Matrix.CLM_apply_orthogonalProjection]
  simp only [StarAlgEquiv.toFun_eq]
  exact auxaux h

theorem Matrix.nonneg_def {x : Matrix n n ℂ} :
  0 ≤ x ↔ x.PosSemidef :=
by rw [le_iff, sub_zero]

/-- the positive square root of the square of a Hermitian matrix `x`,
  in other words, `√(x ^ 2)` -/
noncomputable def Matrix.IsHermitian.sqSqrt {x : Matrix n n ℂ}
  (hx : x.IsHermitian) :
  Matrix n n ℂ :=
innerAut (hx.eigenvectorUnitary)
  (Matrix.diagonal (RCLike.ofReal ∘ (λ i => √ ((hx.eigenvalues i) ^ 2 : ℝ))))

lemma Matrix.IsHermitian.sqSqrt_eq {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  hx.sqSqrt = innerAut (hx.eigenvectorUnitary)
    (Matrix.diagonal (RCLike.ofReal ∘ (|hx.eigenvalues|))) :=
by simp only [sqSqrt, Real.sqrt_sq_eq_abs]; rfl

lemma Matrix.IsHermitian.sqSqrt_isPosSemidef {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  hx.sqSqrt.PosSemidef :=
by
  rw [sqSqrt_eq]
  apply (innerAut_posSemidef_iff _).mpr
  apply (diagonal_posSemidef_iff _).mpr
  intro
  rw [Function.comp_apply, Pi.zero_apply, RCLike.ofReal_nonneg, Pi.abs_apply]
  exact abs_nonneg _

/-- the square of the positive square root of a Hermitian matrix is equal to the square of the matrix -/
lemma Matrix.IsHermitian.sqSqrt_sq {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  hx.sqSqrt ^ 2 = x ^ 2 :=
by
  symm
  nth_rw 1 [hx.spectral_theorem'']
  simp_rw [sqSqrt, innerAut.map_pow, diagonal_pow]
  congr
  simp only [diagonal_eq_diagonal_iff, Pi.pow_apply, Function.comp_apply, ← RCLike.ofReal_pow,
    Real.sq_sqrt (sq_nonneg _), implies_true]

noncomputable def Matrix.IsHermitian.posSemidefDecomposition_left (x : Matrix n n ℂ) [hx : Fact x.IsHermitian] :=
(1 / 2 : ℂ) • (hx.out.sqSqrt + x)
notation3:80 (name := posL) x:81"₊" =>
  @Matrix.IsHermitian.posSemidefDecomposition_left _ _ _ x _
lemma Matrix.IsHermitian.posSemidefDecomposition_left_isHermitian
  {x : Matrix n n ℂ} [hx : Fact x.IsHermitian] : x₊.IsHermitian :=
by
  rw [IsHermitian, posSemidefDecomposition_left, conjTranspose_smul,
    conjTranspose_add, hx.out.eq, RCLike.star_def]
  simp only [one_div, map_inv₀, map_ofNat]
  congr
  apply (innerAut_isHermitian_iff _ _).mp _
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  simp only [Function.comp_apply, _root_.IsSelfAdjoint, RCLike.star_def, RCLike.conj_ofReal]

noncomputable def Matrix.IsHermitian.posSemidefDecomposition_right
  (x : Matrix n n ℂ) [hx : Fact x.IsHermitian] :=
(1 / 2 : ℂ) • (hx.out.sqSqrt - x)
notation3:80 (name := posR) x:81"₋" =>
  Matrix.IsHermitian.posSemidefDecomposition_right x
lemma Matrix.IsHermitian.posSemidefDecomposition_right_isHermitian
  {x : Matrix n n ℂ} [hx : Fact x.IsHermitian] :
  x₋.IsHermitian :=
by
  rw [IsHermitian, posSemidefDecomposition_right, conjTranspose_smul,
    conjTranspose_sub, hx.out.eq, RCLike.star_def]
  simp only [one_div, map_inv₀, map_ofNat]
  congr
  apply (innerAut_isHermitian_iff _ _).mp _
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  simp only [Function.comp_apply, _root_.IsSelfAdjoint, RCLike.star_def, RCLike.conj_ofReal]

/-- a Hermitian matrix commutes with its positive squared-square-root,
  i.e., `x * √(x^2) = √(x^2) * x`. -/
lemma Matrix.IsHermitian.commute_sqSqrt {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  Commute x hx.sqSqrt :=
by
  rw [Commute, SemiconjBy]
  nth_rw 1 [hx.spectral_theorem'']
  symm
  nth_rw 2 [hx.spectral_theorem'']
  simp only [sqSqrt, ← Matrix.innerAut.map_mul, diagonal_mul_diagonal, mul_comm]

lemma Matrix.IsHermitian.posSemidefDecomposition_left_mul_right (x : Matrix n n ℂ)
  [hx : Fact x.IsHermitian] :
  x₊ * x₋ = 0 :=
by
  simp_rw [posSemidefDecomposition_left, posSemidefDecomposition_right,
    smul_add, smul_sub, add_mul, mul_sub]
  simp only [one_div, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  simp_rw [← pow_two, hx.out.commute_sqSqrt.eq]
  simp only [sub_add_sub_cancel, sqSqrt_sq, hx.out.eq, ← pow_two]
  simp only [sub_self]
lemma Matrix.IsHermitian.posSemidefDecomposition_right_mul_left (x : Matrix n n ℂ)
  [hx : Fact x.IsHermitian] :
  x₋ * x₊ = 0 :=
by
  simp_rw [posSemidefDecomposition_left, posSemidefDecomposition_right,
    smul_add, smul_sub, sub_mul, mul_add]
  simp only [one_div, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  simp_rw [← pow_two, hx.out.commute_sqSqrt.eq]
  nth_rw 1 [sqSqrt_sq]
  simp only [sub_add_eq_sub_sub, add_sub_cancel_right, sub_self]

lemma Matrix.IsHermitian.posSemidefDecomposition_eq (x : Matrix n n ℂ) [hx : Fact x.IsHermitian] :
  x = x₊ - x₋ :=
by
  simp_rw [posSemidefDecomposition_left, posSemidefDecomposition_right,
    ← smul_sub, add_sub_sub_cancel, ← two_smul ℂ, smul_smul]
  norm_num

theorem Matrix.IsHermitian.posSemidefDecomposition_posSemidef_left_right
  {x : Matrix n n ℂ} (hx : Fact x.IsHermitian) :
  x₊.PosSemidef ∧ x₋.PosSemidef  :=
by
  have h := λ (a b : Matrix n n ℂ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    => Matrix.posSemidef_iff_commute ha hb
  simp only [sub_zero, Matrix.nonneg_def] at h
  have h₂ := auxaux_2 (IsHermitian.posSemidefDecomposition_left_mul_right x)
  have h₃ : hx.out.sqSqrt = x₊ + x₋ :=
  by
    simp_rw [IsHermitian.posSemidefDecomposition_left, IsHermitian.posSemidefDecomposition_right,
      ← smul_add, add_add_sub_cancel, ← two_smul ℂ, smul_smul]
    norm_num
  have h₄ : orthogonalProjection (LinearMap.ker (toEuclideanCLM.toFun (x₊))) * hx.out.sqSqrt = x₋ :=
  by
    rw [h₃, mul_add, h₂, Matrix.IsHermitian.orthogonalProjection_ker_apply_self
      IsHermitian.posSemidefDecomposition_left_isHermitian, zero_add]
  have h₅ : x = (1 - (2 : ℂ) • (orthogonalProjection (LinearMap.ker (toEuclideanCLM.toFun (x₊)))))
    * hx.out.sqSqrt :=
  by
    rw [sub_mul, smul_mul_assoc, h₄, h₃, one_mul, two_smul, add_sub_add_right_eq_sub]
    exact IsHermitian.posSemidefDecomposition_eq _
  have h₆ : x₊ = (orthogonalProjection (LinearMap.ker (toEuclideanCLM.toFun (x₊)))ᗮ)
    * hx.out.sqSqrt :=
  by
    nth_rw 1 [IsHermitian.posSemidefDecomposition_left]
    nth_rw 3 [h₅]
    rw [Matrix.orthogonalProjection_ortho_eq]
    simp_rw [sub_mul, one_mul, smul_add, smul_sub, smul_mul_assoc,
      h₄, smul_smul, add_sub, ← smul_add, ← two_smul ℂ, smul_smul]
    norm_num
  have h₄' : x₋ = hx.out.sqSqrt * (orthogonalProjection (LinearMap.ker (toEuclideanCLM.toFun (x₊)))) :=
  by rw [← IsHermitian.posSemidefDecomposition_right_isHermitian, ← h₄,
    conjTranspose_mul, (IsHermitian.sqSqrt_isPosSemidef _).1.eq,
    Matrix.orthogonalProjection_isPosSemidef.1.eq]
  have h₆' : x₊ = hx.out.sqSqrt * (orthogonalProjection (LinearMap.ker (toEuclideanCLM.toFun (x₊)))ᗮ) :=
  by
    nth_rw 1 [← IsHermitian.posSemidefDecomposition_left_isHermitian, h₆]
    rw [conjTranspose_mul, (IsHermitian.sqSqrt_isPosSemidef _).1.eq,
      Matrix.orthogonalProjection_isPosSemidef.1.eq]
  constructor
  . rw [h₆', ← h _ _ (IsHermitian.sqSqrt_isPosSemidef _)
      orthogonalProjection_isPosSemidef, Commute, SemiconjBy, ← h₆, ← h₆']
  . rw [h₄', ← h _ _ (IsHermitian.sqSqrt_isPosSemidef _)
      orthogonalProjection_isPosSemidef, Commute, SemiconjBy, h₄, ← h₄']

open scoped Matrix
theorem Matrix.IsHermitian.posSemidefDecomposition'
  {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  ∃ a b, x = aᴴ * a - bᴴ * b :=
by
  let hx := Fact.mk hx
  simp_rw [posSemidefDecomposition_eq]
  obtain ⟨α, hα⟩ := posSemidef_iff_eq_transpose_mul_self.mp
    (posSemidefDecomposition_posSemidef_left_right hx).1
  obtain ⟨β, hβ⟩ := posSemidef_iff_eq_transpose_mul_self.mp
    (posSemidefDecomposition_posSemidef_left_right hx).2
  use α, β
  rw [← hα, ← hβ]

theorem PiMat.IsSelfAdjoint.posSemidefDecomposition {k : Type*} {n : k → Type*}
  [Fintype k] [DecidableEq k] [Π i, Fintype (n i)] [Π i, DecidableEq (n i)]
  {x : PiMat ℂ k n} (hx : IsSelfAdjoint x) :
  ∃ a b, x = star a * a - star b * b :=
by
  have : ∀ i, (x i).IsHermitian := λ i =>
  by
    rw [IsSelfAdjoint, Function.funext_iff] at hx
    simp_rw [Pi.star_apply, Matrix.star_eq_conjTranspose] at hx
    exact hx i
  have := λ i => Matrix.IsHermitian.posSemidefDecomposition' (this i)
  let a : PiMat ℂ k n :=
  λ i => (this i).choose
  let b : PiMat ℂ k n :=
  λ i => (this i).choose_spec.choose
  have hab : ∀ i, x i = star (a i) * (a i) - star (b i) * (b i) :=
  λ i => (this i).choose_spec.choose_spec
  use a, b
  ext1
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.star_apply, hab]

open ContinuousLinearMap in
theorem IsSelfAdjoint.isPositiveDecomposition
  {x : B →L[ℂ] B} (hx : IsSelfAdjoint x) :
  ∃ a b, x = star a * a - star b * b :=
by
  let e := stdOrthonormalBasis ℂ B
  have hx' : Matrix.IsHermitian (e.toMatrix x.toLinearMap) :=
  by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, ← StarAlgEquiv.toFun_eq,
      ← StarAlgEquiv.map_star']
    congr
    rw [isSelfAdjoint_iff_isSymmetric, LinearMap.isSymmetric_iff_isSelfAdjoint] at hx
    exact hx
  obtain ⟨a, b, hab⟩ := hx'.posSemidefDecomposition'
  let a' : B →L[ℂ] B := LinearMap.toContinuousLinearMap (e.toMatrix.symm a)
  let b' : B →L[ℂ] B := LinearMap.toContinuousLinearMap (e.toMatrix.symm b)
  use a', b'
  apply_fun e.toMatrix.symm at hab
  simp_rw [StarAlgEquiv.symm_apply_apply, map_sub, map_mul, ← Matrix.star_eq_conjTranspose,
    ← StarAlgEquiv.toFun_eq, StarAlgEquiv.map_star'] at hab
  calc x = LinearMap.toContinuousLinearMap (x.toLinearMap) := rfl
    _ = LinearMap.toContinuousLinearMap (star (e.toMatrix.symm a)) * a' -
      LinearMap.toContinuousLinearMap (star (e.toMatrix.symm b)) * b' := ?_
    _ = star a' * a' - star b' * b' := ?_
  . rw [hab, ← toLinearMapAlgEquiv_symm_apply, map_sub, map_mul]
    rfl
  . congr 1

theorem IsSelfAdjoint.isPositiveDecomposition_of_starAlgEquiv_piMat
  {k : Type*} {n : k → Type*} [Fintype k] [DecidableEq k]
  [Π i, Fintype (n i)] [Π i, DecidableEq (n i)] (φ : A ≃⋆ₐ[ℂ] (PiMat ℂ k n))
  {x : A} (hx : _root_.IsSelfAdjoint x) :
  ∃ a b, x = star a * a - star b * b :=
by
  have : IsSelfAdjoint (φ x) := by
    rw [IsSelfAdjoint, ← StarAlgEquiv.toFun_eq, ← StarAlgEquiv.map_star', hx]
  obtain ⟨α, β, h⟩ := PiMat.IsSelfAdjoint.posSemidefDecomposition this
  use φ.symm α, φ.symm β
  apply_fun φ
  simp_rw [h, map_sub, map_mul, ← StarAlgEquiv.toFun_eq, StarAlgEquiv.map_star',
    StarAlgEquiv.toFun_eq, StarAlgEquiv.apply_symm_apply]

/-- if a map preserves positivity, then it is star-preserving -/
theorem isReal_of_isPosMap
  {K : Type*}
  [Ring K] [StarRing K] [PartialOrder K] [Algebra ℂ K] [StarOrderedRing K] [StarModule ℂ K]
  {φ : (B →L[ℂ] B) →ₗ[ℂ] K} (hφ : LinearMap.IsPosMap φ) :
  LinearMap.IsReal φ :=
by
  intro x
  rw [selfAdjointDecomposition x]
  let L := aL x
  have hL : L = aL x := rfl
  let R := aR x
  have hR : R = aR x := rfl
  rw [← hL, ← hR]
  simp only [star_add, map_add, star_smul, map_smul]
  repeat rw [selfAdjointDecomposition_left_isSelfAdjoint _]
  suffices h2 : ∀ a (_ : IsSelfAdjoint a),
      φ (star a) = star (φ a)
  by rw [← h2 _ (selfAdjointDecomposition_left_isSelfAdjoint _),
    ← h2 _ (selfAdjointDecomposition_right_isSelfAdjoint _),
    selfAdjointDecomposition_left_isSelfAdjoint,
    selfAdjointDecomposition_right_isSelfAdjoint]
  intro x hx
  obtain ⟨a, b, rfl⟩ := hx.isPositiveDecomposition
  simp only [star_sub, star_mul, star_star, map_sub]
  rw [IsSelfAdjoint.of_nonneg (hφ (star_mul_self_nonneg a)),
    IsSelfAdjoint.of_nonneg (hφ (star_mul_self_nonneg b))]

theorem isReal_of_isPosMap_of_starAlgEquiv_piMat
  {k : Type*} {n : k → Type*} [Fintype k] [DecidableEq k]
  [Π i, Fintype (n i)] [Π i, DecidableEq (n i)] (φ : A ≃⋆ₐ[ℂ] PiMat ℂ k n)
  {K : Type*}
  [Ring K] [StarRing K] [PartialOrder K] [Algebra ℂ K] [StarOrderedRing K] [StarModule ℂ K]
  {f : A →ₗ[ℂ] K} (hf : LinearMap.IsPosMap f) :
  LinearMap.IsReal f :=
by
  intro x
  rw [selfAdjointDecomposition x]
  let L := aL x
  have hL : L = aL x := rfl
  let R := aR x
  have hR : R = aR x := rfl
  rw [← hL, ← hR]
  simp only [star_add, map_add, star_smul, map_smul]
  repeat rw [selfAdjointDecomposition_left_isSelfAdjoint _]
  suffices h2 : ∀ a (_ : IsSelfAdjoint a),
      f (star a) = star (f a)
  by rw [← h2 _ (selfAdjointDecomposition_left_isSelfAdjoint _),
    ← h2 _ (selfAdjointDecomposition_right_isSelfAdjoint _),
    selfAdjointDecomposition_left_isSelfAdjoint,
    selfAdjointDecomposition_right_isSelfAdjoint]
  intro x hx
  obtain ⟨a, b, rfl⟩ := hx.isPositiveDecomposition_of_starAlgEquiv_piMat φ
  simp only [star_sub, star_mul, star_star, map_sub]
  rw [IsSelfAdjoint.of_nonneg (hf (star_mul_self_nonneg a)),
    IsSelfAdjoint.of_nonneg (hf (star_mul_self_nonneg b))]

/-- a $^*$-homomorphism from $A$ to $B$ is a positive map -/
theorem StarAlgHom.isPosMap
  {R A K : Type*}
  [CommSemiring R]
  [Semiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [Algebra R A]
  [Semiring K] [PartialOrder K] [StarRing K] [StarOrderedRing K] [Algebra R K]
  (hA : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ b, a = star b * b)
  (f : A →⋆ₐ[R] K) :
  LinearMap.IsPosMap f :=
by
  intro a ha
  obtain ⟨b, rfl⟩ := hA.mp ha
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

theorem LinearMap.isPosMap_iff_star_mul_self_nonneg {R A K : Type*}
  [CommSemiring R]
  [Semiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [Algebra R A]
  [Semiring K] [PartialOrder K] [StarRing K] [StarOrderedRing K] [Algebra R K]
  (hA : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ b, a = star b * b)
  {f : A →ₗ[R] K} :
  LinearMap.IsPosMap f ↔ ∀ a : A, 0 ≤ f (star a * a) :=
by
  refine ⟨λ h a => h (star_mul_self_nonneg _), λ h a => ?_⟩
  . rw [hA]
    rintro ⟨b, rfl⟩
    exact h _

theorem AlgHom.isPosMap_iff_isReal_of_starAlgEquiv_piMat
  {k : Type*} {n : k → Type*} [Fintype k] [DecidableEq k]
  [Π i, Fintype (n i)] [Π i, DecidableEq (n i)] (φ : A ≃⋆ₐ[ℂ] PiMat ℂ k n)
  (hA : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ b, a = star b * b)
  {K : Type*}
  [Ring K] [StarRing K] [PartialOrder K] [Algebra ℂ K] [StarOrderedRing K] [StarModule ℂ K]
  {f : A →ₐ[ℂ] K} :
  LinearMap.IsPosMap f ↔ LinearMap.IsReal f :=
by
  have : LinearMap.IsPosMap f ↔ LinearMap.IsPosMap f.toLinearMap := by rfl
  refine ⟨λ h => isReal_of_isPosMap_of_starAlgEquiv_piMat φ (this.mp h), λ h => ?_⟩
  let f' : A →⋆ₐ[ℂ] K := StarAlgHom.mk f h
  have : f = f' := rfl
  rw [this]
  exact StarAlgHom.isPosMap hA _
