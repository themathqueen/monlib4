/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.Ips.Functional
import Monlib.LinearAlgebra.Matrix.PosDefRpow
import Monlib.LinearAlgebra.Mul''
import Monlib.LinearAlgebra.Ips.Basic
import Monlib.LinearAlgebra.PiDirectSum
import Monlib.LinearAlgebra.ToMatrixOfEquiv

/-!

# The inner product space on finite dimensional C*-algebras

This file contains some basic results on the inner product space on finite dimensional C*-algebras.

-/


open scoped TensorProduct Functional

/-- A lemma that states the right multiplication property of a linear functional. -/
theorem linear_functional_right_hMul {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]
    [StarMul A] {φ : A →ₗ[R] R} (x y z : A) : φ (star (x * y) * z) = φ (star y * (star x * z)) := by
  rw [StarMul.star_mul, mul_assoc]

/-- A lemma that states the left multiplication property of a linear functional. -/
theorem linear_functional_left_hMul {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]
    [StarMul A] {φ : A →ₗ[R] R} (x y z : A) : φ (star x * (y * z)) = φ (star (star y * x) * z) := by
  rw [StarMul.star_mul, star_star, mul_assoc]

variable {k k₂ : Type _} [Fintype k] [Fintype k₂] [DecidableEq k] [DecidableEq k₂]
  {s : k → Type _} {s₂ : k₂ → Type*} [∀ i, Fintype (s i)] [∀ i, Fintype (s₂ i)]
  [∀ i, DecidableEq (s i)] [∀ i, DecidableEq (s₂ i)]
  {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} {φ : ∀ i, Module.Dual ℂ (Matrix (s₂ i) (s₂ i) ℂ)}
  -- [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]

open Matrix

open scoped Matrix BigOperators

/-- A function that returns the direct sum of matrices for each index of type 'i'. -/
noncomputable def Module.Dual.pi.matrixBlock (ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)) :
  ∀ i, Matrix (s i) (s i) ℂ :=
∑ i, includeBlock (ψ i).matrix

-- /-- A function that returns a direct sum matrix. -/
-- noncomputable def Module.Dual.pi.matrix (ψ : ∀ i, Matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ) :
--   Matrix (Σ i, s i) (Σ i, s i) ℂ :=
-- blockDiagonal' (Module.Dual.pi.matrixBlock ψ)

open scoped InnerProductSpace

omit [DecidableEq k] in
/--
A lemma that states the inner product of two direct sum matrices is the sum of the inner products of their components. -/
theorem inner_pi_eq_sum [∀ i, (ψ i).IsFaithfulPosMap] (x y : PiMat ℂ k s) :
    ⟪x, y⟫_ℂ = ∑ i, ⟪x i, y i⟫_ℂ :=
  rfl

theorem blockDiagonal'_includeBlock_trace' {R k : Type _} [CommSemiring R] [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    (j : k) (x : Matrix (s j) (s j) R) :
    (blockDiagonal' (includeBlock x)).trace = x.trace :=
  by
  calc
    (blockDiagonal' (includeBlock x)).trace
      = ∑ i, (includeBlock x i).trace :=
      by simp_rw [Matrix.trace, Matrix.diag, blockDiagonal'_apply, dif_pos,
      Finset.sum_sigma']; rfl
    _ = ∑ i, ∑ a, includeBlock x i a a := rfl
    _ = ∑ i, ∑ a, dite (j = i) (fun h => by rw [← h]; exact x)
      (fun _ => (0 : Matrix (s i) (s i) R)) a a :=
      by simp_rw [includeBlock_apply]; rfl
    _ = ∑ i, ∑ a, dite (j = i) (fun h =>
        (by rw [← h]; exact x : Matrix (s i) (s i) R) a a)
      (fun _ => (0 : R)) := by congr; ext; congr; ext; aesop
    _ = x.trace := by
        simp_rw [Finset.sum_dite_irrel, Finset.sum_const_zero,
          Finset.sum_dite_eq, Finset.mem_univ, if_true]
        rfl

theorem Module.Dual.pi.matrixBlock_apply {i : k} : Module.Dual.pi.matrixBlock ψ i = (ψ i).matrix :=
  by
  simp only [Module.Dual.pi.matrixBlock, Finset.sum_apply, includeBlock_apply, Finset.sum_dite_eq',
    Finset.mem_univ, if_true]
  rfl

-- /-- A function that returns a star algebra equivalence for each index of type 'i'. -/
-- def StarAlgEquiv.pi {𝕜 : Type _} [RCLike 𝕜] {k : Type _} [Fintype k] [DecidableEq k]
--     {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
--     (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) :
--     (PiMat 𝕜 k s) ≃⋆ₐ[𝕜] PiMat 𝕜 k s
--     where
--   toFun x i := f i (x i)
--   invFun x i := (f i).symm (x i)
--   left_inv a := by simp only [StarAlgEquiv.symm_apply_apply]
--   right_inv a := by simp only [StarAlgEquiv.apply_symm_apply]
--   map_add' a y := by
--     simp only [Pi.add_apply, map_add]
--     rfl
--   map_smul' r a := by
--     simp only [Pi.smul_apply, _root_.map_smul]
--     rfl
--   map_mul' a b := by
--     simp only [Pi.mul_apply, _root_.map_mul]
--     rfl
--   map_star' a := by
--     simp only [Pi.star_apply, map_star]
--     rfl

-- theorem StarAlgEquiv.pi_apply {𝕜 : Type _} [RCLike 𝕜] {k : Type _} [Fintype k] [DecidableEq k]
--     {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
--     (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) (x : PiMat 𝕜 k s)
--     (i : k) : StarAlgEquiv.pi f x i = f i (x i) :=
--   rfl

-- /-- the unitary element from the star algebraic equivalence -/
-- noncomputable def StarAlgEquiv.pi.unitary {𝕜 : Type _} [RCLike 𝕜] {k : Type _} [Fintype k]
--     [DecidableEq k] {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
--     (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) : ∀ i, unitaryGroup (s i) 𝕜 :=
--   fun i => (f i).of_matrix_unitary

-- theorem StarAlgEquiv.pi.unitary_apply {𝕜 : Type _} [RCLike 𝕜] {k : Type _} [Fintype k]
--     [DecidableEq k] {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
--     (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) (a : k) :
--     (StarAlgEquiv.pi.unitary f) a = (f a).of_matrix_unitary :=
--   rfl

-- /-- any decomposable $^*$-isomorphism is an inner automorphism -/
-- theorem StarAlgEquiv.of_pi_is_inner {𝕜 : Type _} [RCLike 𝕜] {k : Type _} [Fintype k]
--     [DecidableEq k] {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
--     (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) :
--     unitary.innerAutStarAlg 𝕜 (unitary.pi (StarAlgEquiv.pi.unitary f)) = StarAlgEquiv.pi f :=
-- by
--   simp_rw [StarAlgEquiv.ext_iff, unitary.innerAutStarAlg_apply, Function.funext_iff, Pi.mul_apply]
--   simp only [unitary.pi_apply, unitary.coe_star, Pi.star_apply, unitary.pi_apply, StarAlgEquiv.pi_apply,
--     StarAlgEquiv.pi.unitary_apply]
--   intros a_1 i
--   rw [← unitary.coe_star, ← @unitary.innerAutStarAlg_apply 𝕜 _ _ _ _ _ (f _).of_matrix_unitary (a_1 _)]
--   congr
--   exact StarAlgEquiv.eq_innerAut _

def inclPi {i : k} (x : s i → ℂ) : (Σ j, s j) → ℂ := fun j =>
  dite (i = j.1) (fun h => x (by rw [h]; exact j.2)) fun _ => 0

def exclPi (x : (Σ j, s j) → ℂ) (i : k) : s i → ℂ := fun j => x ⟨i, j⟩

omit [Fintype k] [DecidableEq k] in
private theorem pi.forall_left_mul (x y : PiMat ℂ k s) :
    (∀ a, a * x = a * y) ↔ x = y := by
  constructor
  · intro h
    specialize h 1
    simp_rw [one_mul] at h
    exact h
  · rintro rfl a
    rfl

theorem Module.Dual.pi.apply'' (ψ : ∀ i, Matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ)
    (x : PiMat ℂ k s) :
    Module.Dual.pi ψ x = (blockDiagonal' (Module.Dual.pi.matrixBlock ψ) * blockDiagonal' x).trace :=
  by
  simp_rw [Module.Dual.pi.apply', Module.Dual.pi.matrixBlock, ← blockDiagonal'AlgHom_apply,
    map_sum, Finset.sum_mul, trace_sum]

-- theorem StarAlgEquiv.pi_is_trace_preserving
--     (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ) (x : PiMat ℂ k s) :
--     (blockDiagonal'AlgHom ((StarAlgEquiv.pi f) x)).trace = (blockDiagonal'AlgHom x).trace :=
--   by
--   rw [matrix_eq_sum_includeBlock ((StarAlgEquiv.pi f) x)]
--   nth_rw 2 [matrix_eq_sum_includeBlock x]
--   simp only [map_sum, trace_sum]
--   simp_rw [blockDiagonal'AlgHom_apply, blockDiagonal'_includeBlock_trace,
--     StarAlgEquiv.pi_apply, StarAlgEquiv.trace_preserving]

-- theorem StarAlgEquiv.pi_symm_apply_apply (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ)
--     (x : PiMat ℂ k s) :
--     (StarAlgEquiv.pi fun i => (f i).symm) ((StarAlgEquiv.pi f) x) = x :=
--   by
--   ext1
--   simp only [StarAlgEquiv.pi_apply, StarAlgEquiv.symm_apply_apply]

theorem Module.Dual.pi.apply_eq_of (ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ))
    (x : PiMat ℂ k s)
    (h : ∀ a, Module.Dual.pi ψ a = (blockDiagonal' x * blockDiagonal' a).trace) :
    x = Module.Dual.pi.matrixBlock ψ := by
  ext1 x_1
  simp only [Module.Dual.pi.matrixBlock_apply]
  apply Module.Dual.apply_eq_of
  intro a
  let a' := includeBlock a
  have ha' : a = a' x_1 := by simp only [a', includeBlock_apply_same]
  specialize h a'
  simp_rw [ha', ← Module.Dual.pi.apply_single_block, ← Pi.mul_apply, ←
    blockDiagonal'_includeBlock_trace, ← ha', Pi.mul_apply, ← ha']
  simp only [← blockDiagonal'AlgHom_apply, ← _root_.map_mul, a', hMul_includeBlock] at h
  exact h

-- theorem StarAlgEquiv.pi_symm_apply_eq (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ)
--     (x y : PiMat ℂ k s) :
--     StarAlgEquiv.pi (fun i => (f i).symm) x = y ↔ x = StarAlgEquiv.pi f y :=
--   by
--   constructor <;> rintro rfl <;> ext1 <;> simp only [StarAlgEquiv.pi_apply]
--   · rw [StarAlgEquiv.apply_symm_apply]
--   · rw [StarAlgEquiv.symm_apply_apply]

theorem unitary.inj_hMul {A : Type _} [Monoid A] [StarMul A] (U : unitary A) (x y : A) :
    x = y ↔ x * U = y * U := by
  rw [IsUnit.mul_left_inj]
  · rw [← unitary.val_toUnits_apply]
    exact (unitary.toUnits U).isUnit

section SingleBlock

/-!
  ## Section `single_block`
-/


variable {n n₂ : Type _} [DecidableEq n] [DecidableEq n₂] [Fintype n] [Fintype n₂]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} {ψ : Module.Dual ℂ (Matrix n₂ n₂ ℂ)}

namespace Module.Dual.IsFaithfulPosMap

open scoped ComplexOrder

theorem inner_eq  [φ.IsFaithfulPosMap] (x y : Matrix n n ℂ) :
  ⟪x, y⟫_ℂ = φ (xᴴ * y) :=
rfl

theorem inner_eq' (hφ : φ.IsFaithfulPosMap) (x y : Matrix n n ℂ) :
  ⟪x, y⟫_ℂ = (φ.matrix * xᴴ * y).trace := by
rw [inner_eq, φ.apply, Matrix.mul_assoc]

def matrixIsPosDef (hφ : φ.IsFaithfulPosMap) : PosDef φ.matrix :=
φ.isFaithfulPosMap_iff_of_matrix.mp hφ

theorem hMul_right (hφ : φ.IsFaithfulPosMap) (x y z : Matrix n n ℂ) :
    φ (xᴴ * (y * z)) = φ ((x * (φ.matrix * zᴴ * φ.matrix⁻¹))ᴴ * y) :=
  by
  haveI := (hφ.matrixIsPosDef).invertible
  simp_rw [φ.apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hφ.matrixIsPosDef.1.eq, hφ.matrixIsPosDef.inv.1.eq, ← Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_inv_cancel_left_of_invertible]
  rw [Matrix.trace_mul_cycle', Matrix.mul_assoc, ← Matrix.trace_mul_cycle', Matrix.mul_assoc]

theorem inner_left_hMul [φ.IsFaithfulPosMap] (x y z : Matrix n n ℂ) :
  ⟪x * y, z⟫_ℂ = ⟪y, xᴴ * z⟫_ℂ :=
linear_functional_right_hMul _ _ _

theorem inner_right_hMul [φ.IsFaithfulPosMap] (x y z : Matrix n n ℂ) :
  ⟪x, y * z⟫_ℂ = ⟪yᴴ * x, z⟫_ℂ :=
linear_functional_left_hMul _ _ _

theorem inner_left_conj (hφ : φ.IsFaithfulPosMap) (x y z : Matrix n n ℂ) :
  ⟪x, y * z⟫_ℂ = ⟪x * (φ.matrix * zᴴ * φ.matrix⁻¹), y⟫_ℂ :=
hφ.hMul_right _ _ _

theorem hMul_left (hφ : φ.IsFaithfulPosMap) (x y z : Matrix n n ℂ) :
    φ ((x * y)ᴴ * z) = φ (xᴴ * (z * (φ.matrix * yᴴ * φ.matrix⁻¹))) :=
by rw [← inner_eq, ← inner_conj_symm, inner_left_conj, inner_conj_symm]; rfl

theorem inner_right_conj (hφ : φ.IsFaithfulPosMap) (x y z : Matrix n n ℂ) :
  ⟪x * y, z⟫_ℂ = ⟪x, z * (φ.matrix * yᴴ * φ.matrix⁻¹)⟫_ℂ :=
hφ.hMul_left _ _ _

theorem adjoint_eq (hφ : φ.IsFaithfulPosMap) :
  LinearMap.adjoint φ = (Algebra.linearMap ℂ (Matrix n n ℂ) : ℂ →ₗ[ℂ] Matrix n n ℂ) :=
by
  rw [LinearMap.ext_iff]
  intro x
  apply @ext_inner_right ℂ
  intro y
  rw [LinearMap.adjoint_inner_left, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
    inner_smul_left, inner_eq, conjTranspose_one, Matrix.one_mul]
  rfl

/-- The adjoint of a star-algebraic equivalence $f$ on matrix algebras is given by
  $$f^*\colon x \mapsto f^{-1}(x Q) Q^{-1},$$
  where $Q$ is `hφ.matrix`. -/
theorem starAlgEquiv_adjoint_eq (hφ : φ.IsFaithfulPosMap)
  (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) (x : Matrix n n ℂ) :
  (LinearMap.adjoint (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ).toLinearMap :
          Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
      x =
    (f.symm (x * φ.matrix) : Matrix n n ℂ) * φ.matrix⁻¹ :=
by
  haveI := hφ.matrixIsPosDef.invertible
  apply @ext_inner_left ℂ
  intro a
  simp_rw [LinearMap.adjoint_inner_right, StarAlgEquiv.toLinearMap_apply]
  obtain ⟨U, rfl⟩ := f.of_matrix_is_inner
  simp_rw [innerAutStarAlg_apply, innerAutStarAlg_symm_apply, Matrix.mul_assoc]
  nth_rw 1 [← Matrix.mul_assoc φ.matrix]
  nth_rw 2 [← Matrix.mul_assoc]
  rw [inner_left_conj, inner_right_hMul]
  simp_rw [conjTranspose_mul, hφ.matrixIsPosDef.1.eq, hφ.matrixIsPosDef.inv.1.eq, ←
    star_eq_conjTranspose, ← unitaryGroup.star_coe_eq_coe_star, star_star,
    Matrix.mul_inv_cancel_left_of_invertible, Matrix.mul_assoc, mul_inv_of_invertible,
    Matrix.mul_one]

theorem starAlgEquiv_unitary_commute_iff [φ.IsFaithfulPosMap]
    (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    Commute φ.matrix f.of_matrix_unitary ↔ f φ.matrix = φ.matrix :=
  by
  rw [Commute, SemiconjBy]
  nth_rw 3 [← StarAlgEquiv.eq_innerAut f]
  rw [innerAutStarAlg_apply, ← unitaryGroup.star_coe_eq_coe_star]
  nth_rw 2 [unitaryGroup.injective_hMul f.of_matrix_unitary]
  simp_rw [Matrix.mul_assoc, UnitaryGroup.star_mul_self, Matrix.mul_one, eq_comm]

/-- Let `f` be a  star-algebraic equivalence on matrix algebras. Then tfae:

* `f φ.matrix = φ.matrix`,
* `f.adjoint = f⁻¹`,
* `φ ∘ f = φ`,
* `∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ`,
* `∀ x, ‖f x‖ = ‖x‖`,
* `φ.matrix` commutes with `f.unitary`.
-/
theorem starAlgEquiv_is_isometry_tFAE [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    List.TFAE
      [f φ.matrix = φ.matrix,
        (LinearMap.adjoint (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ).toLinearMap :
              Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
          f.symm.toLinearMap,
        φ ∘ₗ f.toLinearMap = φ, ∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ,
        ∀ x : Matrix n n ℂ, ‖f x‖ = ‖x‖, Commute φ.matrix f.of_matrix_unitary] :=
  by
  tfae_have 5 ↔ 2
  · simp_rw [InnerProductSpace.Core.norm_eq_sqrt_inner,
      Real.sqrt_inj inner_self_nonneg inner_self_nonneg,
      ← Complex.ofReal_inj]
    have : ∀ x : Matrix n n ℂ, (RCLike.re ⟪x, x⟫_ℂ : ℂ) = ⟪x, x⟫_ℂ := fun x => inner_self_ofReal_re x
      -- inner_self_ofReal_re (f ?_ : Matrix n n ℂ),
    simp_rw [this, ← @sub_eq_zero _ _ _ (⟪_, _⟫_ℂ)]
    have :
      ∀ x y,
        ⟪f x, f y⟫_ℂ - ⟪x, y⟫_ℂ =
          ⟪(LinearMap.adjoint f.toLinearMap ∘ₗ f.toLinearMap - 1) x, y⟫_ℂ :=
      by
      intro x y
      simp only [LinearMap.sub_apply, LinearMap.one_apply, inner_sub_left, LinearMap.comp_apply,
        LinearMap.adjoint_inner_left, StarAlgEquiv.toLinearMap_apply]
    simp_rw [this, inner_map_self_eq_zero, sub_eq_zero, StarAlgEquiv.comp_eq_iff,
      LinearMap.one_comp]
  rw [tfae_5_iff_2]
  tfae_have 4 ↔ 3
  · simp_rw [inner_eq, ← star_eq_conjTranspose, ← map_star f, ← _root_.map_mul f,
      LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply]
    refine' ⟨fun h x => _, fun h x y => h _⟩
    rw [← Matrix.one_mul x, ← star_one]
    exact h _ _
  rw [tfae_4_iff_3]
  haveI :=  hφ.matrixIsPosDef.invertible
  simp_rw [LinearMap.ext_iff, starAlgEquiv_adjoint_eq, LinearMap.comp_apply,
    StarAlgEquiv.toLinearMap_apply, mul_inv_eq_iff_eq_mul_of_invertible,
    φ.apply, StarAlgEquiv.symm_apply_eq, _root_.map_mul,
    StarAlgEquiv.apply_symm_apply, ← forall_left_hMul φ.matrix, @eq_comm _ φ.matrix]
  tfae_have 1 ↔ 2
  · rw [iff_self]; trivial
  tfae_have 1 → 3
  · intro i x
    nth_rw 1 [← i]
    rw [← _root_.map_mul, f.trace_preserving]
  tfae_have 3 → 1
  · intro i
    simp_rw [← f.symm.trace_preserving (φ.matrix * f _), _root_.map_mul,
      StarAlgEquiv.symm_apply_apply, ← φ.apply, @eq_comm _ _ (φ _)] at i
    -- obtain ⟨Q, hQ, h⟩ := Module.Dual.eq_trace_unique φ
    -- have := h _ i
    -- rw [StarAlgEquiv.symm_apply_eq] at this
    have := Module.Dual.apply_eq_of φ _ i
    rw [StarAlgEquiv.symm_apply_eq] at this
    exact this.symm
  rw [starAlgEquiv_unitary_commute_iff]
  tfae_finish

protected noncomputable def basis (hφ : φ.IsFaithfulPosMap) : Basis (n × n) ℂ (Matrix n n ℂ) :=
  by
  let hQ := hφ.matrixIsPosDef
  refine' Basis.mk _ _
  · exact fun ij => stdBasisMatrix ij.1 ij.2 1 * hφ.matrixIsPosDef.rpow (-(1 / 2))
  · have := (stdBasis ℂ n n).linearIndependent
    simp_rw [LinearIndependent, LinearMap.ker_eq_bot, injective_iff_map_eq_zero,
      Finsupp.linearCombination_apply, Finsupp.sum] at this ⊢
    simp_rw [← smul_mul_assoc, ← Finset.sum_mul]
    by_cases h : IsEmpty n
    · haveI := h
      simp only [eq_iff_true_of_subsingleton, forall_const]
    rw [not_isEmpty_iff] at h
    have t1 :
      ∀ a : n × n →₀ ℂ,
        (∑ x : n × n in a.support, a x • (stdBasisMatrix x.fst x.snd 1 : Matrix n n ℂ)) *
              hQ.rpow (-(1 / 2)) =
            0 ↔
          (∑ x : n × n in a.support, a x • (stdBasisMatrix x.fst x.snd 1 : Matrix n n ℂ)) *
                hQ.rpow (-(1 / 2)) *
              hQ.rpow (1 / 2) =
            0 * hQ.rpow (1 / 2) :=
      by
      intro a
      constructor <;> intro h
      · rw [h]
      · simp_rw [mul_assoc, Matrix.PosDef.rpow_mul_rpow, neg_add_cancel,
          Matrix.PosDef.rpow_zero, Matrix.mul_one] at h
        rw [h, Matrix.zero_mul, MulZeroClass.zero_mul]
    simp_rw [t1, mul_assoc, Matrix.PosDef.rpow_mul_rpow, neg_add_cancel,
      Matrix.PosDef.rpow_zero, Matrix.zero_mul, Matrix.mul_one, ← stdBasis_eq_stdBasisMatrix ℂ,
      Prod.mk.eta]
    exact this
  · simp_rw [top_le_iff]
    ext x
    simp_rw [Submodule.mem_top, iff_true, mem_span_range_iff_exists_fun, ← smul_mul,
      ← Finset.sum_mul, ← Matrix.ext_iff, mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, stdBasisMatrix, smul_ite, smul_zero, ← Prod.mk.inj_iff, Prod.mk.eta,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_mul_assoc, one_mul]
    exists fun ij : n × n => (x * hQ.rpow (1 / 2) : Matrix n n ℂ) ij.1 ij.2
    simp_rw [smul_eq_mul, ← mul_apply, Matrix.mul_assoc, Matrix.PosDef.rpow_mul_rpow, add_neg_cancel,
      Matrix.PosDef.rpow_zero, Matrix.mul_one, forall₂_true_iff]

protected theorem basis_apply (hφ : φ.IsFaithfulPosMap) (ij : n × n) :
    hφ.basis ij = stdBasisMatrix ij.1 ij.2 (1 : ℂ) * hφ.matrixIsPosDef.rpow (-(1 / 2 : ℝ)) := by
  rw [IsFaithfulPosMap.basis, Basis.mk_apply]

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

protected noncomputable def toMatrixLinEquiv (hφ : φ.IsFaithfulPosMap) (hψ : ψ.IsFaithfulPosMap) :
  (Matrix n n ℂ →ₗ[ℂ] Matrix n₂ n₂ ℂ) ≃ₗ[ℂ] Matrix (n₂ × n₂) (n × n) ℂ :=
LinearMap.toMatrix hφ.basis hψ.basis

protected noncomputable def toMatrix (hφ : φ.IsFaithfulPosMap) :
    (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) ≃ₐ[ℂ] Matrix (n × n) (n × n) ℂ :=
  LinearMap.toMatrixAlgEquiv hφ.basis

theorem basis_is_orthonormal (hφ : φ.IsFaithfulPosMap) : Orthonormal ℂ  hφ.basis :=
  by
  rw [orthonormal_iff_ite]
  simp_rw [Module.Dual.IsFaithfulPosMap.basis_apply]
  simp_rw [inner_eq', conjTranspose_mul, (PosDef.rpow.isPosDef _ _).1.eq,
    stdBasisMatrix.star_one, Matrix.mul_assoc, ← Matrix.mul_assoc _ (stdBasisMatrix _ _ _),
    stdBasisMatrix_hMul, one_mul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul,
    boole_mul]
  let Q := φ.matrix
  let hQ :=  hφ.matrixIsPosDef
  have :
    ∀ i j : n,
      (Q * (hQ.rpow (-(1 / 2) : ℝ) * (stdBasisMatrix i j 1 * hQ.rpow (-(1 / 2) : ℝ)))).trace =
        ite (i = j) (1 : ℂ) (0 : ℂ) :=
    fun i j =>
    calc
      trace (Q * (hQ.rpow (-(1 / 2) : ℝ) * (stdBasisMatrix i j 1 * hQ.rpow (-(1 / 2) : ℝ)))) =
          trace (hQ.rpow (-(1 / 2) : ℝ) * hQ.rpow 1 * hQ.rpow (-(1 / 2) : ℝ) *
              stdBasisMatrix i j 1) :=
        by
        simp_rw [PosDef.rpow_one_eq_self, Matrix.mul_assoc]
        rw [← trace_mul_cycle', trace_mul_comm]
        simp_rw [Matrix.mul_assoc]
        rw [trace_mul_comm]
        simp_rw [Matrix.mul_assoc]
      _ = (hQ.rpow (-(1 / 2) + 1 + -(1 / 2) : ℝ) * stdBasisMatrix i j 1).trace := by
        simp_rw [PosDef.rpow_mul_rpow]
      _ = (hQ.rpow 0 * stdBasisMatrix i j 1).trace := by ring_nf
      _ = ite (i = j) 1 0 := by simp_rw [PosDef.rpow_zero, Matrix.one_mul, stdBasisMatrix.trace]
  simp_rw [this, ← ite_and, ← Prod.eq_iff_fst_eq_snd_eq, forall₂_true_iff]

protected noncomputable def orthonormalBasis (hφ : φ.IsFaithfulPosMap) :
    OrthonormalBasis (n × n) ℂ (Matrix n n ℂ) :=
   hφ.basis.toOrthonormalBasis hφ.basis_is_orthonormal

protected theorem orthonormalBasis_apply
  (hφ : φ.IsFaithfulPosMap) (ij : n × n) :
  (hφ.orthonormalBasis : OrthonormalBasis (n × n) ℂ (Matrix n n ℂ)) ij =
    stdBasisMatrix ij.1 ij.2 (1 : ℂ) *  hφ.matrixIsPosDef.rpow (-(1 / 2 : ℝ)) :=
  by
  rw [← IsFaithfulPosMap.basis_apply, IsFaithfulPosMap.orthonormalBasis,
    Basis.coe_toOrthonormalBasis]

theorem inner_coord (hφ : φ.IsFaithfulPosMap) (ij : n × n) (y : Matrix n n ℂ) :
    ⟪(hφ.orthonormalBasis : OrthonormalBasis _ _ _) ij, y⟫_ℂ =
      (y *  hφ.matrixIsPosDef.rpow (1 / 2)) ij.1 ij.2 :=
  by
  let Q := φ.matrix
  let hQ :=  hφ.matrixIsPosDef
  simp_rw [inner_eq', hφ.orthonormalBasis_apply, conjTranspose_mul,
    (Matrix.PosDef.rpow.isPosDef hQ _).1.eq, ← Matrix.mul_assoc, stdBasisMatrix_conjTranspose,
    star_one]
  have :=
    calc
      Q * hQ.rpow (-(1 / 2)) = hQ.rpow 1 * hQ.rpow (-(1 / 2)) := by
        rw [Matrix.PosDef.rpow_one_eq_self]
      _ = hQ.rpow (1 + -(1 / 2)) := by rw [Matrix.PosDef.rpow_mul_rpow]
      _ = hQ.rpow (1 / 2) := by ring_nf
  rw [this]
  simp_rw [trace_iff, mul_apply, stdBasisMatrix, mul_boole, ite_and]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, MulZeroClass.zero_mul]
  simp_rw [mul_comm]

protected theorem basis_repr_apply (hφ : φ.IsFaithfulPosMap) (x : Matrix n n ℂ) (ij : n × n) :
     hφ.basis.repr x ij = ⟪hφ.basis ij, x⟫_ℂ :=
  by
  rw [hφ.basis_apply, ← hφ.orthonormalBasis_apply, ←
    OrthonormalBasis.repr_apply_apply]
  rfl

set_option synthInstance.maxHeartbeats 40000 in
protected theorem toMatrixLinEquiv_symm_apply (hφ : φ.IsFaithfulPosMap) (hψ : ψ.IsFaithfulPosMap)
    (x : Matrix (n₂ × n₂) (n × n) ℂ) :
     (hφ.toMatrixLinEquiv hψ).symm x =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (x (i, j) (k, l) : ℂ) • | hψ.basis (i, j)⟩⟨ hφ.basis (k, l)| :=
  by

  rw [IsFaithfulPosMap.toMatrixLinEquiv, LinearMap.ext_iff]
  intro a
  simp_rw [LinearMap.toMatrix_symm, toLin_apply, mulVec, dotProduct, IsFaithfulPosMap.basis_repr_apply,
    ContinuousLinearMap.coe_sum,
    LinearMap.sum_apply, ContinuousLinearMap.coe_smul,
    LinearMap.smul_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    IsFaithfulPosMap.basis_apply, Finset.sum_smul]
  symm
  repeat'
    nth_rw 1 [← Finset.sum_product']
    rw [Finset.univ_product_univ]
    apply Finset.sum_congr rfl
    intro ij _
  simp_rw [smul_smul]

-- lemma toMatrixLinEquiv_eq_toMatrix (hφ : φ.IsFaithfulPosMap) :
--   hφ.toMatrixLinEquiv hφ = hφ.toMatrix :=
-- rfl

@[simp]
lemma _root_.AlgEquiv.toLinearEquiv_coe {R M₁ M₂ : Type*} [CommSemiring R]
  [Semiring M₁] [Algebra R M₁] [Semiring M₂] [Algebra R M₂]
  (φ : M₁ ≃ₐ[R] M₂) :
  φ.toLinearEquiv = φ :=
rfl

set_option synthInstance.maxHeartbeats 40000 in
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
protected theorem toMatrix_symm_apply (hφ : φ.IsFaithfulPosMap)
    (x : Matrix (n × n) (n × n) ℂ) :
     hφ.toMatrix.symm x =
      ∑ i : n, ∑ j : n, ∑ k : n, ∑ l : n,
        (x (i, j) (k, l) : ℂ) • | hφ.basis (i, j)⟩⟨ hφ.basis (k, l)| :=
hφ.toMatrixLinEquiv_symm_apply _ _

end Module.Dual.IsFaithfulPosMap

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

set_option synthInstance.maxHeartbeats 40000 in
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem Module.Dual.eq_rankOne_of_faithful_pos_map (hφ : φ.IsFaithfulPosMap)
  (hψ : ψ.IsFaithfulPosMap)
  (x : Matrix n n ℂ →ₗ[ℂ] Matrix n₂ n₂ ℂ) :
  x =
    ∑ i, ∑ j, ∑ k, ∑ l,
      hφ.toMatrixLinEquiv hψ x (i, j) (k, l) • |hψ.basis (i, j)⟩⟨ hφ.basis (k, l)| :=
by rw [← Module.Dual.IsFaithfulPosMap.toMatrixLinEquiv_symm_apply, LinearEquiv.symm_apply_apply]

end SingleBlock

---------
section DirectSum

/-! # Section direct_sum -/


theorem LinearMap.sum_single_comp_proj {R : Type _} {ι : Type _} [Fintype ι] [DecidableEq ι]
    [Semiring R] {φ : ι → Type _} [∀ i : ι, AddCommMonoid (φ i)] [∀ i : ι, Module R (φ i)] :
    ∑ i : ι, LinearMap.single _ _ i ∘ₗ LinearMap.proj i = (LinearMap.id : (∀ i, φ i) →ₗ[R] ∀ i, φ i) :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.sum_apply, LinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.coe_single, Pi.single, Function.funext_iff, Finset.sum_apply,
    Function.update, Pi.zero_apply, Finset.sum_dite_eq, Finset.mem_univ, if_true]
  intro _ _; trivial

omit [(i : k) → Fintype (s i)] [(i : k₂) → Fintype (s₂ i)]
  [(i : k) → DecidableEq (s i)] [(i : k₂) → DecidableEq (s₂ i)] in
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (r p) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (r p) -/
theorem LinearMap.lrsum_eq_single_proj_lrcomp
    (f : (PiMat ℂ k s) →ₗ[ℂ] PiMat ℂ k₂ s₂) :
    ∑ r, ∑ p,
        LinearMap.single _ _ r ∘ₗ LinearMap.proj r ∘ₗ f ∘ₗ LinearMap.single _ _ p ∘ₗ LinearMap.proj p =
      f :=
  calc
    ∑ r, ∑ p,
          LinearMap.single _ _ r ∘ₗ LinearMap.proj r ∘ₗ f ∘ₗ LinearMap.single _ _ p ∘ₗ LinearMap.proj p =
        (∑ r, LinearMap.single _ _ r ∘ₗ LinearMap.proj r) ∘ₗ
          f ∘ₗ ∑ p, LinearMap.single _ _ p ∘ₗ LinearMap.proj p :=
      by simp_rw [LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.comp_assoc]
    _ = LinearMap.id ∘ₗ f ∘ₗ LinearMap.id := by simp_rw [LinearMap.sum_single_comp_proj]
    _ = f := by rw [LinearMap.id_comp, LinearMap.comp_id]

namespace Module.Dual.pi.IsFaithfulPosMap

omit [DecidableEq k] in
theorem inner_eq [∀ i, (ψ i).IsFaithfulPosMap] (x y : PiMat ℂ k s) :
    ⟪x, y⟫_ℂ = Module.Dual.pi ψ (star x * y) :=
  rfl

omit [DecidableEq k] in
theorem inner_eq' [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x y : PiMat ℂ k s) :
    ⟪x, y⟫_ℂ = ∑ i, ((ψ i).matrix * (x i)ᴴ * y i).trace := by
  simp only [inner_eq, Module.Dual.pi.apply, Pi.mul_apply,
    Matrix.star_eq_conjTranspose, Pi.star_apply, Matrix.mul_assoc]

omit [DecidableEq k] in
theorem inner_left_hMul [∀ i, (ψ i).IsFaithfulPosMap]
    (x y z : PiMat ℂ k s) : ⟪x * y, z⟫_ℂ = ⟪y, star x * z⟫_ℂ :=
  @linear_functional_right_hMul _ _ _ _ _ _ (Module.Dual.pi ψ) _ _ _

theorem hMul_right (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (x y z : PiMat ℂ k s) :
    Module.Dual.pi ψ (star x * (y * z)) =
      Module.Dual.pi ψ
        (star (x * (Module.Dual.pi.matrixBlock ψ * star z * (Module.Dual.pi.matrixBlock ψ)⁻¹)) *
          y) :=
  by
  letI := fun i => Fact.mk (hψ i)
  rw [← inner_eq]
  simp only [inner_eq']
  simp_rw [← Module.Dual.IsFaithfulPosMap.inner_eq', Pi.mul_apply,
    Module.Dual.IsFaithfulPosMap.inner_left_conj, ← inner_eq, inner_pi_eq_sum, Pi.mul_apply,
    Pi.inv_apply, Pi.star_apply, Matrix.star_eq_conjTranspose,
    Module.Dual.pi.matrixBlock_apply]

theorem inner_left_conj [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x y z : PiMat ℂ k s) :
    ⟪x, y * z⟫_ℂ =
      ⟪x * (Module.Dual.pi.matrixBlock ψ * star z * (Module.Dual.pi.matrixBlock ψ)⁻¹), y⟫_ℂ :=
  hMul_right (fun i => (hψ i)) _ _ _

omit [DecidableEq k] in
theorem inner_right_hMul [∀ i, (ψ i).IsFaithfulPosMap]
    (x y z : PiMat ℂ k s) : ⟪x, y * z⟫_ℂ = ⟪star y * x, z⟫_ℂ :=
  @linear_functional_left_hMul _ _ _ _ _ _ (Module.Dual.pi ψ) _ _ _

omit [DecidableEq k] in
theorem adjoint_eq [hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
    LinearMap.adjoint (Module.Dual.pi ψ) = Algebra.linearMap ℂ (PiMat ℂ k s) :=
  by
  rw [LinearMap.ext_iff]
  intro x
  apply @ext_inner_right ℂ
  intro y
  rw [LinearMap.adjoint_inner_left, Algebra.linearMap_apply]
  simp_rw [inner_pi_eq_sum, Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
    InnerProductSpace.Core.inner_smul_left, Module.Dual.IsFaithfulPosMap.inner_eq,
    conjTranspose_one, Matrix.one_mul, ← Finset.mul_sum]
  rfl

protected noncomputable def basis (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    Basis (Σ i, s i × s i) ℂ (PiMat ℂ k s) :=
  Pi.basis fun i => (hψ i).basis

protected theorem basis_apply (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (ijk : Σ i, s i × s i) :
    Module.Dual.pi.IsFaithfulPosMap.basis hψ ijk =
      includeBlock
        (stdBasisMatrix ijk.2.1 ijk.2.2 1 * (hψ ijk.1).matrixIsPosDef.rpow (-(1 / 2 : ℝ))) :=
  by
  simp only [Module.Dual.pi.IsFaithfulPosMap.basis, Pi.basis_apply, Function.funext_iff, ← Matrix.ext_iff]
  intro i j k
  simp only [Pi.single, Pi.mul_apply, includeBlock_apply, mul_apply,
    dite_apply, hMul_dite, MulZeroClass.mul_zero, Pi.zero_apply, Function.update,
    Matrix.cast_apply]
  simp_rw [@eq_comm _ i]
  split_ifs with h
  · rw [← Module.Dual.IsFaithfulPosMap.basis_apply (hψ _)]
    aesop
  · simp only [zero_apply]

protected theorem basis_apply' (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (i : k) (j l : s i) :
    Module.Dual.pi.IsFaithfulPosMap.basis hψ ⟨i, (j, l)⟩ =
      includeBlock (stdBasisMatrix j l 1 * (hψ i).matrixIsPosDef.rpow (-(1 / 2 : ℝ))) :=
  Module.Dual.pi.IsFaithfulPosMap.basis_apply hψ _

theorem includeBlock_left_inner (hψ : ∀ i, (ψ i).IsFaithfulPosMap) {i : k}
    (x : Matrix (s i) (s i) ℂ) (y : PiMat ℂ k s) :
    ⟪includeBlock x, y⟫_ℂ = ⟪x, y i⟫_ℂ :=
calc ⟪includeBlock x, y⟫_ℂ = pi ψ (star (includeBlock x) * y) := rfl
  _ = pi ψ (includeBlock xᴴ * y) := by rw [includeBlock_conjTranspose]
  _ = pi ψ (includeBlock (xᴴ * y i)) := by rw [includeBlock_hMul]
  _ = ψ i (xᴴ * y i) := by rw [Module.Dual.pi.apply_single_block']
  _ = ⟪x, y i⟫_ℂ := rfl

theorem includeBlock_inner_same [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    {x y : Matrix (s i) (s i) ℂ} : ⟪includeBlock x, includeBlock y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [includeBlock_left_inner, includeBlock_apply_same]

theorem includeBlock_inner_same' [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i j : k}
    {x : Matrix (s i) (s i) ℂ} {y : Matrix (s j) (s j) ℂ} (h : i = j) :
    ⟪includeBlock x, includeBlock y⟫_ℂ = ⟪x, by rw [h]; exact y⟫_ℂ :=
  by
  simp_rw [includeBlock_left_inner, includeBlock_apply, h, dif_pos]
  rfl
theorem includeBlock_inner_block_left [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {j : k}
    {x : PiMat ℂ k s} {y : Matrix (s j) (s j) ℂ} {i : k} :
    ⟪includeBlock (x i), includeBlock y⟫_ℂ = if i = j then ⟪x j, y⟫_ℂ else 0 :=
by
  simp_rw [includeBlock_left_inner, includeBlock_apply]
  aesop

theorem includeBlock_inner_ne_same [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i j : k}
    {x : Matrix (s i) (s i) ℂ} {y : Matrix (s j) (s j) ℂ} (h : i ≠ j) :
    ⟪includeBlock x, includeBlock y⟫_ℂ = 0 := by
  simp only [includeBlock_left_inner, includeBlock_apply_ne_same _ h.symm, inner_zero_right]

omit [Fintype k] [DecidableEq k] in
protected theorem basis.apply_cast_eq_mpr (hψ : ∀ i, (ψ i).IsFaithfulPosMap) {i j : k}
    {a : s j × s j} (h : i = j) :
    (hψ i).basis (by rw [h]; exact a) = by rw [h]; exact (hψ j).basis a :=
  by
  simp only [eq_mpr_eq_cast, h]; aesop


protected theorem basis_is_orthonormal [hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
  -- letI := Module.Dual.pi.InnerProductSpace (hφ := hψ)
  @Orthonormal ℂ _ _
    (Module.Dual.PiNormedAddCommGroup (_hφ := hψ)).toSeminormedAddCommGroup

    (Module.Dual.pi.InnerProductSpace (hφ := hψ)) _
    (Module.Dual.pi.IsFaithfulPosMap.basis hψ) :=
by
  letI := (Module.Dual.PiNormedAddCommGroup (_hφ := hψ)).toSeminormedAddCommGroup
  rw [orthonormal_iff_ite]
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.basis_apply]
  intro i j
  rw [eq_comm, ite_eq_iff']
  constructor
  · rintro rfl
    simp_rw [includeBlock_inner_same, ← Module.Dual.IsFaithfulPosMap.basis_apply,
      orthonormal_iff_ite.mp ((hψ i.1).basis_is_orthonormal) i.snd,
      if_true]
  · intro h
    simp_rw [← Module.Dual.IsFaithfulPosMap.basis_apply]
    by_cases h' : i.fst = j.fst
    · simp_rw [Sigma.ext_iff, not_and_or, h', not_true, false_or] at h
      rw [← Sigma.eta i, ← Sigma.eta j]
      simp_rw [includeBlock_inner_same' h']
      rw [← Module.Dual.pi.IsFaithfulPosMap.basis.apply_cast_eq_mpr hψ h']
      simp only [orthonormal_iff_ite.mp (hψ _).basis_is_orthonormal i.snd]
      simp only [eq_mpr_eq_cast]
      rw [eq_comm, ite_eq_right_iff]
      intro hh
      simp only [hh, cast_heq, not_true_eq_false] at h
    · simp only [Module.Dual.pi.IsFaithfulPosMap.basis_apply, includeBlock_inner_ne_same h']

protected noncomputable def orthonormalBasis (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    OrthonormalBasis (Σ i, s i × s i) ℂ (PiMat ℂ k s) :=
  Basis.toOrthonormalBasis (Module.Dual.pi.IsFaithfulPosMap.basis hψ)
    (Module.Dual.pi.IsFaithfulPosMap.basis_is_orthonormal (hψ := hψ))

protected theorem orthonormalBasis_apply (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
    {ijk : Σ i, s i × s i} :
    (Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hψ : OrthonormalBasis _ _ _) ijk =
      includeBlock
        (stdBasisMatrix ijk.2.1 ijk.2.2 1 * (hψ ijk.1).matrixIsPosDef.rpow (-(1 / 2 : ℝ))) :=
  by
  rw [← Module.Dual.pi.IsFaithfulPosMap.basis_apply hψ]
  simp only [Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis, Basis.coe_toOrthonormalBasis]

protected theorem orthonormalBasis_apply' (hψ : ∀ i, (ψ i).IsFaithfulPosMap) {i : k}
    {j l : s i} :
    (Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hψ : OrthonormalBasis _ _ _) ⟨i, (j, l)⟩ =
      includeBlock (stdBasisMatrix j l 1 * (hψ i).matrixIsPosDef.rpow (-(1 / 2 : ℝ))) :=
  Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis_apply hψ

protected theorem inner_coord (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
  (ijk : Σ i, s i × s i)
  (y : PiMat ℂ k s) :
  ⟪Module.Dual.pi.IsFaithfulPosMap.basis hψ ijk, y⟫_ℂ =
    (y ijk.1 * (hψ ijk.1).matrixIsPosDef.rpow (1 / 2)) ijk.2.1 ijk.2.2 :=
by
simp_rw [Module.Dual.pi.IsFaithfulPosMap.basis_apply, includeBlock_left_inner, ←
  Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, Module.Dual.IsFaithfulPosMap.inner_coord]

omit [DecidableEq k] in
protected theorem basis_repr_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (x : PiMat ℂ k s) (ijk : Σ i, s i × s i) :
    (Module.Dual.pi.IsFaithfulPosMap.basis hψ).repr x ijk =
      ⟪(hψ ijk.1).basis ijk.2, x ijk.1⟫_ℂ :=
  by
  rw [Module.Dual.IsFaithfulPosMap.basis_apply, ←
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, ← OrthonormalBasis.repr_apply_apply]
  rfl

theorem MatrixBlock.isSelfAdjoint (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    IsSelfAdjoint (Module.Dual.pi.matrixBlock ψ) :=
  by
  ext x
  simp only [Pi.star_apply, Module.Dual.pi.matrixBlock_apply, star_eq_conjTranspose,
    (hψ x).matrixIsPosDef.1.eq]

noncomputable def matrixBlockInvertible (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    Invertible (Module.Dual.pi.matrixBlock ψ) :=
  by
  haveI := fun i => (hψ i).matrixIsPosDef.invertible
  apply Invertible.mk (Module.Dual.pi.matrixBlock ψ)⁻¹
  all_goals
    ext1
    simp_rw [Pi.mul_apply, Pi.inv_apply, Module.Dual.pi.matrixBlock_apply, Pi.one_apply]
  on_goal 1 => rw [inv_mul_of_invertible]
  rw [mul_inv_of_invertible]

theorem matrixBlock_inv_hMul_self [hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
    (Module.Dual.pi.matrixBlock ψ)⁻¹ * Module.Dual.pi.matrixBlock ψ = 1 :=
  by
  haveI := fun i => (hψ i).matrixIsPosDef.invertible
  ext1
  simp_rw [Pi.mul_apply, Pi.inv_apply, Module.Dual.pi.matrixBlock_apply, Pi.one_apply, inv_mul_of_invertible]

theorem matrixBlock_self_hMul_inv (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    Module.Dual.pi.matrixBlock ψ * (Module.Dual.pi.matrixBlock ψ)⁻¹ = 1 :=
  by
  haveI := fun i => (hψ i).matrixIsPosDef.invertible
  ext
  simp_rw [Pi.mul_apply, Pi.inv_apply, Module.Dual.pi.matrixBlock_apply, Pi.one_apply, mul_inv_of_invertible]

noncomputable def toMatrixLinEquiv (hψ : ∀ i, (ψ i).IsFaithfulPosMap)
  (hφ : ∀ i, (φ i).IsFaithfulPosMap) :
    ((PiMat ℂ k s) →ₗ[ℂ] (PiMat ℂ k₂ s₂)) ≃ₗ[ℂ]
      Matrix (Σ i, s₂ i × s₂ i) (Σ i, s i × s i) ℂ :=
LinearMap.toMatrix (Module.Dual.pi.IsFaithfulPosMap.basis hψ)
  (Module.Dual.pi.IsFaithfulPosMap.basis hφ)

noncomputable def toMatrix (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    ((PiMat ℂ k s) →ₗ[ℂ] PiMat ℂ k s) ≃ₐ[ℂ]
      Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ :=
  LinearMap.toMatrixAlgEquiv (Module.Dual.pi.IsFaithfulPosMap.basis hψ)

lemma toMatrixLinEquiv_eq_toMatrix (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
  toMatrixLinEquiv hψ hψ
    = (Module.Dual.pi.IsFaithfulPosMap.toMatrix hψ).toLinearEquiv :=
rfl

@[simps]
noncomputable def isBlockDiagonalBasis (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    Basis (Σ i, s i × s i) ℂ { x : Matrix (Σ i, s i) (Σ i, s i) ℂ // x.IsBlockDiagonal }
    where repr :=
    isBlockDiagonalPiAlgEquiv.toLinearEquiv.trans (Module.Dual.pi.IsFaithfulPosMap.basis hψ).repr

omit [DecidableEq k₂] in
theorem toMatrixLinEquiv_apply' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    [hφ : ∀ i, (φ i).IsFaithfulPosMap]
    (f : (PiMat ℂ k s) →ₗ[ℂ] PiMat ℂ k₂ s₂) (r : Σ r, s₂ r × s₂ r) (l : Σ r, s r × s r) :
    (toMatrixLinEquiv hψ hφ) f r l =
      (f (includeBlock ((hψ l.1).basis l.2)) r.1 * (hφ r.1).matrixIsPosDef.rpow (1 / 2))
        r.2.1 r.2.2 :=
by
  simp_rw [toMatrixLinEquiv, LinearMap.toMatrix_apply, IsFaithfulPosMap.basis_repr_apply, ←
    Module.Dual.IsFaithfulPosMap.inner_coord, IsFaithfulPosMap.basis_apply,
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, ← Module.Dual.IsFaithfulPosMap.basis_apply]

theorem toMatrix_apply' [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (f : (PiMat ℂ k s) →ₗ[ℂ] PiMat ℂ k s) (r l : Σ r, s r × s r) :
    (toMatrix fun i => (hψ i)) f r l =
      (f (includeBlock ((hψ l.1).basis l.2)) r.1 * (hψ r.1).matrixIsPosDef.rpow (1 / 2))
        r.2.1 r.2.2 :=
toMatrixLinEquiv_apply' _ _ _

-- theorem starAlgEquiv_adjoint_eq [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
--     (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ) (x : PiMat ℂ k s) :
--     LinearMap.adjoint (StarAlgEquiv.pi f).toLinearMap x =
--       (StarAlgEquiv.pi f).symm (x * Module.Dual.pi.matrixBlock ψ) *
--         (Module.Dual.pi.matrixBlock ψ)⁻¹ :=
--   by
--   letI := @matrixBlockInvertible _ _ _ _ _ _ ψ hψ
--   letI := fun i => (hψ i).matrixIsPosDef.invertible
--   apply @ext_inner_left ℂ
--   intro a
--   simp_rw [LinearMap.adjoint_inner_right, StarAlgEquiv.toLinearMap_apply]
--   rw [← StarAlgEquiv.of_pi_is_inner]
--   simp_rw [unitary.innerAutStarAlg_apply, unitary.innerAutStarAlg_symm_apply, mul_assoc]
--   symm
--   nth_rw 1 [← mul_assoc (Module.Dual.pi.matrixBlock ψ)]
--   nth_rw 1 [← mul_assoc]
--   symm
--   rw [inner_left_conj, inner_right_hMul]
--   simp_rw [StarMul.star_mul, IsSelfAdjoint.star_eq (MatrixBlock.isSelfAdjoint hψ), mul_assoc]
--   have t1 : Module.Dual.pi.matrixBlock ψ * (Module.Dual.pi.matrixBlock ψ)⁻¹ = 1 :=
--     by
--     ext1
--     simp only [Pi.mul_apply, Pi.inv_apply, Module.Dual.pi.matrixBlock_apply,
--       mul_inv_of_invertible, Pi.one_apply]
--   have t2 :=
--     calc
--       Module.Dual.pi.matrixBlock ψ * star (Module.Dual.pi.matrixBlock ψ)⁻¹ =
--           Module.Dual.pi.matrixBlock ψ * (Module.Dual.pi.matrixBlock ψ)⁻¹ :=
--         by
--         congr
--         simp only [Pi.inv_def, Pi.star_def, Module.Dual.pi.matrixBlock_apply,
--           star_eq_conjTranspose, (hψ _).matrixIsPosDef.1.eq,
--           (hψ _).matrixIsPosDef.inv.1.eq]
--       _ = 1 := t1
--   simp_rw [t1, ← mul_assoc (Module.Dual.pi.matrixBlock ψ), t2, mul_one, one_mul, unitary.coe_star,
--     star_star]

private theorem mul_inv_eq_iff_eq_mul_aux [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (b c : PiMat ℂ k s) :
    b * (Module.Dual.pi.matrixBlock ψ)⁻¹ = c ↔ b = c * Module.Dual.pi.matrixBlock ψ :=
  by
  constructor <;> rintro rfl <;> rw [mul_assoc]
  · rw [matrixBlock_inv_hMul_self, mul_one]
  · rw [matrixBlock_self_hMul_inv hψ, mul_one]

-- theorem starAlgEquiv_commute_iff [∀ i, (ψ i).IsFaithfulPosMap]
--     (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ) :
--     (Commute (Module.Dual.pi.matrixBlock ψ) fun i => StarAlgEquiv.pi.unitary f i) ↔
--       StarAlgEquiv.pi f (Module.Dual.pi.matrixBlock ψ) = Module.Dual.pi.matrixBlock ψ :=
--   by
--   symm
--   nth_rw 1 [← StarAlgEquiv.of_pi_is_inner]
--   rw [unitary.innerAutStarAlg_apply, unitary.coe_star]
--   rw [unitary.inj_hMul (unitary.pi (StarAlgEquiv.pi.unitary f))]
--   simp only [mul_assoc, unitary.coe_star_mul_self, mul_one, eq_comm, Commute, SemiconjBy,
--     Pi.mul_def, Pi.star_def]

-- theorem starAlgEquiv_is_isometry_tfae [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
--     [∀ i, Nontrivial (s i)] (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ) :
--     List.TFAE
--       [(StarAlgEquiv.pi f) (Module.Dual.pi.matrixBlock ψ) = Module.Dual.pi.matrixBlock ψ,
--         LinearMap.adjoint (StarAlgEquiv.pi f).toLinearMap =
--           (StarAlgEquiv.pi f).symm.toLinearMap,
--         Module.Dual.pi ψ ∘ₗ (StarAlgEquiv.pi f).toLinearMap = Module.Dual.pi ψ,
--         ∀ x y, ⟪(StarAlgEquiv.pi f) x, (StarAlgEquiv.pi f) y⟫_ℂ = ⟪x, y⟫_ℂ,
--         ∀ x : ∀ i, Matrix (s i) (s i) ℂ, ‖(StarAlgEquiv.pi f) x‖ = ‖x‖,
--         Commute (Module.Dual.pi.matrixBlock ψ) fun i => StarAlgEquiv.pi.unitary f i] :=
--   by
--   tfae_have 5 ↔ 2
--   · --simp_rw [List.TFAE.out (@general_starAlgEquiv_is_isometry_tfae _ _ _ _ _ ψ hψ (StarAlgEquiv.pi f)) 4 1]
--     have : ∀ x : PiMat ℂ k s, ‖x‖ = Real.sqrt (RCLike.re ⟪x, x⟫_ℂ) :=
--     fun x => norm_eq_sqrt_inner _
--     have this' : ∀ x : PiMat ℂ k s, (RCLike.re ⟪x, x⟫_ℂ : ℂ) = ⟪x, x⟫_ℂ :=
--     fun x => inner_self_re _
--     simp_rw [this, Real.sqrt_inj inner_self_nonneg inner_self_nonneg,
--       ← Complex.ofReal_inj, this', ← @sub_eq_zero _ _ _ ⟪_, _⟫_ℂ]
--     have :
--       ∀ x y,
--         ⟪(StarAlgEquiv.pi f) x, (StarAlgEquiv.pi f) y⟫_ℂ - ⟪x, y⟫_ℂ =
--           ⟪(LinearMap.adjoint (StarAlgEquiv.pi f).toLinearMap ∘ₗ
--                   (StarAlgEquiv.pi f).toLinearMap -
--                 1)
--               x,
--             y⟫_ℂ :=
--       by
--       intro x y
--       simp only [LinearMap.sub_apply, LinearMap.one_apply, inner_sub_left, LinearMap.comp_apply,
--         LinearMap.adjoint_inner_left, StarAlgEquiv.toLinearMap_apply]
--     simp_rw [this, inner_map_self_eq_zero, sub_eq_zero, StarAlgEquiv.comp_eq_iff,
--       LinearMap.one_comp]
--   rw [tfae_5_iff_2]
--   tfae_have 4 ↔ 3
--   · simp_rw [inner_eq, ← map_star (StarAlgEquiv.pi f), ← _root_.map_mul (StarAlgEquiv.pi f),
--       LinearMap.ext_iff, LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply]
--     refine' ⟨fun h x => _, fun h x y => h _⟩
--     rw [← one_mul x, ← star_one]
--     exact h _ _
--   rw [tfae_4_iff_3]
--   letI := @matrixBlockInvertible _ _ _ _ _ _ ψ hψ
--   simp_rw [LinearMap.ext_iff, starAlgEquiv_adjoint_eq f, LinearMap.comp_apply,
--     StarAlgEquiv.toLinearMap_apply, mul_inv_eq_iff_eq_mul_aux,
--     Module.Dual.pi.apply'', StarAlgEquiv.symm_apply_eq, _root_.map_mul,
--     StarAlgEquiv.apply_symm_apply, pi.forall_left_mul, @eq_comm _ (Module.Dual.pi.matrixBlock ψ), ←
--     blockDiagonal'AlgHom_apply, ← _root_.map_mul]
--   tfae_have 1 ↔ 2
--   · rw [iff_self_iff]; trivial
--   tfae_have 1 → 3
--   · intro i x
--     nth_rw 1 [← i]
--     simp_rw [← _root_.map_mul, StarAlgEquiv.pi_is_trace_preserving]
--   tfae_have 3 → 1
--   · intro i
--     simp_rw [←
--       StarAlgEquiv.pi_is_trace_preserving (fun i => (f i).symm)
--         (Module.Dual.pi.matrixBlock ψ * (StarAlgEquiv.pi f) _),
--       _root_.map_mul, StarAlgEquiv.pi_symm_apply_apply, blockDiagonal'AlgHom_apply, ←
--       Module.Dual.pi.apply'', @eq_comm _ _ (Module.Dual.pi ψ _)] at i
--     have := Module.Dual.pi.apply_eq_of ψ _ i
--     rw [StarAlgEquiv.pi_symm_apply_eq] at this
--     exact this.symm
--   tfae_have 5 ↔ 6
--   · rw [starAlgEquiv_commute_iff]
--   tfae_finish

end Module.Dual.pi.IsFaithfulPosMap

end DirectSum


variable {n : Type _} [Fintype n]

local notation "ℍ" => Matrix n n ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

local notation "L(" x ")" => x →L[ℂ] x

local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

open scoped Matrix

open Matrix


open scoped Kronecker Matrix BigOperators TensorProduct Functional

open Module.Dual
variable [DecidableEq n] {φ : Module.Dual ℂ (Matrix n n ℂ)}
  {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
  [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}



theorem inner_stdBasisMatrix_left [hφ : φ.IsFaithfulPosMap] (i j : n) (x : Matrix n n ℂ) :
    ⟪stdBasisMatrix i j (1 : ℂ), x⟫_ℂ = (x * φ.matrix) i j :=
  by
  simp only [IsFaithfulPosMap.inner_eq', stdBasisMatrix_conjTranspose, star_one]
  rw [Matrix.mul_assoc, ← trace_mul_cycle', Matrix.stdBasisMatrix_hMul_trace]

theorem inner_stdBasisMatrix_stdBasisMatrix [hφ : φ.IsFaithfulPosMap] (i j k l : n) :
    ⟪stdBasisMatrix i j (1 : ℂ), stdBasisMatrix k l (1 : ℂ)⟫_ℂ = ite (i = k) (φ.matrix l j) 0 :=
  by
  simp_rw [inner_stdBasisMatrix_left, mul_apply, stdBasisMatrix, boole_mul, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_ite_eq]
  simp_rw [@eq_comm _ (k : n) (i : n)]

--   $$m^*(x) = \sum_{i,j,k,l} x_{il}Q^{-1}_{kj}(e_{ij} \otimes_t e_{kl})$$ -/
theorem LinearMap.mul'_adjoint [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
    LinearMap.adjoint (LinearMap.mul' ℂ ℍ) x =
      ∑ i : n, ∑ j : n, ∑ k : n, ∑ l : n,
        (x i l * φ.matrix⁻¹ k j) • stdBasisMatrix i j 1 ⊗ₜ[ℂ] stdBasisMatrix k l 1 :=
by
  rw [TensorProduct.inner_ext_iff']
  intro a b
  rw [LinearMap.adjoint_inner_left, LinearMap.mul'_apply]
  simp_rw [sum_inner, inner_smul_left, TensorProduct.inner_tmul,
    inner_stdBasisMatrix_left, _root_.map_mul, starRingEnd_apply,
    ← conjTranspose_apply, hφ.matrixIsPosDef.inv.1.eq,
    mul_assoc, ← mul_assoc (φ.matrix⁻¹ _ _)]
  symm
  calc ∑ x_1 : n,
    ∑ x_2 : n, ∑ x_3 : n, ∑ x_4 : n,
      xᴴ x_4 x_1
    * (φ.matrix⁻¹ x_2 x_3 * (a * φ.matrix) x_1 x_2
    * (b * φ.matrix) x_3 x_4)
      = ∑ x_1 : n,
    ∑ x_3 : n, (∑ x_4 : n,
      (b * φ.matrix) x_3 x_4 * xᴴ x_4 x_1)
    * (∑ x_2 : n, (a * φ.matrix) x_1 x_2 * φ.matrix⁻¹ x_2 x_3) := ?_
    _ = ∑ x_1, ∑ x_3, (a * (φ.matrix * φ.matrix⁻¹)) x_1 x_3
      * (b * φ.matrix * xᴴ) x_3 x_1 := ?_
    _ = ∑ x_1, (a * b * φ.matrix * xᴴ) x_1 x_1 := ?_
    _ = ⟪x, a * b⟫_ℂ := ?_
  . congr
    ext
    rw [Finset.sum_comm]
    congr
    ext
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    repeat congr; ext
    ring_nf
  . repeat congr 1; ext1
    rw [← mul_assoc, Matrix.mul_apply, Matrix.mul_apply, mul_comm]
  . congr; ext
    letI := hφ.matrixIsPosDef.invertible
    rw [← Matrix.mul_apply, mul_inv_of_invertible, mul_one]
    simp_rw [← mul_assoc]
  . rw [← Matrix.trace_iff, IsFaithfulPosMap.inner_eq',
      Matrix.trace_mul_cycle, Matrix.trace_mul_comm, mul_assoc]

theorem Matrix.linearMap_ext_iff_inner_map [hφ : φ.IsFaithfulPosMap] {x y : l(ℍ)} :
    x = y ↔ ∀ u v : ℍ, ⟪x u, v⟫_ℂ = ⟪y u, v⟫_ℂ :=
  by
  simp_rw [LinearMap.ext_iff]
  refine' ⟨fun h u v => by rw [h], fun h a => _⟩
  apply @_root_.ext_inner_right ℂ _ _
  exact h _

theorem Matrix.linearMap_ext_iff_map_inner [hφ : φ.IsFaithfulPosMap] {x y : l(ℍ)} :
    x = y ↔ ∀ u v : ℍ, ⟪v, x u⟫_ℂ = ⟪v, y u⟫_ℂ :=
  by
  rw [@Matrix.linearMap_ext_iff_inner_map n _ _ φ]
  simp_rw [← inner_conj_symm _ (x _), ←
    inner_conj_symm (y _) _]
  exact
    ⟨fun h u v => by rw [h, starRingEnd_self_apply], fun h u v => by
      rw [← h, starRingEnd_self_apply]⟩

theorem Matrix.inner_conj_Q [hφ : φ.IsFaithfulPosMap] (a x : ℍ) :
    ⟪x, φ.matrix * a * φ.matrix⁻¹⟫_ℂ = ⟪x * aᴴ, 1⟫_ℂ :=
  by
  simp_rw [IsFaithfulPosMap.inner_eq', ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp_rw [← Matrix.mul_assoc,
    @inv_mul_of_invertible n ℂ _ _ _ φ.matrix hφ.matrixIsPosDef.invertible, Matrix.one_mul,
    conjTranspose_mul, Matrix.mul_one, conjTranspose_conjTranspose]
  rw [← Matrix.trace_mul_cycle, Matrix.mul_assoc]

theorem Matrix.inner_star_right [hφ : φ.IsFaithfulPosMap] (b y : ℍ) :
    ⟪b, y⟫_ℂ = ⟪1, bᴴ * y⟫_ℂ := by
  simp_rw [IsFaithfulPosMap.inner_eq', ← Matrix.mul_assoc, conjTranspose_one, Matrix.mul_one]

theorem Matrix.inner_star_left [hφ : φ.IsFaithfulPosMap] (a x : ℍ) :
    ⟪a, x⟫_ℂ = ⟪xᴴ * a, 1⟫_ℂ := by
  rw [← inner_conj_symm, Matrix.inner_star_right, inner_conj_symm]

theorem one_inner [hφ : φ.IsFaithfulPosMap] (a : ℍ) : ⟪1, a⟫_ℂ = (φ.matrix * a).trace := by
  rw [IsFaithfulPosMap.inner_eq', conjTranspose_one, Matrix.mul_one]

theorem Module.Dual.IsFaithfulPosMap.map_star (hφ : φ.IsFaithfulPosMap) (x : ℍ) :
    φ (star x) = star (φ x) :=
  hφ.1.isReal x

theorem Nontracial.unit_adjoint_eq [hφ : φ.IsFaithfulPosMap] :
    LinearMap.adjoint (Algebra.linearMap ℂ ℍ : ℂ →ₗ[ℂ] ℍ) = φ := by
  rw [← @IsFaithfulPosMap.adjoint_eq n _ _ φ, LinearMap.adjoint_adjoint]

local notation "m" => LinearMap.mul' ℂ ℍ

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 350000 in
theorem Qam.Nontracial.mul_comp_mul_adjoint [hφ : φ.IsFaithfulPosMap] :
    LinearMap.mul' ℂ ℍ ∘ₗ LinearMap.adjoint (LinearMap.mul' ℂ ℍ) = trace (φ.matrix⁻¹) • 1 :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply]
  intro x
  simp_rw [← Matrix.ext_iff, LinearMap.mul'_adjoint,
    map_sum, _root_.map_smul, LinearMap.mul'_apply,
    Matrix.sum_apply, LinearMap.smul_apply, Matrix.smul_apply,
    smul_eq_mul, LinearMap.one_apply, mul_apply, stdBasisMatrix,
    boole_mul, Finset.mul_sum, mul_ite, MulZeroClass.mul_zero, mul_one, ite_and]
  intro i j
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp_rw [← Finset.mul_sum, ← trace_iff φ.matrix⁻¹, mul_comm]


-- theorem Module.Dual.IsFaithfulPosMap.basis_op_repr_apply (hφ : φ.IsFaithfulPosMap) (x : ℍᵐᵒᵖ)
--     (ij : n × n) :
--     (hφ.basis.mulOpposite.repr x) ij =
--       ((unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) x * hφ.matrixIsPosDef.rpow (1 / 2)) ij.1 ij.2 :=
--   by
--   rw [Basis.mulOpposite_repr_apply, unop, LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv_symm]
--   letI := Fact.mk hφ
--   rw [Module.Dual.IsFaithfulPosMap.basis_repr_apply]
--   exact Module.Dual.IsFaithfulPosMap.inner_coord' _ _


-- theorem LinearMap.mulLeft_toMatrix (hφ : φ.IsFaithfulPosMap) (x : Matrix n n ℂ) :
--     hφ.toMatrix (LinearMap.mulLeft ℂ x) = x ⊗ₖ 1 :=
--   by
--   ext
--   simp_rw [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply,
--     LinearMap.mulLeft_apply, IsFaithfulPosMap.basis_repr_apply,
--     Module.Dual.IsFaithfulPosMap.inner_coord', IsFaithfulPosMap.basis_apply, Matrix.mul_assoc,
--     PosDef.rpow_mul_rpow, neg_add_self, PosDef.rpow_zero, Matrix.mul_one, Matrix.mul_apply,
--     stdBasisMatrix, kroneckerMap, of_apply, Matrix.one_apply, mul_boole, ite_and, Finset.sum_ite_eq,
--     Finset.mem_univ, if_true, eq_comm]

-- theorem LinearMap.mulRight_toMatrix [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
--     hφ.toMatrix (LinearMap.mulRight ℂ x) = 1 ⊗ₖ (hφ.sig (1 / 2) x)ᵀ :=
--   by
--   ext
--   simp_rw [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply,
--     LinearMap.mulRight_apply, Module.Dual.IsFaithfulPosMap.basis_repr_apply,
--     Module.Dual.IsFaithfulPosMap.inner_coord']
--   simp_rw [Matrix.mul_apply, kroneckerMap, of_apply, Matrix.one_apply, IsFaithfulPosMap.basis_apply,
--     Matrix.mul_apply, stdBasisMatrix, boole_mul, Matrix.transpose_apply, ite_and, Finset.sum_ite_irrel,
--     Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, eq_comm]
--   simp only [ite_mul, MulZeroClass.zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
--   simp_rw [← Matrix.mul_apply]
--   rfl


local notation "ℍ_" i => Matrix (s i) (s i) ℂ

theorem includeBlock_adjoint [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    (x : PiMat ℂ k s) :
    LinearMap.adjoint (includeBlock : (ℍ_ i) →ₗ[ℂ] PiMat ℂ k s) x = x i :=
  by
  apply @ext_inner_left ℂ _ _
  intro a
  rw [LinearMap.adjoint_inner_right, pi.IsFaithfulPosMap.includeBlock_left_inner]


theorem pi_inner_stdBasisMatrix_left [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (i : k) (j l : s i)
    (x : PiMat ℂ k s) :
    ⟪blockDiag' (stdBasisMatrix (⟨i, j⟩ : Σ a, s a) (⟨i, l⟩ : Σ a, s a) (1 : ℂ)), x⟫_ℂ =
      (x i * (ψ i).matrix) j l :=
  by
  simp only [← includeBlock_apply_stdBasisMatrix,
    pi.IsFaithfulPosMap.includeBlock_left_inner, inner_stdBasisMatrix_left]

theorem eq_mpr_stdBasisMatrix {k : Type _} {s : k → Type _} [∀ i, DecidableEq (s i)] {i j : k}
    {b c : s j} (h₁ : i = j) :
    (by rw [h₁]; exact stdBasisMatrix b c (1 : ℂ) : Matrix (s i) (s i) ℂ) =
      stdBasisMatrix (by rw [h₁]; exact b) (by rw [h₁]; exact c) (1 : ℂ) :=
  by aesop

theorem pi_inner_stdBasisMatrix_stdBasisMatrix [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i j : k}
    (a b : s i) (c d : s j) :
    ⟪blockDiag' (stdBasisMatrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
        blockDiag' (stdBasisMatrix ⟨j, c⟩ ⟨j, d⟩ (1 : ℂ))⟫_ℂ =
      dite (i = j)
        (fun h => ite (a = by rw [h]; exact c) ((ψ i).matrix (by rw [h]; exact d) b) 0)
        fun _ => 0 :=
  by
  simp only [← includeBlock_apply_stdBasisMatrix]
  by_cases h : i = j
  ·
    simp only [h, dif_pos, pi.IsFaithfulPosMap.includeBlock_inner_same' h,
      inner_stdBasisMatrix_stdBasisMatrix, eq_mpr_stdBasisMatrix h]
  · simp only [h, dif_neg, not_false_iff, pi.IsFaithfulPosMap.includeBlock_inner_ne_same h]

theorem pi_inner_stdBasisMatrix_stdBasisMatrix_same [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    (a b c d : s i) :
    ⟪blockDiag' (stdBasisMatrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
        blockDiag' (stdBasisMatrix ⟨i, c⟩ ⟨i, d⟩ (1 : ℂ))⟫_ℂ =
      ite (a = c) ((ψ i).matrix d b) 0 :=
  by rw [pi_inner_stdBasisMatrix_stdBasisMatrix]; aesop

theorem pi_inner_stdBasisMatrix_stdBasisMatrix_ne [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i j : k}
    (h : i ≠ j) (a b : s i) (c d : s j) :
    ⟪blockDiag' (stdBasisMatrix ⟨i, a⟩ ⟨i, b⟩ (1 : ℂ)),
        blockDiag' (stdBasisMatrix ⟨j, c⟩ ⟨j, d⟩ (1 : ℂ))⟫_ℂ =
      0 :=
  by rw [pi_inner_stdBasisMatrix_stdBasisMatrix]; aesop

theorem LinearMap.pi_mul'_adjoint_single_block [hψ : ∀ i, (ψ i).IsFaithfulPosMap] {i : k}
    (x : Matrix (s i) (s i) ℂ) :
    (LinearMap.adjoint (LinearMap.mul' ℂ (PiMat ℂ k s))) (includeBlock x) =
      (TensorProduct.map includeBlock includeBlock)
        (LinearMap.adjoint (LinearMap.mul' ℂ (ℍ_ i)) x) :=
  by
  rw [TensorProduct.inner_ext_iff']
  intro a b
  rw [LinearMap.adjoint_inner_left, LinearMap.mul'_apply,
    pi.IsFaithfulPosMap.includeBlock_left_inner, ← LinearMap.adjoint_inner_right,
    TensorProduct.map_adjoint, TensorProduct.map_tmul, LinearMap.adjoint_inner_left,
    LinearMap.mul'_apply]
  simp_rw [includeBlock_adjoint, Pi.mul_apply]


/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b c d) -/
set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem LinearMap.pi_mul'_adjoint [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : PiMat ℂ k s) :
    LinearMap.adjoint (LinearMap.mul' ℂ (PiMat ℂ k s)) x =
      ∑ r : k, ∑ a, ∑ b, ∑ c, ∑ d,
        (x r a d * (pi.matrixBlock ψ r)⁻¹ c b) •
          blockDiag' (stdBasisMatrix (⟨r, a⟩ : Σ i, s i) (⟨r, b⟩ : Σ i, s i) (1 : ℂ)) ⊗ₜ[ℂ]
            blockDiag' (stdBasisMatrix (⟨r, c⟩ : Σ i, s i) (⟨r, d⟩ : Σ i, s i) (1 : ℂ)) :=
  by
  nth_rw 1 [matrix_eq_sum_includeBlock x]
  simp_rw [map_sum, LinearMap.pi_mul'_adjoint_single_block]
  apply Finset.sum_congr rfl; intros
  rw [LinearMap.mul'_adjoint]
  simp_rw [map_sum, _root_.map_smul, TensorProduct.map_tmul,
    includeBlock_apply_stdBasisMatrix, pi.matrixBlock_apply]

theorem LinearMap.pi_mul'_apply_includeBlock {i : k} (x : (ℍ_ i) ⊗[ℂ] ℍ_ i) :
    LinearMap.mul' ℂ (PiMat ℂ k s) ((TensorProduct.map includeBlock includeBlock) x) =
      includeBlock (LinearMap.mul' ℂ (ℍ_ i) x) :=
  by
  simp_rw [← LinearMap.comp_apply]
  revert x
  rw [← LinearMap.ext_iff, TensorProduct.ext_iff']
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    includeBlock_hMul_same]

private theorem linear_map.pi_mul'_comp_mul_adjoint_aux [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    {i : k} (x : ℍ_ i) :
    LinearMap.mul' ℂ (PiMat ℂ k s) (LinearMap.adjoint (LinearMap.mul' ℂ (PiMat ℂ k s)) (includeBlock x)) =
      trace ((ψ i).matrix⁻¹) • includeBlock x :=
  by
  rw [LinearMap.pi_mul'_adjoint_single_block, LinearMap.pi_mul'_apply_includeBlock]
  simp_rw [← LinearMap.comp_apply, Qam.Nontracial.mul_comp_mul_adjoint, LinearMap.comp_apply,
    LinearMap.smul_apply, _root_.map_smul, LinearMap.one_apply]

set_option synthInstance.maxHeartbeats 0 in
theorem LinearMap.pi_mul'_comp_mul'_adjoint [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x : PiMat ℂ k s) :
    LinearMap.mul' ℂ (PiMat ℂ k s) (LinearMap.adjoint (LinearMap.mul' ℂ (PiMat ℂ k s)) x) =
      ∑ i, Matrix.trace (((ψ i).matrix)⁻¹) • includeBlock (x i) :=
  by
  nth_rw 1 [matrix_eq_sum_includeBlock x]
  simp_rw [_root_.map_sum, linear_map.pi_mul'_comp_mul_adjoint_aux]


lemma Matrix.smul_inj_mul_one {n : Type*} [Fintype n] [DecidableEq n]
  [Nonempty n] (x y : ℂ) :
  x • (1 : Matrix n n ℂ) = y • (1 : Matrix n n ℂ) ↔ x = y :=
by
  simp_rw [← Matrix.ext_iff, Matrix.smul_apply, Matrix.one_apply, smul_ite,
    smul_zero, smul_eq_mul, mul_one]
  constructor
  . intro h
    let i : n := Nonempty.some ‹_›
    specialize h i i
    simp only [↓reduceIte] at h
    exact h
  . rintro rfl i j
    rfl

theorem LinearMap.pi_mul'_comp_mul'_adjoint_eq_smul_id_iff [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    [∀ i, Nontrivial (s i)] (α : ℂ) :
    LinearMap.mul' ℂ (PiMat ℂ k s) ∘ₗ (LinearMap.adjoint (LinearMap.mul' ℂ (PiMat ℂ k s))) = α • 1 ↔ ∀ i, Matrix.trace ((ψ i).matrix⁻¹) = α :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.pi_mul'_comp_mul'_adjoint,
    Function.funext_iff, Finset.sum_apply, ← LinearMap.map_smul,
    includeBlock_apply, Finset.sum_dite_eq', Finset.mem_univ, if_true,
    LinearMap.smul_apply, LinearMap.one_apply, Pi.smul_apply]
  simp only [eq_mp_eq_cast, cast_eq, ← Pi.smul_apply]
  -- simp_rw [← @Function.funext_iff k]
  constructor
  · intro h
    specialize h (1 : PiMat ℂ k s)
    simp only [Pi.smul_apply, Pi.one_apply] at h
    simp_rw [Matrix.smul_inj_mul_one] at h
    exact h
  · intro h i a
    rw [h]
