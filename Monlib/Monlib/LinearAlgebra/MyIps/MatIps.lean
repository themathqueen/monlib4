/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyIps.Functional
import LinearAlgebra.MyMatrix.PosDefRpow
import LinearAlgebra.Mul''
import LinearAlgebra.MyIps.Basic
import LinearAlgebra.PiDirectSum
import LinearAlgebra.ToMatrixOfEquiv

#align_import linear_algebra.my_ips.mat_ips

/-!

# The inner product space on finite dimensional C*-algebras

This file contains some basic results on the inner product space on finite dimensional C*-algebras.

-/


open scoped TensorProduct Functional

/-- A lemma that states the right multiplication property of a linear functional. -/
theorem linear_functional_right_hMul {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]
    [StarMul A] {φ : A →ₗ[R] R} (x y z : A) : φ (star (x * y) * z) = φ (star y * (star x * z)) := by
  rw [StarMul.star_hMul, mul_assoc]

/-- A lemma that states the left multiplication property of a linear functional. -/
theorem linear_functional_left_hMul {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]
    [StarMul A] {φ : A →ₗ[R] R} (x y z : A) : φ (star x * (y * z)) = φ (star (star y * x) * z) := by
  rw [StarMul.star_hMul, star_star, mul_assoc]

variable {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
  [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]

open Matrix

open scoped Matrix BigOperators

/-- A function that returns the direct sum of matrices for each index of type 'i'. -/
def Module.Dual.pi.matrixBlock (ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)) :
    ∀ i, Matrix (s i) (s i) ℂ :=
  ∑ i, (ψ i).Matrix.includeBlock

/-- A function that returns a direct sum matrix. -/
def Module.Dual.pi.matrix (ψ : ∀ i, Matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ) :
    Matrix (Σ i, s i) (Σ i, s i) ℂ :=
  blockDiagonal' (Module.Dual.pi.matrixBlock ψ)

/--
A lemma that states the inner product of two direct sum matrices is the sum of the inner products of their components. -/
theorem inner_pi_eq_sum [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (x y : ∀ i, Matrix (s i) (s i) ℂ) :
    ⟪x, y⟫_ℂ = ∑ i, ⟪x i, y i⟫_ℂ :=
  rfl

theorem Module.Dual.pi.matrixBlock_apply {i : k} : Module.Dual.pi.matrixBlock ψ i = (ψ i).Matrix :=
  by
  simp only [Module.Dual.pi.matrixBlock, Finset.sum_apply, include_block_apply, Finset.sum_dite_eq',
    Finset.mem_univ, if_true]
  rfl

/-- A function that returns a star algebra equivalence for each index of type 'i'. -/
def StarAlgEquiv.pi {𝕜 : Type _} [IsROrC 𝕜] {k : Type u_1} [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
    (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) :
    (∀ i, Matrix (s i) (s i) 𝕜) ≃⋆ₐ[𝕜] ∀ i, Matrix (s i) (s i) 𝕜
    where
  toFun x i := f i (x i)
  invFun x i := (f i).symm (x i)
  left_inv a := by simp only [StarAlgEquiv.symm_apply_apply]
  right_inv a := by simp only [StarAlgEquiv.apply_symm_apply]
  map_add' a y := by
    simp only [Pi.add_apply, map_add]
    rfl
  map_smul' r a := by
    simp only [Pi.smul_apply, SMulHomClass.map_smul]
    rfl
  map_mul' a b := by
    simp only [Pi.mul_apply, _root_.map_mul]
    rfl
  map_star' a := by
    simp only [Pi.star_apply, map_star]
    rfl

theorem StarAlgEquiv.pi_apply {𝕜 : Type _} [IsROrC 𝕜] {k : Type u_1} [Fintype k] [DecidableEq k]
    {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
    (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) (x : ∀ i, Matrix (s i) (s i) 𝕜)
    (i : k) : StarAlgEquiv.pi f x i = f i (x i) :=
  rfl

/-- the unitary element from the star algebraic equivalence -/
noncomputable def StarAlgEquiv.pi.unitary {𝕜 : Type _} [IsROrC 𝕜] {k : Type u_1} [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
    (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) : ∀ i, unitaryGroup (s i) 𝕜 :=
  fun i => (f i).unitary

theorem StarAlgEquiv.pi.unitary_apply {𝕜 : Type _} [IsROrC 𝕜] {k : Type u_1} [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
    (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) (a : k) :
    (StarAlgEquiv.pi.unitary f) a = (f a).unitary :=
  rfl

/-- any $^*$-isomorphism on $\bigoplus_i M_{n_i}$ is an inner automorphism -/
theorem StarAlgEquiv.of_pi_is_inner {𝕜 : Type _} [IsROrC 𝕜] {k : Type u_1} [Fintype k]
    [DecidableEq k] {s : k → Type _} [∀ i : k, Fintype (s i)] [∀ i : k, DecidableEq (s i)]
    (f : ∀ i, Matrix (s i) (s i) 𝕜 ≃⋆ₐ[𝕜] Matrix (s i) (s i) 𝕜) :
    unitary.innerAutStarAlg 𝕜 (unitary.pi (StarAlgEquiv.pi.unitary f)) = StarAlgEquiv.pi f :=
  by
  simp_rw [StarAlgEquiv.ext_iff, unitary.innerAutStarAlg_apply, Function.funext_iff, Pi.mul_apply,
    unitary.pi_apply, unitary.coe_star, Pi.star_apply, unitary.pi_apply, StarAlgEquiv.pi_apply,
    StarAlgEquiv.pi.unitary_apply]
  intros
  rw [← unitary.coe_star, ← @unitary.innerAutStarAlg_apply 𝕜 _ _ _ _ _ (f a_1).unitary (a a_1)]
  congr
  exact star_alg_equiv.eq_inner_aut _

def inclPi {i : k} (x : s i → ℂ) : (Σ j, s j) → ℂ := fun j =>
  dite (i = j.1) (fun h => x (by rw [h]; exact j.2)) fun h => 0

def exclPi (x : (Σ j, s j) → ℂ) (i : k) : s i → ℂ := fun j => x ⟨i, j⟩

private theorem pi.forall_left_mul (x y : ∀ i, Matrix (s i) (s i) ℂ) :
    (∀ a, a * x = a * y) ↔ x = y := by
  constructor
  · intro h
    specialize h 1
    simp_rw [one_mul] at h
    exact h
  · rintro rfl a
    rfl

theorem Module.Dual.pi.apply'' (ψ : ∀ i, Matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ)
    (x : ∀ i, Matrix (s i) (s i) ℂ) :
    Module.Dual.pi ψ x = (blockDiagonal' (Module.Dual.pi.matrixBlock ψ) * blockDiagonal' x).trace :=
  by
  simp_rw [Module.Dual.pi.apply', Module.Dual.pi.matrixBlock, ← block_diagonal'_alg_hom_apply,
    map_sum, Finset.sum_mul, trace_sum, mul_eq_mul]

theorem StarAlgEquiv.pi_is_trace_preserving
    (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ) (x : ∀ i, Matrix (s i) (s i) ℂ) :
    (blockDiagonal'AlgHom ((StarAlgEquiv.pi f) x)).trace = (blockDiagonal'AlgHom x).trace :=
  by
  rw [matrix_eq_sum_include_block ((StarAlgEquiv.pi f) x)]
  nth_rw_rhs 1 [matrix_eq_sum_include_block x]
  simp only [map_sum, trace_sum]
  simp only [block_diagonal'_alg_hom_apply, block_diagonal'_include_block_trace,
    StarAlgEquiv.pi_apply, StarAlgEquiv.trace_preserving]

theorem StarAlgEquiv.pi_symm_apply_apply (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ)
    (x : ∀ i, Matrix (s i) (s i) ℂ) :
    (StarAlgEquiv.pi fun i => (f i).symm) ((StarAlgEquiv.pi f) x) = x :=
  by
  ext1
  simp only [StarAlgEquiv.pi_apply, StarAlgEquiv.symm_apply_apply]

theorem Module.Dual.pi.apply_eq_of (ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ))
    (x : ∀ i, Matrix (s i) (s i) ℂ)
    (h : ∀ a, Module.Dual.pi ψ a = (blockDiagonal' x * blockDiagonal' a).trace) :
    x = Module.Dual.pi.matrixBlock ψ := by
  ext1
  simp only [Module.Dual.pi.matrixBlock_apply]
  apply Module.Dual.apply_eq_of
  intro a
  let a' := include_block a
  have ha' : a = a' x_1 := by simp only [a', include_block_apply_same]
  specialize h a'
  simp_rw [ha', ← Module.Dual.pi.apply_single_block, ← mul_eq_mul, ← Pi.mul_apply, ←
    block_diagonal'_include_block_trace, ← ha', Pi.mul_apply, ← ha']
  simp only [← block_diagonal'_alg_hom_apply, ← _root_.map_mul, a', mul_include_block] at h
  exact h

theorem StarAlgEquiv.pi_symm_apply_eq (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ)
    (x y : ∀ i, Matrix (s i) (s i) ℂ) :
    StarAlgEquiv.pi (fun i => (f i).symm) x = y ↔ x = StarAlgEquiv.pi f y :=
  by
  constructor <;> rintro rfl <;> ext1 <;> simp only [StarAlgEquiv.pi_apply]
  · rw [StarAlgEquiv.apply_symm_apply]
  · rw [StarAlgEquiv.symm_apply_apply]

theorem unitary.inj_hMul {A : Type _} [Monoid A] [StarMul A] (U : unitary A) (x y : A) :
    x = y ↔ x * U = y * U := by
  rw [IsUnit.mul_left_inj]
  · rw [← unitary.coe_toUnits_apply]
    exact (unitary.toUnits U).IsUnit

section SingleBlock

/-!
  ## Section `single_block`
-/


variable {n : Type _} [DecidableEq n] [Fintype n] {φ : Module.Dual ℂ (Matrix n n ℂ)}
  [hφ : Fact φ.IsFaithfulPosMap]

namespace Module.Dual.IsFaithfulPosMap

theorem inner_eq [hφ : Fact φ.IsFaithfulPosMap] (x y : Matrix n n ℂ) : ⟪x, y⟫_ℂ = φ (xᴴ ⬝ y) :=
  rfl

theorem inner_eq' [hφ : Fact φ.IsFaithfulPosMap] (x y : Matrix n n ℂ) :
    ⟪x, y⟫_ℂ = (φ.Matrix ⬝ xᴴ ⬝ y).trace := by rw [inner_eq, φ.apply, Matrix.mul_assoc]

def matrixIsPosDef (hφ : φ.IsFaithfulPosMap) : φ.Matrix.PosDef :=
  φ.isFaithfulPosMap_iff_of_matrix.mp hφ

theorem hMul_right (hφ : φ.IsFaithfulPosMap) (x y z : Matrix n n ℂ) :
    φ (xᴴ ⬝ (y ⬝ z)) = φ ((x ⬝ (φ.Matrix ⬝ zᴴ ⬝ φ.Matrix⁻¹))ᴴ ⬝ y) :=
  by
  haveI := hφ.matrix_is_pos_def.invertible
  simp_rw [φ.apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hφ.matrix_is_pos_def.1.Eq, hφ.matrix_is_pos_def.inv.1.Eq, ← Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_inv_cancel_left_of_invertible]
  rw [Matrix.trace_mul_cycle', Matrix.mul_assoc, ← Matrix.trace_mul_cycle', Matrix.mul_assoc]

theorem inner_left_hMul [hφ : Fact φ.IsFaithfulPosMap] (x y z : Matrix n n ℂ) :
    ⟪x ⬝ y, z⟫_ℂ = ⟪y, xᴴ ⬝ z⟫_ℂ :=
  linear_functional_right_hMul _ _ _

theorem inner_right_hMul [hφ : Fact φ.IsFaithfulPosMap] (x y z : Matrix n n ℂ) :
    ⟪x, y ⬝ z⟫_ℂ = ⟪yᴴ ⬝ x, z⟫_ℂ :=
  linear_functional_left_hMul _ _ _

theorem inner_left_conj [hφ : Fact φ.IsFaithfulPosMap] (x y z : Matrix n n ℂ) :
    ⟪x, y ⬝ z⟫_ℂ = ⟪x ⬝ (φ.Matrix ⬝ zᴴ ⬝ φ.Matrix⁻¹), y⟫_ℂ :=
  hφ.elim.mul_right _ _ _

theorem hMul_left (hφ : φ.IsFaithfulPosMap) (x y z : Matrix n n ℂ) :
    φ ((x ⬝ y)ᴴ ⬝ z) = φ (xᴴ ⬝ (z ⬝ (φ.Matrix ⬝ yᴴ ⬝ φ.Matrix⁻¹))) :=
  by
  letI := Fact.mk hφ
  rw [← inner_eq, ← InnerProductSpace.Core.inner_conj_symm, inner_left_conj,
    InnerProductSpace.Core.inner_conj_symm]
  rfl

theorem inner_right_conj [hφ : Fact φ.IsFaithfulPosMap] (x y z : Matrix n n ℂ) :
    ⟪x ⬝ y, z⟫_ℂ = ⟪x, z ⬝ (φ.Matrix ⬝ yᴴ ⬝ φ.Matrix⁻¹)⟫_ℂ :=
  hφ.elim.mul_left _ _ _

theorem adjoint_eq [hφ : Fact φ.IsFaithfulPosMap] :
    φ.adjoint = (Algebra.linearMap ℂ (Matrix n n ℂ) : ℂ →ₗ[ℂ] Matrix n n ℂ) :=
  by
  rw [LinearMap.ext_iff]
  intro x
  apply @ext_inner_right ℂ
  intro y
  rw [LinearMap.adjoint_inner_left, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
    InnerProductSpace.Core.inner_smul_left, inner_eq, conj_transpose_one, Matrix.one_mul]
  rfl

/-- The adjoint of a star-algebraic equivalence $f$ on matrix algebras is given by
  $$f^*\colon x \mapsto f^{-1}(x Q) Q^{-1},$$
  where $Q$ is `hφ.matrix`. -/
theorem starAlgEquiv_adjoint_eq [hφ : Fact φ.IsFaithfulPosMap]
    (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) (x : Matrix n n ℂ) :
    ((f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ).toAlgEquiv.toLinearMap :
            Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ).adjoint
        x =
      (f.symm (x ⬝ φ.Matrix) : Matrix n n ℂ) ⬝ φ.Matrix⁻¹ :=
  by
  haveI := hφ.elim.matrix_is_pos_def.invertible
  apply @ext_inner_left ℂ
  intro a
  simp_rw [LinearMap.adjoint_inner_right, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv]
  obtain ⟨U, rfl⟩ := f.of_matrix_is_inner
  simp_rw [inner_aut_star_alg_apply, inner_aut_star_alg_symm_apply, Matrix.mul_assoc]
  nth_rw_rhs 1 [← Matrix.mul_assoc φ.matrix]
  nth_rw_rhs 1 [← Matrix.mul_assoc]
  rw [inner_left_conj, inner_right_mul]
  simp_rw [conj_transpose_mul, hφ.elim.matrix_is_pos_def.1.Eq, hφ.elim.matrix_is_pos_def.inv.1.Eq, ←
    star_eq_conj_transpose, ← unitary_group.star_coe_eq_coe_star, star_star,
    Matrix.mul_inv_cancel_left_of_invertible, Matrix.mul_assoc, mul_inv_of_invertible,
    Matrix.mul_one]

theorem starAlgEquiv_unitary_commute_iff [hφ : Fact φ.IsFaithfulPosMap]
    (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) : Commute φ.Matrix f.unitary ↔ f φ.Matrix = φ.Matrix :=
  by
  rw [Commute, SemiconjBy]
  nth_rw 3 [← star_alg_equiv.eq_inner_aut f]
  rw [inner_aut_star_alg_apply, ← unitary_group.star_coe_eq_coe_star]
  nth_rw 2 [unitary_group.injective_mul f.unitary]
  simp_rw [Matrix.mul_assoc, unitary_group.star_mul_self, Matrix.mul_one, mul_eq_mul, eq_comm]

/-- Let `f` be a  star-algebraic equivalence on matrix algebras. Then tfae:

* `f φ.matrix = φ.matrix`,
* `f.adjoint = f⁻¹`,
* `φ ∘ f = φ`,
* `∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ`,
* `∀ x, ‖f x‖ = ‖x‖`,
* `φ.matrix` commutes with `f.unitary`.
-/
theorem starAlgEquiv_is_isometry_tFAE [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    TFAE
      [f φ.Matrix = φ.Matrix,
        ((f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ).toAlgEquiv.toLinearMap :
              Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ).adjoint =
          f.symm.toAlgEquiv.toLinearMap,
        φ ∘ₗ f.toAlgEquiv.toLinearMap = φ, ∀ x y, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ,
        ∀ x : Matrix n n ℂ, ‖f x‖ = ‖x‖, Commute φ.Matrix f.unitary] :=
  by
  tfae_have 5 ↔ 2
  · simp_rw [InnerProductSpace.Core.norm_eq_sqrt_inner,
      Real.sqrt_inj InnerProductSpace.Core.inner_self_nonneg
        InnerProductSpace.Core.inner_self_nonneg,
      ← Complex.ofReal_inj, inner_self_re, ← @sub_eq_zero _ _ _ ⟪_, _⟫_ℂ]
    have :
      ∀ x y,
        ⟪f x, f y⟫_ℂ - ⟪x, y⟫_ℂ =
          ⟪(f.to_alg_equiv.to_linear_map.adjoint ∘ₗ f.to_alg_equiv.to_linear_map - 1) x, y⟫_ℂ :=
      by
      intro x y
      simp only [LinearMap.sub_apply, LinearMap.one_apply, inner_sub_left, LinearMap.comp_apply,
        LinearMap.adjoint_inner_left, StarAlgEquiv.coe_toAlgEquiv, AlgEquiv.toLinearMap_apply]
    simp_rw [this, inner_map_self_eq_zero, sub_eq_zero, StarAlgEquiv.comp_eq_iff,
      LinearMap.one_comp]
  rw [tfae_5_iff_2]
  tfae_have 4 ↔ 3
  · simp_rw [inner_eq, ← star_eq_conj_transpose, ← map_star f, ← mul_eq_mul, ← _root_.map_mul f,
      LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      StarAlgEquiv.coe_toAlgEquiv]
    refine' ⟨fun h x => _, fun h x y => h _⟩
    rw [← Matrix.one_mul x, ← star_one, ← mul_eq_mul]
    exact h _ _
  rw [tfae_4_iff_3]
  haveI := hφ.elim.matrix_is_pos_def.invertible
  simp_rw [LinearMap.ext_iff, star_alg_equiv_adjoint_eq f, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv, mul_inv_eq_iff_eq_mul_of_invertible,
    φ.apply, StarAlgEquiv.symm_apply_eq, ← mul_eq_mul, _root_.map_mul,
    StarAlgEquiv.apply_symm_apply, ← forall_left_hMul φ.matrix, @eq_comm _ φ.matrix]
  tfae_have 1 ↔ 2
  · rw [iff_self_iff]; trivial
  tfae_have 1 → 3
  · intro i x
    nth_rw 1 [← i]
    rw [← _root_.map_mul, f.trace_preserving]
  tfae_have 3 → 1
  · intro i
    simp_rw [← f.symm.trace_preserving (φ.matrix * f _), _root_.map_mul,
      StarAlgEquiv.symm_apply_apply, mul_eq_mul, ← φ.apply, @eq_comm _ _ (φ _)] at i
    obtain ⟨Q, hQ, h⟩ := Module.Dual.eq_trace_unique φ
    have := h _ i
    rw [StarAlgEquiv.symm_apply_eq] at this
    nth_rw_rhs 1 [this]
    congr
    exact h _ φ.apply
  rw [star_alg_equiv_unitary_commute_iff]
  tfae_finish

protected noncomputable def basis (hφ : φ.IsFaithfulPosMap) : Basis (n × n) ℂ (Matrix n n ℂ) :=
  by
  let hQ := hφ.matrix_is_pos_def
  refine' Basis.mk _ _
  · exact fun ij => std_basis_matrix ij.1 ij.2 1 ⬝ hφ.matrix_is_pos_def.rpow (-(1 / 2))
  · have := (std_basis ℂ n n).LinearIndependent
    simp_rw [LinearIndependent, LinearMap.ker_eq_bot, injective_iff_map_eq_zero,
      Finsupp.total_apply, Finsupp.sum] at this ⊢
    simp_rw [← mul_eq_mul, ← smul_mul_assoc, ← Finset.sum_mul]
    by_cases IsEmpty n
    · haveI := h
      simp only [eq_iff_true_of_subsingleton, forall_const]
    rw [not_isEmpty_iff] at h
    have t1 :
      ∀ a : n × n →₀ ℂ,
        (∑ x : n × n in a.support, a x • (std_basis_matrix x.fst x.snd 1 : Matrix n n ℂ)) *
              hQ.rpow (-(1 / 2)) =
            0 ↔
          (∑ x : n × n in a.support, a x • (std_basis_matrix x.fst x.snd 1 : Matrix n n ℂ)) *
                hQ.rpow (-(1 / 2)) *
              hQ.rpow (1 / 2) =
            0 * hQ.rpow (1 / 2) :=
      by
      intro a
      constructor <;> intro h
      · rw [h]
      · simp_rw [mul_assoc, mul_eq_mul, Matrix.PosDef.rpow_hMul_rpow, neg_add_self,
          Matrix.PosDef.rpow_zero, Matrix.mul_one] at h
        rw [h, Matrix.zero_mul, MulZeroClass.zero_mul]
    simp_rw [t1, mul_assoc, mul_eq_mul, Matrix.PosDef.rpow_hMul_rpow, neg_add_self,
      Matrix.PosDef.rpow_zero, Matrix.zero_mul, Matrix.mul_one, ← std_basis_eq_std_basis_matrix ℂ,
      Prod.mk.eta]
    exact this
  · simp_rw [top_le_iff]
    ext
    simp_rw [Submodule.mem_top, iff_true_iff, mem_span_range_iff_exists_fun, ← smul_mul, ←
      mul_eq_mul, ← Finset.sum_mul, ← Matrix.ext_iff, mul_eq_mul, mul_apply, Matrix.sum_apply,
      Pi.smul_apply, std_basis_matrix, smul_ite, smul_zero, ← Prod.mk.inj_iff, Prod.mk.eta,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_mul_assoc, one_mul]
    exists fun ij : n × n => (x ⬝ hQ.rpow (1 / 2) : Matrix n n ℂ) ij.1 ij.2
    simp_rw [smul_eq_mul, ← mul_apply, Matrix.mul_assoc, Matrix.PosDef.rpow_hMul_rpow, add_neg_self,
      Matrix.PosDef.rpow_zero, Matrix.mul_one, eq_self_iff_true, forall₂_true_iff]

protected theorem basis_apply (hφ : φ.IsFaithfulPosMap) (ij : n × n) :
    hφ.Basis ij = stdBasisMatrix ij.1 ij.2 (1 : ℂ) ⬝ hφ.matrixIsPosDef.rpow (-(1 / 2 : ℝ)) := by
  rw [is_faithful_pos_map.basis, Basis.mk_apply]

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

protected noncomputable def toMatrix (hφ : φ.IsFaithfulPosMap) :
    (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) ≃ₐ[ℂ] Matrix (n × n) (n × n) ℂ :=
  LinearMap.toMatrixAlgEquiv hφ.Basis

theorem basis_is_orthonormal [hφ : Fact φ.IsFaithfulPosMap] : Orthonormal ℂ hφ.elim.Basis :=
  by
  rw [orthonormal_iff_ite]
  simp_rw [Module.Dual.IsFaithfulPosMap.basis_apply]
  simp_rw [inner_eq', conj_transpose_mul, (pos_def.rpow.is_hermitian _ _).Eq,
    std_basis_matrix.star_one, Matrix.mul_assoc, ← Matrix.mul_assoc _ (std_basis_matrix _ _ _),
    stdBasisMatrix_hMul, one_mul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul,
    boole_mul]
  let Q := φ.matrix
  let hQ := hφ.elim.matrix_is_pos_def
  have :
    ∀ i j : n,
      (Q ⬝ (hQ.rpow (-(1 / 2) : ℝ) ⬝ (std_basis_matrix i j 1 ⬝ hQ.rpow (-(1 / 2) : ℝ)))).trace =
        ite (i = j) (1 : ℂ) (0 : ℂ) :=
    fun i j =>
    calc
      (Q ⬝ (hQ.rpow (-(1 / 2) : ℝ) ⬝ (std_basis_matrix i j 1 ⬝ hQ.rpow (-(1 / 2) : ℝ)))).trace =
          (hQ.rpow (-(1 / 2) : ℝ) ⬝ hQ.rpow 1 ⬝ hQ.rpow (-(1 / 2) : ℝ) ⬝
              std_basis_matrix i j 1).trace :=
        by
        simp_rw [pos_def.rpow_one_eq_self, Matrix.mul_assoc]
        rw [← trace_mul_cycle', trace_mul_comm]
        simp_rw [Matrix.mul_assoc]
        rw [trace_mul_comm]
        simp_rw [Matrix.mul_assoc]
      _ = (hQ.rpow (-(1 / 2) + 1 + -(1 / 2) : ℝ) ⬝ std_basis_matrix i j 1).trace := by
        simp_rw [pos_def.rpow_mul_rpow]
      _ = (hQ.rpow 0 ⬝ std_basis_matrix i j 1).trace := by norm_num
      _ = ite (i = j) 1 0 := by simp_rw [pos_def.rpow_zero, Matrix.one_mul, std_basis_matrix.trace]
  simp_rw [this, ← ite_and, ← Prod.eq_iff_fst_eq_snd_eq, eq_self_iff_true, forall₂_true_iff]

protected noncomputable def orthonormalBasis [hφ : Fact φ.IsFaithfulPosMap] :
    OrthonormalBasis (n × n) ℂ (Matrix n n ℂ) :=
  hφ.elim.Basis.toOrthonormalBasis basis_is_orthonormal

protected theorem orthonormalBasis_apply [hφ : Fact φ.IsFaithfulPosMap] (ij : n × n) :
    (IsFaithfulPosMap.orthonormalBasis : OrthonormalBasis (n × n) ℂ (Matrix n n ℂ)) ij =
      stdBasisMatrix ij.1 ij.2 (1 : ℂ) ⬝ hφ.elim.matrixIsPosDef.rpow (-(1 / 2 : ℝ)) :=
  by
  rw [← is_faithful_pos_map.basis_apply, is_faithful_pos_map.orthonormal_basis,
    Basis.coe_toOrthonormalBasis]

theorem inner_coord [hφ : Fact φ.IsFaithfulPosMap] (ij : n × n) (y : Matrix n n ℂ) :
    ⟪(IsFaithfulPosMap.orthonormalBasis : OrthonormalBasis _ _ _) ij, y⟫_ℂ =
      (y ⬝ hφ.elim.matrixIsPosDef.rpow (1 / 2)) ij.1 ij.2 :=
  by
  let Q := φ.matrix
  let hQ := hφ.elim.matrix_is_pos_def
  simp_rw [inner_eq', is_faithful_pos_map.orthonormal_basis_apply, conj_transpose_mul,
    (Matrix.PosDef.rpow.isHermitian hQ _).Eq, ← Matrix.mul_assoc, std_basis_matrix_conj_transpose,
    star_one]
  have :=
    calc
      Q ⬝ hQ.rpow (-(1 / 2)) = hQ.rpow 1 ⬝ hQ.rpow (-(1 / 2)) := by
        rw [Matrix.PosDef.rpow_one_eq_self]
      _ = hQ.rpow (1 + -(1 / 2)) := by rw [Matrix.PosDef.rpow_hMul_rpow]
      _ = hQ.rpow (1 / 2) := by norm_num
  rw [this]
  simp_rw [trace_iff, mul_apply, std_basis_matrix, mul_boole, ite_and]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, MulZeroClass.zero_mul]
  simp_rw [mul_comm]

protected theorem basis_repr_apply [hφ : Fact φ.IsFaithfulPosMap] (x : Matrix n n ℂ) (ij : n × n) :
    hφ.elim.Basis.repr x ij = ⟪hφ.elim.Basis ij, x⟫_ℂ :=
  by
  rw [is_faithful_pos_map.basis_apply, ← is_faithful_pos_map.orthonormal_basis_apply, ←
    OrthonormalBasis.repr_apply_apply]
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
protected theorem toMatrix_symm_apply [hφ : Fact φ.IsFaithfulPosMap]
    (x : Matrix (n × n) (n × n) ℂ) :
    hφ.elim.toMatrix.symm x =
      ∑ (i : n) (j : n) (k : n) (l : n),
        (x (i, j) (k, l) : ℂ) • |hφ.elim.Basis (i, j)⟩⟨hφ.elim.Basis (k, l)| :=
  by
  rw [is_faithful_pos_map.to_matrix, LinearMap.toMatrixAlgEquiv_symm, LinearMap.ext_iff]
  intro a
  simp_rw [to_lin_alg_equiv_apply, mul_vec, dot_product, is_faithful_pos_map.basis_repr_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    is_faithful_pos_map.basis_apply, Finset.sum_smul]
  repeat'
    nth_rw_rhs 1 [← Finset.sum_product']
    rw [Finset.univ_product_univ]
    apply Finset.sum_congr rfl
    intro ij hij
  simp_rw [smul_smul, Prod.mk.eta]

end Module.Dual.IsFaithfulPosMap

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem Module.Dual.eq_rankOne_of_faithful_pos_map [hφ : Fact φ.IsFaithfulPosMap]
    (x : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    x =
      ∑ (i : n) (j : n) (k : n) (l : n),
        hφ.elim.toMatrix x (i, j) (k, l) • |hφ.elim.Basis (i, j)⟩⟨hφ.elim.Basis (k, l)| :=
  by rw [← Module.Dual.IsFaithfulPosMap.toMatrix_symm_apply, AlgEquiv.symm_apply_apply]

end SingleBlock

---------
section DirectSum

/-! # Section direct_sum -/


theorem LinearMap.sum_single_comp_proj {R : Type _} {ι : Type _} [Fintype ι] [DecidableEq ι]
    [Semiring R] {φ : ι → Type _} [∀ i : ι, AddCommMonoid (φ i)] [∀ i : ι, Module R (φ i)] :
    ∑ i : ι, LinearMap.single i ∘ₗ LinearMap.proj i = (LinearMap.id : (∀ i, φ i) →ₗ[R] ∀ i, φ i) :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.sum_apply, LinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.coe_single, Pi.single, Function.funext_iff, Finset.sum_apply,
    Function.update, Pi.zero_apply, Finset.sum_dite_eq, Finset.mem_univ, if_true]
  intro x y; trivial

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (r p) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (r p) -/
theorem LinearMap.lrsum_eq_single_proj_lrcomp
    (f : (∀ i, Matrix (s i) (s i) ℂ) →ₗ[ℂ] ∀ i, Matrix (s i) (s i) ℂ) :
    ∑ (r) (p),
        LinearMap.single r ∘ₗ LinearMap.proj r ∘ₗ f ∘ₗ LinearMap.single p ∘ₗ LinearMap.proj p =
      f :=
  calc
    ∑ (r) (p),
          LinearMap.single r ∘ₗ LinearMap.proj r ∘ₗ f ∘ₗ LinearMap.single p ∘ₗ LinearMap.proj p =
        (∑ r, LinearMap.single r ∘ₗ LinearMap.proj r) ∘ₗ
          f ∘ₗ ∑ p, LinearMap.single p ∘ₗ LinearMap.proj p :=
      by simp_rw [LinearMap.sum_comp, LinearMap.comp_sum, LinearMap.comp_assoc]
    _ = LinearMap.id ∘ₗ f ∘ₗ LinearMap.id := by rw [LinearMap.sum_single_comp_proj]
    _ = f := by rw [LinearMap.id_comp, LinearMap.comp_id]

namespace Module.Dual.pi.IsFaithfulPosMap

theorem inner_eq [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (x y : ∀ i, Matrix (s i) (s i) ℂ) :
    ⟪x, y⟫_ℂ = Module.Dual.pi ψ (star x * y) :=
  rfl

theorem inner_eq' [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (x y : ∀ i, Matrix (s i) (s i) ℂ) :
    ⟪x, y⟫_ℂ = ∑ i, ((ψ i).Matrix ⬝ (x i)ᴴ ⬝ y i).trace := by
  simp only [inner_eq, Module.Dual.pi.apply, Pi.mul_apply, Matrix.hMul_eq_hMul,
    Matrix.star_eq_conjTranspose, Pi.star_apply, Matrix.mul_assoc]

theorem inner_left_hMul [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (x y z : ∀ i, Matrix (s i) (s i) ℂ) : ⟪x * y, z⟫_ℂ = ⟪y, star x * z⟫_ℂ :=
  @linear_functional_right_hMul _ _ _ _ _ _ (Module.Dual.pi ψ) _ _ _

theorem hMul_right (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (x y z : ∀ i, Matrix (s i) (s i) ℂ) :
    Module.Dual.pi ψ (star x * (y * z)) =
      Module.Dual.pi ψ
        (star (x * (Module.Dual.pi.matrixBlock ψ * star z * (Module.Dual.pi.matrixBlock ψ)⁻¹)) *
          y) :=
  by
  letI := fun i => Fact.mk (hψ i)
  rw [← inner_eq]
  simp only [inner_eq']
  simp_rw [← Module.Dual.IsFaithfulPosMap.inner_eq', Pi.mul_apply, Matrix.hMul_eq_hMul,
    Module.Dual.IsFaithfulPosMap.inner_left_conj, ← inner_eq, inner_pi_eq_sum, Pi.mul_apply,
    Pi.inv_apply, Pi.star_apply, Matrix.hMul_eq_hMul, Matrix.star_eq_conjTranspose,
    Module.Dual.pi.matrixBlock_apply]

theorem inner_left_conj [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (x y z : ∀ i, Matrix (s i) (s i) ℂ) :
    ⟪x, y * z⟫_ℂ =
      ⟪x * (Module.Dual.pi.matrixBlock ψ * star z * (Module.Dual.pi.matrixBlock ψ)⁻¹), y⟫_ℂ :=
  hMul_right (fun i => (hψ i).elim) _ _ _

theorem inner_right_hMul [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (x y z : ∀ i, Matrix (s i) (s i) ℂ) : ⟪x, y * z⟫_ℂ = ⟪star y * x, z⟫_ℂ :=
  @linear_functional_left_hMul _ _ _ _ _ _ (Module.Dual.pi ψ) _ _ _

theorem adjoint_eq [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] :
    (Module.Dual.pi ψ).adjoint = Algebra.linearMap ℂ (∀ i, Matrix (s i) (s i) ℂ) :=
  by
  rw [LinearMap.ext_iff]
  intro x
  apply @ext_inner_right ℂ
  intro y
  rw [LinearMap.adjoint_inner_left, Algebra.linearMap_apply]
  simp_rw [inner_pi_eq_sum, Pi.algebraMap_apply, algebra_map_eq_smul,
    InnerProductSpace.Core.inner_smul_left, Module.Dual.IsFaithfulPosMap.inner_eq,
    conj_transpose_one, Matrix.one_mul, ← Finset.mul_sum]
  rfl

protected noncomputable def basis (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    Basis (Σ i, s i × s i) ℂ (∀ i, Matrix (s i) (s i) ℂ) :=
  Pi.basis fun i => (hψ i).Basis

protected theorem basis_apply (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (ijk : Σ i, s i × s i) :
    Module.Dual.pi.IsFaithfulPosMap.basis hψ ijk =
      includeBlock
        (stdBasisMatrix ijk.2.1 ijk.2.2 1 ⬝ (hψ ijk.1).matrixIsPosDef.rpow (-(1 / 2 : ℝ))) :=
  by
  simp only [Module.Dual.pi.IsFaithfulPosMap.basis, Pi.basis_apply, Function.funext_iff]
  intro i j k
  simp only [LinearMap.stdBasis_apply, Pi.mul_apply, include_block_apply, mul_eq_mul, mul_apply,
    dite_apply, hMul_dite, MulZeroClass.mul_zero, Pi.zero_apply, Function.update]
  rw [dite_eq_iff']
  constructor
  · intro h
    simp only [h, eq_self_iff_true, dif_pos, Module.Dual.IsFaithfulPosMap.basis_apply]
    finish
  · intro h
    rw [eq_comm] at h
    simp only [h, not_false_iff, dif_neg]

protected theorem basis_apply' (hψ : ∀ i, (ψ i).IsFaithfulPosMap) (i : k) (j l : s i) :
    Module.Dual.pi.IsFaithfulPosMap.basis hψ ⟨i, (j, l)⟩ =
      includeBlock (stdBasisMatrix j l 1 ⬝ (hψ i).matrixIsPosDef.rpow (-(1 / 2 : ℝ))) :=
  Module.Dual.pi.IsFaithfulPosMap.basis_apply hψ _

theorem includeBlock_left_inner [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] {i : k}
    (x : Matrix (s i) (s i) ℂ) (y : ∀ j, Matrix (s j) (s j) ℂ) :
    ⟪includeBlock x, y⟫_ℂ = ⟪x, y i⟫_ℂ :=
  by
  simp only [inner_pi_eq_sum, include_block_apply, Module.Dual.IsFaithfulPosMap.inner_eq', ←
    mul_eq_mul, ← star_eq_conj_transpose, star_dite, star_zero, hMul_dite, MulZeroClass.mul_zero,
    dite_hMul, MulZeroClass.zero_mul]
  simp_rw [trace_iff, dite_apply, Pi.zero_apply, Finset.sum_dite_irrel, Finset.sum_const_zero,
    Finset.sum_dite_eq, Finset.mem_univ, if_true]
  rfl

theorem includeBlock_inner_same [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] {i : k}
    {x y : Matrix (s i) (s i) ℂ} : ⟪includeBlock x, includeBlock y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [include_block_left_inner, include_block_apply_same]

theorem includeBlock_inner_same' [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] {i j : k}
    {x : Matrix (s i) (s i) ℂ} {y : Matrix (s j) (s j) ℂ} (h : i = j) :
    ⟪includeBlock x, includeBlock y⟫_ℂ = ⟪x, by rw [h]; exact y⟫_ℂ :=
  by
  simp_rw [include_block_left_inner, include_block_apply, h, eq_self_iff_true, dif_pos]
  rfl

theorem includeBlock_inner_ne_same [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] {i j : k}
    {x : Matrix (s i) (s i) ℂ} {y : Matrix (s j) (s j) ℂ} (h : i ≠ j) :
    ⟪includeBlock x, includeBlock y⟫_ℂ = 0 := by
  simp only [include_block_left_inner, include_block_apply_ne_same _ h.symm, inner_zero_right]

protected theorem basis.apply_cast_eq_mpr (hψ : ∀ i, (ψ i).IsFaithfulPosMap) {i j : k}
    {a : s j × s j} (h : i = j) :
    (hψ i).Basis (by rw [h]; exact a) = by rw [h]; exact (hψ j).Basis a :=
  by
  simp only [eq_mpr_eq_cast, h]
  finish

protected theorem basis_is_orthonormal [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] :
    Orthonormal ℂ (Module.Dual.pi.IsFaithfulPosMap.basis fun i => (hψ i).elim) :=
  by
  rw [orthonormal_iff_ite]
  intro i j
  rw [eq_comm, ite_eq_iff']
  constructor
  · rintro rfl
    simp only [Module.Dual.pi.IsFaithfulPosMap.basis_apply, include_block_inner_same', cast_eq,
      eq_mpr_eq_cast, ← Module.Dual.IsFaithfulPosMap.basis_apply,
      orthonormal_iff_ite.mp Module.Dual.IsFaithfulPosMap.basis_is_orthonormal i.snd,
      eq_self_iff_true, if_true]
  · intro h
    by_cases h' : i.fst = j.fst
    · rw [Sigma.ext_iff, not_and_or] at h
      cases' h with h1 h2
      · contradiction
      · rw [← Sigma.eta i, ← Sigma.eta j]
        simp only [Module.Dual.pi.IsFaithfulPosMap.basis_apply, include_block_inner_same' h', ←
          Module.Dual.IsFaithfulPosMap.basis_apply, ← basis.apply_cast_eq_mpr fun i => (hψ i).elim,
          Sigma.eta, orthonormal_iff_ite.mp Module.Dual.IsFaithfulPosMap.basis_is_orthonormal i.snd]
        rw [eq_comm, ite_eq_right_iff]
        intro hh
        rw [hh] at h2
        simp only [eq_mpr_eq_cast, cast_hEq, not_true] at h2
        contradiction
    · simp only [Module.Dual.pi.IsFaithfulPosMap.basis_apply, include_block_inner_ne_same h']

protected noncomputable def orthonormalBasis [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] :
    OrthonormalBasis (Σ i, s i × s i) ℂ (∀ i, Matrix (s i) (s i) ℂ) :=
  Basis.toOrthonormalBasis (Module.Dual.pi.IsFaithfulPosMap.basis fun i => (hψ i).elim)
    Module.Dual.pi.IsFaithfulPosMap.basis_is_orthonormal

protected theorem orthonormalBasis_apply [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    {ijk : Σ i, s i × s i} :
    (Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis : OrthonormalBasis _ _ _) ijk =
      includeBlock
        (stdBasisMatrix ijk.2.1 ijk.2.2 1 ⬝ (hψ ijk.1).elim.matrixIsPosDef.rpow (-(1 / 2 : ℝ))) :=
  by
  rw [← Module.Dual.pi.IsFaithfulPosMap.basis_apply _]
  simp only [Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis, Basis.coe_toOrthonormalBasis]

protected theorem orthonormalBasis_apply' [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] {i : k}
    {j l : s i} :
    (Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis : OrthonormalBasis _ _ _) ⟨i, (j, l)⟩ =
      includeBlock (stdBasisMatrix j l 1 ⬝ (hψ i).elim.matrixIsPosDef.rpow (-(1 / 2 : ℝ))) :=
  Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis_apply

protected theorem inner_coord [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (ijk : Σ i, s i × s i)
    (y : ∀ i, Matrix (s i) (s i) ℂ) :
    ⟪Module.Dual.pi.IsFaithfulPosMap.basis (fun i => (hψ i).elim) ijk, y⟫_ℂ =
      (y ijk.1 ⬝ (hψ ijk.1).elim.matrixIsPosDef.rpow (1 / 2)) ijk.2.1 ijk.2.2 :=
  by
  let Q := (ψ ijk.1).Matrix
  let hQ := (hψ ijk.1).elim.matrixIsPosDef
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.basis_apply, include_block_left_inner, ←
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, Module.Dual.IsFaithfulPosMap.inner_coord]

protected theorem basis_repr_apply [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (x : ∀ i, Matrix (s i) (s i) ℂ) (ijk : Σ i, s i × s i) :
    (Module.Dual.pi.IsFaithfulPosMap.basis fun i => (hψ i).elim).repr x ijk =
      ⟪(hψ ijk.1).elim.Basis ijk.2, x ijk.1⟫_ℂ :=
  by
  rw [Module.Dual.IsFaithfulPosMap.basis_apply, ←
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, ← OrthonormalBasis.repr_apply_apply]
  rfl

theorem MatrixBlock.isSelfAdjoint [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] :
    IsSelfAdjoint (Module.Dual.pi.matrixBlock ψ) :=
  by
  ext1
  simp only [Pi.star_apply, Module.Dual.pi.matrixBlock_apply, star_eq_conj_transpose,
    (hψ x).elim.matrixIsPosDef.1.Eq]

noncomputable def matrixBlockInvertible [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] :
    Invertible (Module.Dual.pi.matrixBlock ψ) :=
  by
  haveI := fun i => (hψ i).elim.matrixIsPosDef.Invertible
  apply Invertible.mk (Module.Dual.pi.matrixBlock ψ)⁻¹
  all_goals
    ext1
    simp_rw [Pi.mul_apply, Pi.inv_apply, Module.Dual.pi.matrixBlock_apply, mul_eq_mul, Pi.one_apply]
  on_goal 1 => rw [inv_mul_of_invertible]
  rw [mul_inv_of_invertible]

theorem matrixBlock_inv_hMul_self [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] :
    (Module.Dual.pi.matrixBlock ψ)⁻¹ * Module.Dual.pi.matrixBlock ψ = 1 :=
  by
  haveI := fun i => (hψ i).elim.matrixIsPosDef.Invertible
  ext1
  simp_rw [Pi.mul_apply, Pi.inv_apply, Module.Dual.pi.matrixBlock_apply, mul_eq_mul, Pi.one_apply,
    inv_mul_of_invertible]

theorem matrixBlock_self_hMul_inv [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] :
    Module.Dual.pi.matrixBlock ψ * (Module.Dual.pi.matrixBlock ψ)⁻¹ = 1 :=
  by
  haveI := fun i => (hψ i).elim.matrixIsPosDef.Invertible
  ext1
  simp_rw [Pi.mul_apply, Pi.inv_apply, Module.Dual.pi.matrixBlock_apply, mul_eq_mul, Pi.one_apply,
    mul_inv_of_invertible]

noncomputable def toMatrix (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    ((∀ i, Matrix (s i) (s i) ℂ) →ₗ[ℂ] ∀ i, Matrix (s i) (s i) ℂ) ≃ₐ[ℂ]
      Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ :=
  LinearMap.toMatrixAlgEquiv (Module.Dual.pi.IsFaithfulPosMap.basis hψ)

@[simps]
noncomputable def isBlockDiagonalBasis (hψ : ∀ i, (ψ i).IsFaithfulPosMap) :
    Basis (Σ i, s i × s i) ℂ { x : Matrix (Σ i, s i) (Σ i, s i) ℂ // x.IsBlockDiagonal }
    where repr :=
    isBlockDiagonalPiAlgEquiv.toLinearEquiv.trans (Module.Dual.pi.IsFaithfulPosMap.basis hψ).repr

theorem toMatrix_apply' [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (f : (∀ i, Matrix (s i) (s i) ℂ) →ₗ[ℂ] ∀ i, Matrix (s i) (s i) ℂ) (r l : Σ r, s r × s r) :
    (toMatrix fun i => (hψ i).elim) f r l =
      (f (includeBlock ((hψ l.1).elim.Basis l.2)) r.1 ⬝ (hψ r.1).elim.matrixIsPosDef.rpow (1 / 2))
        r.2.1 r.2.2 :=
  by
  simp_rw [to_matrix, LinearMap.toMatrixAlgEquiv_apply, is_faithful_pos_map.basis_repr_apply, ←
    Module.Dual.IsFaithfulPosMap.inner_coord, is_faithful_pos_map.basis_apply,
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, ← Module.Dual.IsFaithfulPosMap.basis_apply]

theorem starAlgEquiv_adjoint_eq [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ) (x : ∀ i, Matrix (s i) (s i) ℂ) :
    (StarAlgEquiv.pi f).toAlgEquiv.toLinearMap.adjoint x =
      (StarAlgEquiv.pi f).symm (x * Module.Dual.pi.matrixBlock ψ) *
        (Module.Dual.pi.matrixBlock ψ)⁻¹ :=
  by
  letI := @matrix_block_invertible _ _ _ _ _ _ ψ _
  letI := fun i => (hψ i).elim.matrixIsPosDef.Invertible
  apply @ext_inner_left ℂ
  intro a
  simp_rw [LinearMap.adjoint_inner_right, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv]
  rw [← StarAlgEquiv.of_pi_is_inner]
  simp_rw [unitary.innerAutStarAlg_apply, unitary.innerAutStarAlg_symm_apply, mul_assoc]
  nth_rw_rhs 1 [← mul_assoc (Module.Dual.pi.matrixBlock ψ)]
  nth_rw_rhs 1 [← mul_assoc]
  rw [inner_left_conj, inner_right_mul]
  simp_rw [StarMul.star_hMul, IsSelfAdjoint.star_eq matrix_block.is_self_adjoint, mul_assoc]
  have t1 : Module.Dual.pi.matrixBlock ψ * (Module.Dual.pi.matrixBlock ψ)⁻¹ = 1 :=
    by
    ext1
    simp only [Pi.mul_apply, Pi.inv_apply, mul_eq_mul, Module.Dual.pi.matrixBlock_apply,
      mul_inv_of_invertible, Pi.one_apply]
  have t2 :=
    calc
      Module.Dual.pi.matrixBlock ψ * star (Module.Dual.pi.matrixBlock ψ)⁻¹ =
          Module.Dual.pi.matrixBlock ψ * (Module.Dual.pi.matrixBlock ψ)⁻¹ :=
        by
        congr
        simp only [Pi.inv_def, Pi.star_def, Module.Dual.pi.matrixBlock_apply,
          star_eq_conj_transpose, (hψ _).elim.matrixIsPosDef.1.Eq,
          (hψ _).elim.matrixIsPosDef.inv.1.Eq]
      _ = 1 := t1
  simp_rw [t1, ← mul_assoc (Module.Dual.pi.matrixBlock ψ), t2, mul_one, one_mul, unitary.coe_star,
    star_star]

private theorem mul_inv_eq_iff_eq_mul_aux [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (b c : ∀ i, Matrix (s i) (s i) ℂ) :
    b * (Module.Dual.pi.matrixBlock ψ)⁻¹ = c ↔ b = c * Module.Dual.pi.matrixBlock ψ :=
  by
  constructor <;> rintro rfl <;> rw [mul_assoc]
  · rw [matrix_block_inv_mul_self, mul_one]
  · rw [matrix_block_self_mul_inv, mul_one]

theorem starAlgEquiv_commute_iff [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ) :
    (Commute (Module.Dual.pi.matrixBlock ψ) fun i => StarAlgEquiv.pi.unitary f i) ↔
      StarAlgEquiv.pi f (Module.Dual.pi.matrixBlock ψ) = Module.Dual.pi.matrixBlock ψ :=
  by
  nth_rw_rhs 1 [← StarAlgEquiv.of_pi_is_inner]
  rw [unitary.innerAutStarAlg_apply, unitary.coe_star]
  rw [unitary.inj_hMul (unitary.pi (StarAlgEquiv.pi.unitary f))]
  simp_rw [mul_assoc, unitary.coe_star_mul_self, mul_one]
  rw [eq_comm, Commute, SemiconjBy]
  rfl

theorem starAlgEquiv_is_isometry_tFAE [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    [∀ i, Nontrivial (s i)] (f : ∀ i, Matrix (s i) (s i) ℂ ≃⋆ₐ[ℂ] Matrix (s i) (s i) ℂ) :
    TFAE
      [(StarAlgEquiv.pi f) (Module.Dual.pi.matrixBlock ψ) = Module.Dual.pi.matrixBlock ψ,
        (StarAlgEquiv.pi f).toAlgEquiv.toLinearMap.adjoint =
          (StarAlgEquiv.pi f).symm.toAlgEquiv.toLinearMap,
        Module.Dual.pi ψ ∘ₗ (StarAlgEquiv.pi f).toAlgEquiv.toLinearMap = Module.Dual.pi ψ,
        ∀ x y, ⟪(StarAlgEquiv.pi f) x, (StarAlgEquiv.pi f) y⟫_ℂ = ⟪x, y⟫_ℂ,
        ∀ x : ∀ i, Matrix (s i) (s i) ℂ, ‖(StarAlgEquiv.pi f) x‖ = ‖x‖,
        Commute (Module.Dual.pi.matrixBlock ψ) fun i => StarAlgEquiv.pi.unitary f i] :=
  by
  tfae_have 5 ↔ 2
  · simp_rw [InnerProductSpace.Core.norm_eq_sqrt_inner,
      Real.sqrt_inj InnerProductSpace.Core.inner_self_nonneg
        InnerProductSpace.Core.inner_self_nonneg,
      ← Complex.ofReal_inj, inner_self_re, ← @sub_eq_zero _ _ _ ⟪_, _⟫_ℂ]
    have :
      ∀ x y,
        ⟪(StarAlgEquiv.pi f) x, (StarAlgEquiv.pi f) y⟫_ℂ - ⟪x, y⟫_ℂ =
          ⟪((StarAlgEquiv.pi f).toAlgEquiv.toLinearMap.adjoint ∘ₗ
                  (StarAlgEquiv.pi f).toAlgEquiv.toLinearMap -
                1)
              x,
            y⟫_ℂ :=
      by
      intro x y
      simp only [LinearMap.sub_apply, LinearMap.one_apply, inner_sub_left, LinearMap.comp_apply,
        LinearMap.adjoint_inner_left, StarAlgEquiv.coe_toAlgEquiv, AlgEquiv.toLinearMap_apply]
    simp_rw [this, inner_map_self_eq_zero, sub_eq_zero, StarAlgEquiv.comp_eq_iff,
      LinearMap.one_comp]
  rw [tfae_5_iff_2]
  tfae_have 4 ↔ 3
  · simp_rw [inner_eq, ← map_star (StarAlgEquiv.pi f), ← _root_.map_mul (StarAlgEquiv.pi f),
      LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      StarAlgEquiv.coe_toAlgEquiv]
    refine' ⟨fun h x => _, fun h x y => h _⟩
    rw [← one_mul x, ← star_one]
    exact h _ _
  rw [tfae_4_iff_3]
  letI := @matrix_block_invertible _ _ _ _ _ _ ψ _
  simp_rw [LinearMap.ext_iff, star_alg_equiv_adjoint_eq f, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv, mul_inv_eq_iff_eq_mul_aux,
    Module.Dual.pi.apply'', StarAlgEquiv.symm_apply_eq, _root_.map_mul,
    StarAlgEquiv.apply_symm_apply, pi.forall_left_mul, @eq_comm _ (Module.Dual.pi.matrixBlock ψ), ←
    block_diagonal'_alg_hom_apply, ← _root_.map_mul]
  tfae_have 1 ↔ 2
  · rw [iff_self_iff]; trivial
  tfae_have 1 → 3
  · intro i x
    nth_rw 1 [← i]
    simp_rw [← _root_.map_mul, StarAlgEquiv.pi_is_trace_preserving]
  tfae_have 3 → 1
  · intro i
    simp_rw [←
      StarAlgEquiv.pi_is_trace_preserving (fun i => (f i).symm)
        (Module.Dual.pi.matrixBlock ψ * (StarAlgEquiv.pi f) _),
      _root_.map_mul, StarAlgEquiv.pi_symm_apply_apply, block_diagonal'_alg_hom_apply, ←
      Module.Dual.pi.apply'', @eq_comm _ _ (Module.Dual.pi ψ _)] at i
    have := Module.Dual.pi.apply_eq_of ψ _ i
    rw [StarAlgEquiv.pi_symm_apply_eq] at this
    exact this.symm
  tfae_have 5 ↔ 6
  · rw [star_alg_equiv_commute_iff]
  tfae_finish

end Module.Dual.pi.IsFaithfulPosMap

end DirectSum

