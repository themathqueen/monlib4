/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Monlib.LinearAlgebra.MyMatrix.Basic

#align_import rep_theory.aut_mat

/-!
# Inner automorphisms

In this file we prove that any algebraic automorphism is an inner automorphism.

We work in a field `is_R_or_C 𝕜` and finite dimensional vector spaces and matrix algebras.

## main definition
`def linear_equiv.matrix_conj_of`: this defines an algebraic automorphism over $Mₙ$ given
  by $x \mapsto yxy^{-1}$ for some linear automorphism $y$ over $\mathbb{k}^n$

## main result
`automorphism_matrix_inner'''`: given an algebraic automorphism $f$ over a non-trivial
  finite-dimensional matrix algebra $M_n(\mathbb{k})$, we have that there exists a
  linear automorphism $T$ over the vector space $\mathbb{k}^n$ such that `f = T.matrix_conj_of`
-/


open scoped BigOperators

variable {n R 𝕜 : Type _} [Field 𝕜] [Fintype n]

local notation "L(" V ")" => V →ₗ[𝕜] V

local notation "M" n => Matrix n n 𝕜

local notation "Mₙ" n => Matrix n n R

section Matrix

open Matrix

open scoped Matrix

/-- we define `T` as a linear map on `𝕜ⁿ` given by `x ↦ (f (vecMulVec x y)) z`,
  where `f` is a linear map on `Mₙ` and `y,z ∈ 𝕜ⁿ` -/
private def mat_T [Semiring R] (f : (Mₙ n) →ₗ[R] Mₙ n) (y z : n → R) : (n → R) →ₗ[R] n → R
    where
  toFun x := (f (vecMulVec x y)).mulVec z
  map_add' w p := by simp_rw [vecMulVec_eq, col_add w p, Matrix.add_mul, map_add, add_mulVec]
  map_smul' w r := by
    simp_rw [vecMulVec_eq, RingHom.id_apply, col_smul, smul_mul, LinearMap.map_smul,
      smul_mulVec_assoc]

private theorem mat_T_apply [Semiring R] (f : (Mₙ n) →ₗ[R] Mₙ n) (y z r : n → R) :
    mat_T f y z r = (f (vecMulVec r y)).mulVec z :=
  rfl

-- TODO: generalize this...
/-- any automorphism of `Mₙ` is inner given by `𝕜ⁿ`,
  in particular, given a bijective linear map `f ∈ L(Mₙ)` such that
  `f(ab)=f(a)f(b)`, we have that there exists a matrix `T ∈ Mₙ` such that
  `∀ a ∈ Mₙ : f(a) * T = T * a` and `T` is invertible -/
theorem automorphism_matrix_inner [Field R] [DecidableEq n] [h5 : Nonempty n] (f : (Mₙ n) ≃ₐ[R] Mₙ n) :
    ∃ T : Mₙ n, (∀ a : Mₙ n, f a * T = T * a) ∧ Function.Bijective (Matrix.toLin' T) :=
  by
  -- let hn := h5.some
  -- there exists a non-zero vector
  have : ∃ u : n → R, u ≠ 0 := ⟨1, one_ne_zero⟩
  have t1 := this
  -- let `u, y ∈ 𝕜ⁿ` such that `u,y ≠ 0`
  cases' this with u hu
  cases' t1 with y hy
  -- `f (col u * (col y)ᴴ) ≠ 0` iff `col u * (col y)ᴴ ≠ 0`
  -- (and we know `col u * (col y)ᴴ ≠ 0` since `u,y ≠ 0` by `vecMulVec_ne_zero`)
  have f_ne_zero_iff : f (vecMulVec u y) ≠ 0 ↔ vecMulVec u y ≠ 0 :=
    by
    rw [not_iff_not]
    exact
      ⟨fun z => (injective_iff_map_eq_zero f).mp f.bijective.1 _ z, fun z => by rw [z, map_zero]⟩
  -- there exists a vector `z ∈ 𝕜ⁿ` such that `f (col u * ) z ≠ 0`
  have : ∃ z : n → R, (f (vecMulVec u y)) *ᵥ z ≠ 0 :=
    by
    simp_rw [Ne.def, ← Classical.not_forall]
    suffices ¬f (vecMulVec u y) = 0
      by
      simp_rw [mulVec_eq, zero_mulVec] at this
      exact this
    rw [← Ne.def, f_ne_zero_iff]
    exact vecMulVec_ne_zero hu hy
  -- let `z ∈ 𝕜ⁿ` such that `f (uy⋆) z ≠ 0`
  cases' this with z hz
  -- let `T ∈ L(𝕜ⁿ)` such that `x ↦ xy⋆ z`
  let T := mat_T f.toLinearMap y z
  -- we now use `M(T)` as our matrix
  use LinearMap.toMatrix' T
  -- it is easy to show `(f a) * M(T) = M(T) * a`
  have fir : ∀ a : Mₙ n, f a * (LinearMap.toMatrix' T) = (LinearMap.toMatrix' T) * a :=
    by
    simp_rw [mulVec_eq]
    intro A x
    symm
    calc
      ((LinearMap.toMatrix' T) * A) *ᵥ x = T (A *ᵥ x) :=
        by ext; rw [← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      _ = (f (vecMulVec (A *ᵥ x) y)) *ᵥ z := by
        rw [mat_T_apply, AlgEquiv.toLinearMap_apply]
      _ = (f (A * vecMulVec x y)) *ᵥ z := by
        simp_rw [vecMulVec_eq, col_mulVec, ← Matrix.mul_assoc]
      _ = (f A * f (vecMulVec x y)) *ᵥ z := by simp_rw [AlgEquiv.map_mul]
      _ = (f A) *ᵥ (T x) := by
        simp_rw [← mulVec_mulVec, ← AlgEquiv.toLinearMap_apply, ← mat_T_apply _ y z]
      _ = (f A * (LinearMap.toMatrix' T)) *ᵥ x := by
        simp_rw [← mulVec_mulVec, ← toLin'_apply (LinearMap.toMatrix' T), toLin'_toMatrix']
  refine' ⟨fir, _⟩
  -- we now show `M(T)` is invertible (or, equivalently, `T` is invertible)
  simp_rw [Matrix.toLin'_toMatrix']
  -- it suffices to show `T` is surjective
  suffices Function.Surjective T by exact ⟨LinearMap.injective_iff_surjective.mpr this, this⟩
  -- let `w ∈ 𝕜ⁿ`
  intro w
  -- clearly `T u ≠ 0`
  have hi : T u ≠ 0 := by
    rw [mat_T_apply _ y z]
    exact hz
  -- there exists a vector `d ∈ 𝕜ⁿ` such that `(T u) * d = 1`
  have this1 : ∃ d : n → R, T u ⬝ᵥ d = 1 :=
    by
    rw [← vec_ne_zero] at hi
    cases' hi with q hq
    use Pi.single q (T u q)⁻¹
    rw [dotProduct_single, mul_inv_cancel hq]
  -- there also exists a matrix `B ∈ Mₙ` such that `(f B) (T u) = w`
  have this2 : ∃ B : Mₙ n, (f B) *ᵥ (T u) = w :=
    by
    -- by `this1` we have `d ∈ 𝕜ⁿ` such that `(T u) d = 1`
    cases' this1 with d hd
    -- and since `f` is bijective, we have that there exists a matrix `B` such that
    -- `f B = |w⟩⟨d|`
    cases' f.bijective.2 (vecMulVec w d) with B hB
    -- we use this `B` to show our desired result (i.e., `(f B) (T u) = w`)
    -- `(f B) (T u) = wd⋆ * (T u) |w⟩ * d * (T u) = w = w`
    use B
    rw [hB, vecMulVec_eq, ← mulVec_mulVec]
    suffices (row d) *ᵥ (T u) = 1 by
      ext
      simp_rw [this, mulVec, dotProduct, col_apply, Fintype.univ_punit, Pi.one_apply, mul_one,
        Finset.sum_const, Finset.card_singleton, nsmul_eq_mul, Nat.cast_one, one_mul]
    ext
    simp_rw [mulVec, Pi.one_apply, ← hd, dotProduct, row_apply, mul_comm]
  -- now let `B ∈ Mₙ` be our matrix such that `(f B) (T u) = w`
  cases' this2 with B hB
  -- then we let our vector be `M⁻¹(B) u`
  use (toLin' B) u
  -- it remains to then show that we have `T (M⁻¹(B) u) = w`
  -- this can be seen from:
  -- `w = (f B) (T u) = (f B) (M(T)u) = ((f B) * M(T)) u = (M(T) * B) u = M(T) (Bu)`
  --             `... = T (M⁻¹(B) u)`
  rw [← toLin'_toMatrix' T]
  simp_rw [toLin'_apply, mulVec_mulVec, ← fir, ← mulVec_mulVec, ← toLin'_apply (LinearMap.toMatrix' T),
    toLin'_toMatrix']
  exact hB

private def g_mat [DecidableEq n] (a : M n) (b : (n → 𝕜) → n → 𝕜)
    (hb : Function.LeftInverse b (toLin' a) ∧ Function.RightInverse b (toLin' a)) : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜
    where
  toFun x := (toLin' a) x
  map_add' := a.toLin'.map_add'
  map_smul' := a.toLin'.map_smul'
  invFun := b
  left_inv := hb.1
  right_inv := hb.2

private theorem g_mat_apply [DecidableEq n] (a : M n) (b : (n → 𝕜) → n → 𝕜)
    (hb : Function.LeftInverse b (toLin' a) ∧ Function.RightInverse b (toLin' a)) (x : n → 𝕜) :
    g_mat a b hb x = (toLin' a) x :=
  rfl

open scoped Matrix

/-- given an automorphic algebraic equivalence `f` on `Mₙ`, we have
  that there exists a linear equivalence `T` such that
  `f(a) = M(T) * a * M(⅟ T)`,
  i.e., any automorphic algebraic equivalence on `Mₙ` is inner -/
theorem automorphism_matrix_inner'' [DecidableEq n] [Nonempty n] (f : (M n) ≃ₐ[𝕜] M n) :
    ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜,
      ∀ a : M n, f a = (LinearMap.toMatrix' T)
        * a * (LinearMap.toMatrix' (T.symm)) :=
  by
  cases' automorphism_matrix_inner f with T hT
  cases' Function.bijective_iff_has_inverse.mp hT.2 with r hr
  let g := g_mat T r hr
  exists g
  intro a
  have : g.toLinearMap = toLin' T := by
    ext
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, LinearMap.coe_single,
      Function.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_single, mul_one, g_mat_apply T r hr,
      Matrix.toLin'_apply, Matrix.mulVec_single, mul_one]
  rw [this, LinearMap.toMatrix'_toLin', ← hT.1, ← LinearMap.toMatrix'_toLin' T, Matrix.mul_assoc, ←
    this]
  symm
  calc
    f a * ((LinearMap.toMatrix' g) * (LinearMap.toMatrix' g.symm)) =
        f a * (LinearMap.toMatrix' (g.symm.trans g)) :=
      by simp_rw [← LinearEquiv.comp_coe, LinearMap.toMatrix'_comp]
    _ = f a := ?_
  simp_rw [LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id,
    Matrix.mul_one]

def Algebra.autInner {R E : Type _} [CommSemiring R] [Semiring E] [Algebra R E] (x : E)
    [Invertible x] : E ≃ₐ[R] E where
  toFun y := x * y * ⅟ x
  invFun y := ⅟ x * y * x
  left_inv u := by simp_rw [← mul_assoc, invOf_mul_self, one_mul, mul_invOf_mul_self_cancel]
  right_inv u := by simp_rw [← mul_assoc, mul_invOf_self, one_mul, mul_mul_invOf_self_cancel]
  map_add' y z := by simp_rw [mul_add, add_mul]
  commutes' r := by
    simp_rw [Algebra.algebraMap_eq_smul_one, mul_smul_one, smul_mul_assoc, mul_invOf_self]
  map_mul' y z := by simp_rw [mul_assoc, invOf_mul_self_assoc]

theorem Algebra.autInner_apply {R E : Type _} [CommSemiring R] [Semiring E] [Algebra R E] (x : E)
    [Invertible x] (y : E) : (Algebra.autInner x : E ≃ₐ[R] E) y = x * y * ⅟ x :=
  rfl

theorem Algebra.autInner_symm_apply {R E : Type _} [CommSemiring R] [Semiring E] [Algebra R E]
    (x : E) [Invertible x] (y : E) : (Algebra.autInner x : E ≃ₐ[R] E).symm y = ⅟ x * y * x :=
  rfl

theorem Algebra.autInner_hMul_autInner {R E : Type _} [CommSemiring R] [Semiring E] [Algebra R E]
    (x y : E) [hx : Invertible x] [hy : Invertible y] :
    (Algebra.autInner x : E ≃ₐ[R] E) * Algebra.autInner y =
      @Algebra.autInner _ _ _ _ _ (x * y) (hx.mul hy) :=
  by
  ext
  simp_rw [AlgEquiv.mul_apply, Algebra.autInner_apply, invOf_mul, mul_assoc]

private theorem automorphism_matrix_inner''' [DecidableEq n] [Nonempty n] (f : (M n) ≃ₐ[𝕜] M n) :
    ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜,
      f = @Algebra.autInner 𝕜 (M n) _ _ _
        (LinearMap.toMatrix' (T : (n → 𝕜) →ₗ[𝕜] n → 𝕜)) T.toInvertibleMatrix :=
  by
  cases' automorphism_matrix_inner'' f with T hT
  exists T
  ext
  simp_rw [Algebra.autInner_apply, hT]
  rfl

theorem aut_mat_inner [DecidableEq n] (f : (M n) ≃ₐ[𝕜] M n) :
    ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜,
      f = @Algebra.autInner 𝕜 (M n) _ _ _ (LinearMap.toMatrix' (T : (n → 𝕜) →ₗ[𝕜] n → 𝕜))
        T.toInvertibleMatrix :=
  by
  rcases (em (Nonempty n)) with (hn | hn)
  · exact automorphism_matrix_inner''' f
  · use 1
    ext x i j
    simp only [not_nonempty_iff, isEmpty_iff, eq_self_iff_true, not_exists, not_true] at hn
    exfalso
    exact hn i

theorem aut_mat_inner' [DecidableEq n] (f : (M n) ≃ₐ[𝕜] M n) :
    ∃ T : GL n 𝕜, f = @Algebra.autInner 𝕜 (M n) _ _ _ (T : M n) (Units.invertible T) :=
  by
  cases' aut_mat_inner f with T hT
  let T' : M n := LinearMap.toMatrix' T
  have hT' : T' = LinearMap.toMatrix' T := rfl
  let Tinv : M n := LinearMap.toMatrix' T.symm
  have hTinv : Tinv = LinearMap.toMatrix' T.symm := rfl
  refine' ⟨⟨T', Tinv, _, _⟩, by congr⟩
  all_goals
    simp only [hT', hTinv, ← LinearMap.toMatrix'_mul, LinearMap.mul_eq_comp, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.toMatrix'_id]


theorem aut_mat_inner_trace_preserving [DecidableEq n] (f : (M n) ≃ₐ[𝕜] M n) (x : M n) :
    (f x).trace = x.trace := by
  obtain ⟨T, rfl⟩ := aut_mat_inner' f
  rw [Algebra.autInner_apply, trace_mul_comm, Matrix.invOf_mul_self_assoc]

/-- if a matrix commutes with all matrices, then it is equal to a scalar
  multiplied by the identity -/
theorem Matrix.commutes_with_all_iff {R : Type _} [CommSemiring R] [DecidableEq n]
    {x : Matrix n n R} : (∀ y : Matrix n n R, Commute y x) ↔ ∃ α : R, x = α • 1 :=
  by
  simp_rw [Commute, SemiconjBy]
  constructor
  · intro h
    by_cases h' : x = 0
    · exact ⟨0, by rw [h', zero_smul]⟩
    simp_rw [← eq_zero, Classical.not_forall] at h'
    obtain ⟨i, _, _⟩ := h'
    have : x = diagonal x.diag := by
      ext k l
      specialize h (stdBasisMatrix l k 1)
      simp_rw [← Matrix.ext_iff, mul_apply, stdBasisMatrix, boole_mul, mul_boole, ite_and,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
      specialize h k k
      simp_rw [diagonal, of_apply, Matrix.diag]
      simp_rw [if_true, @eq_comm _ l k] at h
      exact h.symm
    have this1 : ∀ k l : n, x k k = x l l := by
      intro k l
      specialize h (stdBasisMatrix k l 1)
      simp_rw [← Matrix.ext_iff, mul_apply, stdBasisMatrix, boole_mul, mul_boole, ite_and,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
      specialize h k l
      simp_rw [if_true] at h
      exact h.symm
    use x i i
    ext k l
    simp_rw [Matrix.smul_apply, one_apply, smul_ite, smul_zero, smul_eq_mul, mul_one]
    nth_rw 1 [this]
    simp_rw [diagonal, diag, of_apply, this1 i k]
  · rintro ⟨α, rfl⟩ y
    simp_rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

private theorem matrix.one_ne_zero {R : Type _} [Semiring R] [One R] [Zero R] [NeZero (1 : R)]
    [DecidableEq n] [hn : Nonempty n] : (1 : Matrix n n R) ≠ 0 :=
  by
  simp_rw [Ne.def, ← Matrix.eq_zero, Matrix.one_apply, ite_eq_right_iff, _root_.one_ne_zero, imp_false,
    Classical.not_forall, Classical.not_not]
  exact ⟨hn.some, hn.some, rfl⟩

theorem Matrix.commutes_with_all_iff_of_ne_zero [DecidableEq n] [Nonempty n] {x : Matrix n n 𝕜}
    (hx : x ≠ 0) : (∀ y : Matrix n n 𝕜, Commute y x) ↔ ∃! α : 𝕜ˣ, x = (α : 𝕜) • 1 :=
  by
  simp_rw [Matrix.commutes_with_all_iff]
  refine' ⟨fun h => _, fun ⟨α, hα, _⟩ => ⟨α, hα⟩⟩
  obtain ⟨α, hα⟩ := h
  have : α ≠ 0 := by
    intro this
    rw [this, zero_smul] at hα
    contradiction
  refine' ⟨Units.mk0 α this, hα, fun y hy => _⟩
  simp only at hy
  rw [hα, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at hy
  simp_rw [matrix.one_ne_zero, or_false_iff] at hy
  simp_rw [Units.mk0, hy, Units.mk_val]

theorem Algebra.autInner_eq_autInner_iff [DecidableEq n] (x y : Matrix n n 𝕜) [Invertible x]
    [Invertible y] :
    (Algebra.autInner x : Matrix n n 𝕜 ≃ₐ[𝕜] Matrix n n 𝕜) = Algebra.autInner y ↔
      ∃ α : 𝕜, y = α • x :=
  by
  have : (∃ α : 𝕜, y = α • x) ↔ ∃ α : 𝕜, ⅟ x * y = α • 1 := by
    simp_rw [invOf_eq_nonsing_inv, inv_mul_eq_iff_eq_mul_of_invertible,
      Matrix.mul_smul, Matrix.mul_one]
  simp_rw [this, AlgEquiv.ext_iff, Algebra.autInner_apply, ← Matrix.commutes_with_all_iff, Commute,
    SemiconjBy, invOf_eq_nonsing_inv, ← mul_inv_eq_iff_eq_mul_of_invertible,
    Matrix.mul_assoc, ← inv_mul_eq_iff_eq_mul_of_invertible, inv_inv_of_invertible]

end Matrix
