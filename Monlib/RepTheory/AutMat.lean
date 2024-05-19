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
import Monlib.Preq.Set
import Monlib.Preq.Submodule
import Monlib.Preq.StarAlgEquiv
import Monlib.LinearAlgebra.MyMatrix.PiMat

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

@[pp_dot] def AlgEquiv.IsInner {R E : Type*} [CommSemiring R] [Semiring E]
  [Algebra R E]
  (f : E ≃ₐ[R] E) : Prop :=
∃ (a : E) (ha : Invertible a), f = Algebra.autInner a

@[simps] def AlgEquiv.prod_map {K R₁ R₂ R₃ R₄ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  [Algebra K R₁] [Algebra K R₂] [Algebra K R₃] [Algebra K R₄]
  (f : R₁ ≃ₐ[K] R₂) (g : R₃ ≃ₐ[K] R₄) :
  (R₁ × R₃) ≃ₐ[K] (R₂ × R₄) :=
{ toFun := Prod.map f g
  invFun := Prod.map f.symm g.symm
  left_inv := λ x => by simp
  right_inv := λ x => by simp
  map_add' := λ x y => by simp
  map_mul' := λ x y => by simp
  commutes' := λ r => by simp }

@[simps] def AlgEquiv.Pi {K ι : Type*} [CommSemiring K] {R : ι → Type*} [∀ i, Semiring (R i)]
  [∀ i, Algebra K (R i)] (f : Π i, R i ≃ₐ[K] R i) : (Π i, R i) ≃ₐ[K] (Π i, R i) :=
{ toFun := λ x i => f i (x i)
  invFun := λ x i => (f i).symm (x i)
  left_inv := λ x => funext λ i => (f i).left_inv (x i)
  right_inv := λ x => funext λ i => (f i).right_inv (x i)
  map_add' := λ x y => funext λ i => (f i).map_add (x i) (y i)
  map_mul' := λ x y => funext λ i => (f i).map_mul (x i) (y i)
  commutes' := λ r => funext λ i => (f i).commutes r }

instance Prod.invertible_fst {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
  {a : R₁ × R₂} [ha : Invertible a] :
  Invertible a.1 :=
by
  use (⅟ a).1
  on_goal 1 => have := ha.invOf_mul_self
  on_goal 2 => have := ha.mul_invOf_self
  all_goals
    rw [Prod.mul_def, Prod.mk_eq_one] at this
    simp_rw [this]
instance Prod.invertible_snd {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
  {a : R₁ × R₂} [ha : Invertible a] :
  Invertible a.2 :=
by
  use (⅟ a).2
  on_goal 1 => have := ha.invOf_mul_self
  on_goal 2 => have := ha.mul_invOf_self
  all_goals
    rw [Prod.mul_def, Prod.mk_eq_one] at this
    simp_rw [this]
instance Prod.invertible {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
  {a : R₁} {b : R₂} [ha : Invertible a] [hb : Invertible b] :
  Invertible (a, b) :=
⟨(⅟ a, ⅟ b), by simp, by simp⟩

instance Pi.invertible_i {ι : Type*} {R : ι → Type*} [Π i, Semiring (R i)]
  [Π i, Semiring (R i)] {a : Π i, R i} [ha : Invertible a] (i : ι) :
  Invertible (a i) :=
by
  use (⅟ a) i
  on_goal 1 => have := ha.invOf_mul_self
  on_goal 2 => have := ha.mul_invOf_self
  all_goals
    rw [Pi.mul_def, Function.funext_iff] at this
    simp_rw [this]
    rfl
instance Pi.invertible {ι : Type*} {R : ι → Type*} [Π i, Semiring (R i)]
  [Π i, Semiring (R i)] {a : Π i, R i} [ha : Π i, Invertible (a i)] :
  Invertible a :=
⟨λ i => ⅟ (a i), by simp_rw [mul_def, invOf_mul_self]; rfl,
  by simp_rw [mul_def, mul_invOf_self]; rfl⟩

theorem AlgEquiv.prod_isInner_iff_prod_map {K R₁ R₂ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂]
  [Algebra K R₁] [Algebra K R₂] (f : (R₁ × R₂) ≃ₐ[K] (R₁ × R₂)) :
  AlgEquiv.IsInner f
    ↔ ∃ (a : R₁) (ha : Invertible a) (b : R₂) (hb : Invertible b),
      f = AlgEquiv.prod_map (Algebra.autInner a) (Algebra.autInner b) :=
by
  constructor
  . rintro ⟨a, ha, h⟩
    use a.1, by infer_instance, a.snd, by infer_instance
    exact h
  . rintro ⟨a, ha, b, hb, h⟩
    use (a, b), by infer_instance
    exact h

theorem AlgEquiv.pi_isInner_iff_pi_map {K ι : Type*} {R : ι → Type*} [CommSemiring K]
  [Π i, Semiring (R i)] [Π i, Algebra K (R i)]
  (f : (Π i, R i) ≃ₐ[K] (Π i, R i)) :
  AlgEquiv.IsInner f
    ↔ ∃ (a : Π i, R i) (ha : Π i, Invertible (a i)),
      f = AlgEquiv.Pi (λ i => Algebra.autInner (a i)) :=
by
  constructor
  . rintro ⟨a, ha, h⟩
    use (λ i => a i), by infer_instance
    rw [h]
    rfl
  . rintro ⟨a, ha, h⟩
    use (λ i => a i), by infer_instance
    rw [h]
    rfl

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


lemma _root_.Matrix.center {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n] :
  Set.center (Matrix n n R) = Submodule.span R {(1 : Matrix n n R)} :=
by
  ext x
  rw [Set.mem_center_iff, isMulCentral_iff]
  simp_rw [mul_assoc, forall_const, and_self, and_true, SetLike.mem_coe]
  have := @Matrix.commutes_with_all_iff _ _ _ _ _ x
  simp_rw [Commute, SemiconjBy] at this
  simp_rw [@eq_comm _ (x * _), this, Submodule.mem_span_singleton, eq_comm]

lemma _root_.Matrix.prod_center {R n m : Type*} [CommSemiring R] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :
  Set.center (Matrix n n R × Matrix m m R)
    = (Submodule.span R {((1 : Matrix n n R), (0 : Matrix m m R)), (0, 1)}) :=
by
  simp_rw [Set.center_prod, Matrix.center]
  ext x
  simp only [Set.mem_prod, SetLike.mem_coe, Submodule.mem_span_pair,
    Submodule.mem_span_singleton, Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add,
    add_zero]
  nth_rw 3 [← Prod.eta x]
  simp_rw [Prod.ext_iff, exists_and_left, exists_and_right]

lemma _root_.Matrix.pi_center {R ι : Type*} [CommSemiring R] [DecidableEq ι]
  [Fintype ι] {n : ι → Type*}
  [Π i, DecidableEq (n i)] [Π i, Fintype (n i)] :
  Set.center (Π i : ι, Matrix (n i) (n i) R) = { x | ∀ i, x i ∈ Set.center (Matrix (n i) (n i) R) } :=
by
  simp_rw [Set.center_pi, Matrix.center]
  ext x
  simp only [Set.mem_pi, Set.mem_univ, SetLike.mem_coe, forall_true_left]
  simp only [Submodule.mem_span_singleton, mem_span_range_iff_exists_fun,
    ← Pi.single_smul, Function.funext_iff]
  rfl
lemma PiMat.center {R ι : Type*} [CommSemiring R] [DecidableEq ι] [Fintype ι] {n : ι → Type*}
  [Π i, DecidableEq (n i)] [Π i, Fintype (n i)] :
  Set.center (PiMat R ι n) = { x | ∀ i, x i ∈ Set.center (Matrix (n i) (n i) R) } :=
Matrix.pi_center

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

theorem Matrix.one_ne_zero_iff {𝕜 n : Type*} [DecidableEq n]
  [Zero 𝕜] [One 𝕜] [NeZero (1 : 𝕜)] :
  (1 : Matrix n n 𝕜) ≠ (0 : Matrix n n 𝕜) ↔ Nonempty n :=
by
  simp_rw [Ne.def, ← Matrix.ext_iff, one_apply, zero_apply, not_forall]
  constructor
  . rintro ⟨x, _, _⟩
    use x
  . intro h
    obtain ⟨i⟩ := h
    use i, i
    simp only [↓reduceIte, one_ne_zero, not_false_iff]

theorem Matrix.one_eq_zero_iff {𝕜 n : Type*} [DecidableEq n]
  [Zero 𝕜] [One 𝕜] [NeZero (1 : 𝕜)] :
  (1 : Matrix n n 𝕜) = (0 : Matrix n n 𝕜) ↔ IsEmpty n :=
by rw [← not_nonempty_iff, ← @one_ne_zero_iff 𝕜 n, not_ne_iff]

theorem AlgEquiv.matrix_prod_aut {𝕜 n m : Type*} [Field 𝕜] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  [Nonempty n] [Nonempty m]
  (f : (Matrix n n 𝕜 × Matrix m m 𝕜) ≃ₐ[𝕜] (Matrix n n 𝕜 × Matrix m m 𝕜)) :
  (f (1, 0) = (1, 0) ∧ f (0, 1) = (0, 1)) ∨ (f (1, 0) = (0, 1) ∧ f (0, 1) = (1, 0)) :=
by
  let e₁ : (Matrix n n 𝕜 × Matrix m m 𝕜) := (1, 0)
  let e₂ : (Matrix n n 𝕜 × Matrix m m 𝕜) := (0, 1)
  have he₁ : e₁ = (1, 0) := rfl
  have he₂ : e₂ = (0, 1) := rfl
  rw [← he₁, ← he₂]
  have h₁ : e₁ + e₂ = 1 := by
    rw [he₁, he₂]
    simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk_eq_one, and_self]
  have h₂ : e₁ * e₂ = 0 := by
    rw [he₁, he₂]
    simp only [Prod.mk_mul_mk, mul_zero, mul_one, Prod.mk_eq_zero, and_self]
  have h₃ : e₂ * e₁ = 0 := by
    rw [he₁, he₂]
    simp only [Prod.mk_mul_mk, mul_one, mul_zero, Prod.mk_eq_zero, and_self]
  have h₄ : e₁ * e₁ = e₁ := by
    rw [he₁]
    simp only [Prod.mk_mul_mk, mul_one, mul_zero]
  have h₅ : e₂ * e₂ = e₂ := by
    rw [he₂]
    simp only [Prod.mk_mul_mk, mul_zero, mul_one]
  have h10 : ∀ a : 𝕜, a • e₁ = (a • 1, 0) := by
    intro a
    simp_rw [e₁, Prod.smul_mk, smul_zero]
  have h11 : ∀ a : 𝕜, a • e₂ = (0, a • 1) := by
    intro a
    simp_rw [e₂, Prod.smul_mk, smul_zero]
  have hf := AlgEquiv.image_center f
  rw [Set.ext_iff] at hf
  have he₁' : e₁ ∈ (Submodule.span 𝕜 {((1 : Matrix n n 𝕜), (0 : Matrix m m 𝕜)), (0, 1)} : Set _) := by
    simp only [SetLike.mem_coe]
    simp_rw [Submodule.mem_span_pair, ← he₁, ← he₂, h10, h11, Prod.mk_add_mk, add_zero]
    use 1, 0
    simp only [one_smul, zero_smul, add_zero]
  have he₂' : e₂ ∈ (Submodule.span 𝕜 {((1 : Matrix n n 𝕜), (0 : Matrix m m 𝕜)), (0, 1)} : Set _) := by
    simp only [SetLike.mem_coe]
    simp_rw [Submodule.mem_span_pair, ← he₁, ← he₂, h10, h11, Prod.mk_add_mk, add_zero]
    use 0, 1
    simp only [one_smul, zero_smul, zero_add]
  have : Set.center (Matrix n n 𝕜 × Matrix m m 𝕜) = Submodule.span 𝕜 {((1 : Matrix n n 𝕜), (0 : Matrix m m 𝕜)), (0, 1)} :=
  Matrix.prod_center
  rw [← this] at he₁' he₂'
  have hf1 := (hf e₁).mpr he₁'
  have hf2 := (hf e₂).mpr he₂'
  simp only [Set.mem_image, SetLike.coe_mem] at hf1 hf2
  have H : ∀ x : (Matrix n n 𝕜 × Matrix m m 𝕜),
    x ∈ Set.center (Matrix n n 𝕜 × Matrix m m 𝕜) ↔ ∃ a b : 𝕜, a • e₁ + b • e₂ = f x := by
      simp_rw [← Submodule.mem_span_pair]
      intro x
      have this1 : f x ∈ Submodule.span 𝕜 {e₁, e₂} ↔ f x ∈ (Submodule.span 𝕜 {e₁, e₂} : Set _) := by rfl
      rw [this1, he₁, he₂, ← this]
      nth_rw 2 [← hf]
      simp only [Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right, Subtype.coe_prop]
  obtain ⟨α, β, h₆⟩ : ∃ a b : 𝕜, a • e₁ + b • e₂ = f e₁ := (H e₁).mp he₁'
  obtain ⟨γ, ζ, h₇⟩ : ∃ a b : 𝕜, a • e₁ + b • e₂ = f e₂ := (H e₂).mp he₂'
  obtain ⟨a, ha1, ha2⟩ := hf1
  obtain ⟨b, hb1, hb2⟩ := hf2
  simp_rw [this, SetLike.mem_coe, Submodule.mem_span_pair] at ha1 hb1
  obtain ⟨c, d, hcd⟩ := ha1
  obtain ⟨c₂, d₂, hcd2⟩ := hb1
  have h₈ : f (e₁ * e₂) = 0 := by rw [h₂, f.map_zero]
  have h₉ : f (e₁ + e₂) = 1 := by rw [h₁, f.map_one]
  simp_rw [f.map_mul, ← h₆, ← h₇, add_mul, mul_add, smul_mul_smul, h₂, h₃, h₄, h₅, smul_zero,
    add_zero, zero_add, h10, h11, Prod.mk_add_mk, add_zero, zero_add, Prod.zero_eq_mk,
    Prod.ext_iff, smul_eq_zero, mul_eq_zero, one_ne_zero, or_false] at h₈
  rw [f.map_add, ← h₆, ← h₇, add_add_add_comm] at h₉
  simp_rw [← add_smul, Prod.one_eq_mk, h10, h11, Prod.mk_add_mk, add_zero, zero_add,
    Prod.ext_iff, smul_one_eq_one_iff, not_isEmpty_of_nonempty, or_false] at h₉
  by_cases hα : α ≠ 0
  . simp_rw [hα, false_or] at h₈
    rw [h₈.1, add_zero] at h₉
    rw [h₉.1] at h₆
    rw [h₈.1, zero_smul, zero_add] at h₇
    have hζ : ζ ≠ 0 := by
      intro hζ
      simp_rw [hζ, zero_smul, @eq_comm _ (0 : Matrix n n 𝕜 × Matrix m m 𝕜),
        AlgEquiv.map_eq_zero_iff, he₂, Prod.zero_eq_mk, Prod.ext_iff,
        one_ne_zero, and_false] at h₇
    simp_rw [hζ, or_false] at h₈
    rw [h₈.2, zero_add] at h₉
    rw [h₉.2, one_smul] at h₇
    rw [one_smul, h₈.2, zero_smul, add_zero] at h₆
    left
    exact ⟨h₆.symm, h₇.symm⟩
  . rw [not_ne_iff] at hα
    rw [hα] at h₈ h₉ h₆
    simp only [true_or, zero_add, true_and] at h₈ h₉
    rw [zero_smul, zero_add] at h₆
    rw [h₉.1, one_smul] at h₇
    have hβ : β ≠ 0 := by
      intro hβ
      simp_rw [hβ, zero_smul, @eq_comm _ (0 : Matrix n n 𝕜 × Matrix m m 𝕜),
        AlgEquiv.map_eq_zero_iff, he₁, Prod.zero_eq_mk, Prod.ext_iff,
        one_ne_zero, false_and] at h₆
    simp_rw [hβ, false_or] at h₈
    rw [h₈, add_zero] at h₉
    rw [h₉.2, one_smul] at h₆
    rw [h₈, zero_smul, add_zero] at h₇
    right
    exact ⟨h₆.symm, h₇.symm⟩

lemma _root_.Algebra.prod_one_zero_mul {R₁ R₂ : Type*}
  [Semiring R₁] [Semiring R₂] (a : R₁ × R₂) :
  (1, 0) * a = (a.1, 0) :=
by simp_rw [Prod.mul_def, one_mul, zero_mul]
lemma _root_.Algebra.prod_zero_one_mul {R₁ R₂ : Type*}
  [Semiring R₁] [Semiring R₂] (a : R₁ × R₂) :
  (0, 1) * a = (0, a.2) :=
by simp_rw [Prod.mul_def, zero_mul, one_mul]

macro "prod_map_add" : tactic =>
  `(tactic|
    (simp only
     nth_rw 1 [← add_zero (0 : _)]
     simp_rw [← Prod.mk_add_mk, AlgEquiv.map_add]
     rfl))
macro "prod_map_mul" : tactic =>
  `(tactic|
    (simp only
     nth_rw 1 [← zero_mul (0 : _)]
     simp_rw [← Prod.mk_mul_mk, AlgEquiv.map_mul]
     rfl))

def AlgEquiv.of_prod_map₁₁ {K R₁ R₂ R₃ R₄ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  [Algebra K R₁] [Algebra K R₂] [Algebra K R₃] [Algebra K R₄]
  (f : (R₁ × R₂) ≃ₐ[K] (R₃ × R₄))
  (hf : f (1, 0) = (1, 0)) :
  R₁ ≃ₐ[K] R₃ :=
have Hf : (1, 0) = f.symm (1, 0) := by
  rw [← hf]; simp only [symm_apply_apply, and_self]
{ toFun := λ a => (f (a, 0)).1
  invFun := λ a => (f.symm (a, 0)).1
  left_inv := λ a => by
    have : ((f.symm ((f (a, 0)).1, 0)).1, 0) = (a, 0) := by
      rw [← Algebra.prod_one_zero_mul, f.symm.map_mul, ← Hf, f.symm_apply_apply,
        Algebra.prod_one_zero_mul]
    simp_rw [Prod.ext_iff, and_true] at this
    exact this
  right_inv := λ a => by
    have : ((f ((f.symm (a, 0)).1, 0)).1, 0) = (a, 0) := by
      rw [← Algebra.prod_one_zero_mul, f.map_mul, hf, f.apply_symm_apply,
        Algebra.prod_one_zero_mul]
    simp_rw [Prod.ext_iff, and_true] at this
    exact this
  map_add' := λ a b => by prod_map_add
  map_mul' := λ a b => by prod_map_mul
  commutes' := λ r => by
    simp only
    simp_rw [Algebra.algebraMap_eq_smul_one]
    nth_rw 1 [← smul_zero r]
    rw [← Prod.smul_mk, f.map_smul, Prod.smul_fst, hf] }
def AlgEquiv.of_prod_map₂₂ {K R₁ R₂ R₃ R₄ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  [Algebra K R₁] [Algebra K R₂] [Algebra K R₃] [Algebra K R₄]
  (f : (R₁ × R₂) ≃ₐ[K] (R₃ × R₄))
  (hf : f (0, 1) = (0, 1)) :
  R₂ ≃ₐ[K] R₄ :=
have Hf : (0, 1) = f.symm (0, 1) := by
  rw [← hf]; simp only [symm_apply_apply, and_self]
{ toFun := λ a => (f (0, a)).2
  invFun := λ a => (f.symm (0, a)).2
  left_inv := λ a => by
    have : (0, (f.symm (0, (f (0, a)).2)).2) = (0, a) := by
      rw [← Algebra.prod_zero_one_mul, f.symm.map_mul, ← Hf, f.symm_apply_apply,
        Algebra.prod_zero_one_mul]
    simp_rw [Prod.ext_iff, true_and] at this
    exact this
  right_inv := λ a => by
    have : (0, (f (0, (f.symm (0, a)).2)).2) = (0, a) := by
      rw [← Algebra.prod_zero_one_mul, f.map_mul, hf, f.apply_symm_apply,
        Algebra.prod_zero_one_mul]
    simp_rw [Prod.ext_iff, true_and] at this
    exact this
  map_add' := λ a b => by prod_map_add
  map_mul' := λ a b => by prod_map_mul
  commutes' := λ r => by
    simp only
    simp_rw [Algebra.algebraMap_eq_smul_one]
    nth_rw 1 [← smul_zero r]
    rw [← Prod.smul_mk, f.map_smul, Prod.smul_snd, hf] }
def AlgEquiv.of_prod_map₁₂ {K R₁ R₂ R₃ R₄ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  [Algebra K R₁] [Algebra K R₂] [Algebra K R₃] [Algebra K R₄]
  (f : (R₁ × R₂) ≃ₐ[K] (R₃ × R₄))
  (hf : f (1, 0) = (0, 1)) :
  R₁ ≃ₐ[K] R₄ :=
{ toFun := λ x => (f (x, 0)).2
  invFun := λ x => (f.symm (0, x)).1
  left_inv := λ x => by
    have : ((f.symm (0, (f (x, 0)).2)).1, 0) = (x, 0) := by
      rw [← Algebra.prod_zero_one_mul, f.symm.map_mul, ← hf, f.symm_apply_apply,
        Algebra.prod_one_zero_mul, f.symm_apply_apply]
    simp_rw [Prod.ext_iff, and_true] at this
    exact this
  right_inv := λ x => by
    have : (0, (f ((f.symm (0, x)).1, 0)).2) = (0, x) := by
      rw [← Algebra.prod_one_zero_mul, f.map_mul, hf, f.apply_symm_apply, Algebra.prod_zero_one_mul]
    simp_rw [Prod.ext_iff, true_and] at this
    exact this
  map_add' := λ x y => by prod_map_add
  map_mul' := λ x y => by prod_map_mul
  commutes' := λ r => by
    simp only
    simp_rw [Algebra.algebraMap_eq_smul_one]
    nth_rw 1 [← smul_zero r]
    rw [← Prod.smul_mk, f.map_smul, Prod.smul_snd, hf] }
def AlgEquiv.of_prod_map₂₁ {K R₁ R₂ R₃ R₄ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  [Algebra K R₁] [Algebra K R₂] [Algebra K R₃] [Algebra K R₄]
  (f : (R₁ × R₂) ≃ₐ[K] (R₃ × R₄))
  (hf : f (0, 1) = (1, 0)) :
  R₂ ≃ₐ[K] R₃ :=
{ toFun := λ x => (f (0, x)).1
  invFun := λ x => (f.symm (x, 0)).2
  left_inv := λ x => by
    have : (0, (f.symm ((f (0, x)).1, 0)).2) = (0, x) := by
      rw [← Algebra.prod_one_zero_mul, f.symm.map_mul, ← hf, f.symm_apply_apply,
        Algebra.prod_zero_one_mul, f.symm_apply_apply]
    simp_rw [Prod.ext_iff, true_and] at this
    exact this
  right_inv := λ x => by
    have : ((f (0, (f.symm (x, 0)).2)).1, 0) = (x, 0) := by
      rw [← Algebra.prod_zero_one_mul, f.map_mul, hf, f.apply_symm_apply, Algebra.prod_one_zero_mul]
    simp_rw [Prod.ext_iff, and_true] at this
    exact this
  map_add' := λ x y => by prod_map_add
  map_mul' := λ x y => by prod_map_mul
  commutes' := λ r => by
    simp only
    simp_rw [Algebra.algebraMap_eq_smul_one]
    nth_rw 1 [← smul_zero r]
    rw [← Prod.smul_mk, f.map_smul, Prod.smul_fst, hf] }

theorem AlgEquiv.matrix_prod_aut' {𝕜 n m : Type*} [Field 𝕜] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  [Nonempty n] [Nonempty m]
  (f : (Matrix n n 𝕜 × Matrix m m 𝕜) ≃ₐ[𝕜] (Matrix n n 𝕜 × Matrix m m 𝕜)) :
  (∃ (f₁ : Matrix n n 𝕜 ≃ₐ[𝕜] Matrix n n 𝕜) (f₂ : Matrix m m 𝕜 ≃ₐ[𝕜] Matrix m m 𝕜),
    f = AlgEquiv.prod_map f₁ f₂)
  ∨
  (∃ (g : (Matrix m m 𝕜 × Matrix n n 𝕜) ≃ₐ[𝕜] (Matrix n n 𝕜 × Matrix m m 𝕜)),
    f = g ∘ Prod.swap) :=
by
  rcases AlgEquiv.matrix_prod_aut f with (h | h)
  . left
    let f₁ : Matrix n n 𝕜 ≃ₐ[𝕜] Matrix n n 𝕜 := AlgEquiv.of_prod_map₁₁ f h.1
    let f₂ : Matrix m m 𝕜 ≃ₐ[𝕜] Matrix m m 𝕜 := AlgEquiv.of_prod_map₂₂ f h.2
    use f₁, f₂
    ext1 x
    simp_rw [AlgEquiv.prod_map_apply, Prod_map]
    calc f x = f (x.1, 0) + f (0, x.2) := by rw [← map_add, Prod.fst_add_snd]
      _ = f ((1,0) * (x.1, 0)) + f ((0,1) * (0, x.2)) := by
        rw [Prod.mul_def]; simp only [one_mul, mul_zero, Prod.mk_mul_mk]
      _ = (1, 0) * f (x.1, 0) + (0, 1) * f (0, x.2) := by
        simp_rw [f.map_mul, h]
      _ = ((f (x.1, 0)).1, 0) + (0, (f (0, x.2)).2) := by
        simp_rw [Prod.mul_def, zero_mul, one_mul]
      _ = (f₁ x.1, 0) + (0, f₂ x.2) := rfl
      _ = (f₁ x.1, f₂ x.2) := by simp only [Prod.mk_add_mk, add_zero, zero_add]
  . right
    let g₁ : Matrix n n 𝕜 ≃ₐ[𝕜] Matrix m m 𝕜 := AlgEquiv.of_prod_map₁₂ f h.1
    let g₂ : Matrix m m 𝕜 ≃ₐ[𝕜] Matrix n n 𝕜 := AlgEquiv.of_prod_map₂₁ f h.2
    use (AlgEquiv.prod_map g₂ g₁)
    ext1 x
    simp_rw [Function.comp_apply, Prod.swap, AlgEquiv.prod_map_apply, Prod_map]
    calc f x = f (0, x.2) + f (x.1, 0) := by rw [← map_add, add_comm, Prod.fst_add_snd]
      _ = f ((0,1) * (0, x.2)) + f ((1,0) * (x.1, 0)) := by
        rw [Prod.mul_def]; simp only [one_mul, mul_zero, Prod.mk_mul_mk]
      _ = (1, 0) * f (0, x.2) + (0, 1) * f (x.1, 0) := by
        simp_rw [f.map_mul, h]
      _ = ((f (0, x.2)).1, 0) + (0, (f (x.1, 0)).2) := by
        simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mul_def, zero_mul, one_mul]
      _ = (g₂ x.2, 0) + (0, g₁ x.1) := rfl
      _ = (g₂ x.2, g₁ x.1) := by simp_rw [Prod.mk_add_mk, add_zero, zero_add]

lemma AlgEquiv.matrix_fintype_card_eq_of {𝕜 n m : Type*} [Field 𝕜] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  {f : (Matrix n n 𝕜 × Matrix m m 𝕜) ≃ₐ[𝕜] (Matrix n n 𝕜 × Matrix m m 𝕜)}
  (hf : f (0, 1) = (1, 0)) :
  Fintype.card n = Fintype.card m :=
by
  let f' := AlgEquiv.of_prod_map₂₁ f hf
  have := LinearEquiv.finrank_eq f'.toLinearEquiv
  simp [FiniteDimensional.finrank_matrix, ← pow_two] at this
  exact this.symm

end Matrix
