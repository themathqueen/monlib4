/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.LinearAlgebra.TensorProduct.BasicLemmas
import Mathlib.Algebra.Algebra.Bilinear
import Monlib.LinearAlgebra.End
import Mathlib.RingTheory.TensorProduct.Basic
import Monlib.Preq.Finset
import Monlib.LinearAlgebra.LmulRmul

/-!
 # (A-A)-Bimodules

  We define (A-A)-bimodules, where A is a commutative semiring, and show basic properties of them.
-/


variable {R H₁ H₂ : Type _} [CommSemiring R] [Semiring H₁] [Semiring H₂] [Algebra R H₁]
  [Algebra R H₂]

open scoped TensorProduct

local notation x " ⊗ₘ " y => TensorProduct.map x y

noncomputable def Bimodule.lsmul (x : H₁) (y : H₁ ⊗[R] H₂) : H₁ ⊗[R] H₂ :=
  (LinearMap.mulLeft R x ⊗ₘ 1) y

noncomputable def Bimodule.rsmul (x : H₁ ⊗[R] H₂) (y : H₂) : H₁ ⊗[R] H₂ :=
  (1 ⊗ₘ LinearMap.mulRight R y) x

scoped[Bimodule] infixl:72 " •ₗ " => Bimodule.lsmul

scoped[Bimodule] infixl:72 " •ᵣ " => Bimodule.rsmul

open scoped Bimodule BigOperators

theorem Bimodule.lsmul_apply (x a : H₁) (b : H₂) : x •ₗ a ⊗ₜ b = (x * a) ⊗ₜ[R] b :=
  rfl

theorem Bimodule.rsmul_apply (a : H₁) (x b : H₂) : a ⊗ₜ b •ᵣ x = a ⊗ₜ[R] (b * x) :=
  rfl

theorem Bimodule.lsmul_rsmul_assoc (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂) :
    x •ₗ a •ᵣ y = x •ₗ (a •ᵣ y) := by
  simp_rw [Bimodule.lsmul, Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.one_comp, LinearMap.comp_one]

theorem Bimodule.lsmul_zero (x : H₁) : x •ₗ (0 : H₁ ⊗[R] H₂) = 0 :=
  rfl

theorem Bimodule.zero_lsmul (x : H₁ ⊗[R] H₂) : 0 •ₗ x = 0 := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_zero_eq_zero, TensorProduct.zero_map, LinearMap.zero_apply]

theorem Bimodule.zero_rsmul (x : H₂) : (0 : H₁ ⊗[R] H₂) •ᵣ x = 0 :=
  rfl

theorem Bimodule.rsmul_zero (x : H₁ ⊗[R] H₂) : x •ᵣ 0 = 0 := by
  rw [Bimodule.rsmul, LinearMap.mulRight_zero_eq_zero, TensorProduct.map_zero, LinearMap.zero_apply]

theorem Bimodule.lsmul_add (x : H₁) (a b : H₁ ⊗[R] H₂) : x •ₗ (a + b) = x •ₗ a + x •ₗ b :=
  map_add _ _ _

theorem Bimodule.add_rsmul (x : H₂) (a b : H₁ ⊗[R] H₂) : (a + b) •ᵣ x = a •ᵣ x + b •ᵣ x :=
  map_add _ _ _

theorem Bimodule.lsmul_sum (x : H₁) {k : Type _} {s : Finset k} (a : k → H₁ ⊗[R] H₂) :
    x •ₗ ∑ i ∈ s, a i = ∑ i ∈ s, x •ₗ a i :=
  map_sum _ _ _

theorem Bimodule.sum_rsmul (x : H₂) {k : Type _} {s : Finset k} (a : k → H₁ ⊗[R] H₂) :
    (∑ i ∈ s, a i) •ᵣ x = ∑ i ∈ s, a i •ᵣ x :=
  map_sum _ _ _

theorem Bimodule.one_lsmul (x : H₁ ⊗[R] H₂) : 1 •ₗ x = x := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_one, ← Module.End.one_eq_id, TensorProduct.map_one,
    Module.End.one_apply]

theorem Bimodule.rsmul_one (x : H₁ ⊗[R] H₂) : x •ᵣ 1 = x := by
  rw [Bimodule.rsmul, LinearMap.mulRight_one, ← Module.End.one_eq_id, TensorProduct.map_one,
    Module.End.one_apply]

theorem Bimodule.lsmul_one (x : H₁) : x •ₗ (1 : H₁ ⊗[R] H₂) = x ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def, Bimodule.lsmul_apply, mul_one]

theorem Bimodule.one_rsmul (x : H₂) : (1 : H₁ ⊗[R] H₂) •ᵣ x = 1 ⊗ₜ x := by
  rw [Algebra.TensorProduct.one_def, Bimodule.rsmul_apply, one_mul]

theorem Bimodule.lsmul_smul (α : R) (x : H₁) (a : H₁ ⊗[R] H₂) : x •ₗ α • a = α • (x •ₗ a) := by
  simp_rw [Bimodule.lsmul, _root_.map_smul]

theorem Bimodule.smul_rsmul (α : R) (x : H₂) (a : H₁ ⊗[R] H₂) : α • a •ᵣ x = α • (a •ᵣ x) := by
  simp_rw [Bimodule.rsmul, _root_.map_smul]

theorem Bimodule.lsmul_lsmul (x y : H₁) (a : H₁ ⊗[R] H₂) : x •ₗ (y •ₗ a) = (x * y) •ₗ a := by
  simp_rw [Bimodule.lsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← LinearMap.mulLeft_mul]
  rfl

theorem Bimodule.rsmul_rsmul (x y : H₂) (a : H₁ ⊗[R] H₂) : a •ᵣ x •ᵣ y = a •ᵣ (x * y) := by
  simp_rw [Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← LinearMap.mulRight_mul]
  rfl

local notation "l(" x "," y ")" => y →ₗ[x] y

def LinearMap.IsBimoduleMap (P : l(R,H₁ ⊗[R] H₂)) : Prop :=
  ∀ (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂), P (x •ₗ a •ᵣ y) = x •ₗ P a •ᵣ y

theorem LinearMap.IsBimoduleMap.lsmul {P : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap) (x : H₁)
    (a : H₁ ⊗[R] H₂) : P (x •ₗ a) = x •ₗ P a :=
  by
  nth_rw 1 [← Bimodule.rsmul_one a]
  rw [← Bimodule.lsmul_rsmul_assoc, hP, Bimodule.rsmul_one]

theorem LinearMap.IsBimoduleMap.rsmul {P : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap) (x : H₂)
    (a : H₁ ⊗[R] H₂) : P (a •ᵣ x) = P a •ᵣ x :=
  by
  nth_rw 1 [← Bimodule.one_lsmul a]
  rw [hP, Bimodule.one_lsmul]

theorem LinearMap.IsBimoduleMap.add {P Q : l(R,H₁ ⊗[R] H₂)} (hP : P.IsBimoduleMap)
    (hQ : Q.IsBimoduleMap) : (P + Q).IsBimoduleMap :=
  by
  simp_rw [LinearMap.IsBimoduleMap, LinearMap.add_apply, Bimodule.lsmul_add, Bimodule.add_rsmul]
  intro x y a
  rw [hP, hQ]

theorem LinearMap.isBimoduleMap.zero : (0 : l(R,H₁ ⊗[R] H₂)).IsBimoduleMap :=
  by
  intro x y a
  simp_rw [LinearMap.zero_apply, Bimodule.lsmul_zero, Bimodule.zero_rsmul]

theorem LinearMap.IsBimoduleMap.smul {x : l(R,H₁ ⊗[R] H₂)} (hx : x.IsBimoduleMap) (k : R) :
    (k • x).IsBimoduleMap := by
  intro x y a
  simp only [LinearMap.smul_apply, Bimodule.lsmul_smul, Bimodule.smul_rsmul]
  rw [hx]

theorem LinearMap.IsBimoduleMap.nsmul {x : l(R,H₁ ⊗[R] H₂)} (hx : x.IsBimoduleMap) (k : ℕ) :
    (k • x).IsBimoduleMap := by
  intro x y a
  simp only [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul R k,
    Bimodule.lsmul_smul, Bimodule.smul_rsmul]
  rw [hx]

noncomputable def LinearMap.IsBimoduleMaps (R H₁ H₂ : Type _) [CommSemiring R]
  [Semiring H₁] [Semiring H₂] [Algebra R H₁] [Algebra R H₂] :
    Submodule R (l(R, H₁ ⊗[R] H₂)) where
  carrier x := x.IsBimoduleMap
  add_mem' x y := x.add y
  zero_mem' := LinearMap.isBimoduleMap.zero
  smul_mem' r _ x := x.smul r

-- { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }


-- noncomputable instance LinearMap.IsBidmoduleMaps.Add :
--   Add (LinearMap.IsBimoduleMaps R H₁ H₂) :=
-- ⟨fun x y => ⟨↑x + ↑y, x.property.add y.property⟩⟩
-- noncomputable instance LinearMap.IsBimoduleMaps.Zero :
--   Zero (LinearMap.IsBimoduleMaps R H₁ H₂) :=
-- ⟨⟨0, LinearMap.isBimoduleMap.zero⟩⟩
-- noncomputable instance LinearMap.IsBimoduleMaps.Smul :
--   SMul R (LinearMap.IsBimoduleMaps R H₁ H₂) :=
-- ⟨fun a x => ⟨a • ↑x, x.property.smul a⟩⟩
-- noncomputable instance LinearMap.IsBimoduleMaps.NSmul :
--   SMul ℕ (LinearMap.IsBimoduleMaps R H₁ H₂) :=
-- ⟨fun a x => ⟨a • ↑x, x.property.nsmul a⟩⟩

@[simp] lemma LinearMap.IsBimoduleMaps.coe_add (x y : IsBimoduleMaps R H₁ H₂) :
   ((x + y : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = ↑x + ↑y := rfl
@[simp] lemma LinearMap.IsBimoduleMaps.coe_smul (x : IsBimoduleMaps R H₁ H₂)
  (r : R) :
   ((r • x : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = r • ↑x := rfl
@[simp] lemma LinearMap.IsBimoduleMaps.coe_nsmul (x : IsBimoduleMaps R H₁ H₂)
  (r : ℕ) :
   ((r • x : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = r • ↑x := rfl
@[simp] lemma LinearMap.IsBimoduleMaps.coe_zero :
   ((0 : IsBimoduleMaps R H₁ H₂) : H₁ ⊗[R] H₂ →ₗ[R] H₁ ⊗[R] H₂) = 0 := rfl

-- @[instance]
-- noncomputable def LinearMap.IsBimoduleMaps.AddCommMonoid : AddCommMonoid (IsBimoduleMaps R H₁ H₂)
--     where
--   add_assoc x y z := by ext; simp only [coe_add, add_assoc]
--   zero_add x := by ext; simp only [coe_zero, coe_add, zero_add]
--   add_zero x := by ext; simp only [coe_zero, coe_add, add_zero]
--   nsmul n x := n • x
--   nsmul_zero x := by ext; simp only [coe_nsmul, coe_zero, zero_smul]
--   nsmul_succ k x :=
--     by
--     ext
--     simp only [coe_add, coe_nsmul, add_smul, one_mul, add_comm,
--       nsmul_eq_mul, Nat.cast_one]
--   add_comm x y := by
--     rw [← Subtype.coe_inj]
--     simp_rw [coe_add, add_comm]

theorem LinearMap.IsBimoduleMap.add_smul (a b : R) (x : (IsBimoduleMaps R H₁ H₂)) :
    (a + b) • x = a • x + b • x := by
  rw [← Subtype.coe_inj]
  simp_rw [IsBimoduleMaps.coe_smul, IsBimoduleMaps.coe_add, _root_.add_smul]
  rfl

-- open LinearMap.IsBimoduleMaps in
-- noncomputable instance : MulAction R (LinearMap.IsBimoduleMaps R H₁ H₂)
--     where
--   one_smul x := by
--     simp_rw [← Subtype.coe_inj]
--     simp_rw [coe_smul, one_smul]
--   mul_smul x y a := by
--     simp_rw [← Subtype.coe_inj]
--     simp_rw [coe_smul, ← smul_smul]

-- open LinearMap.IsBimoduleMaps in
-- noncomputable instance : DistribMulAction R (LinearMap.IsBimoduleMaps R H₁ H₂)
--     where
--   smul_zero x := rfl
--   smul_add x y z := by
--     simp only [← Subtype.coe_inj, coe_smul, coe_add, smul_add]

-- noncomputable instance LinearMap.IsBimoduleMaps.Module :
--   Module R (IsBimoduleMaps R H₁ H₂)
--     where
--   add_smul r s x := IsBimoduleMap.add_smul _ _ _
--   zero_smul x := by
--     simp_rw [← Subtype.coe_inj, coe_smul, zero_smul, coe_zero]

-- @[reducible]
-- def LinearMap.IsBimoduleMaps.submodule :
--   Submodule R (IsBimoduleMaps R H₁ H₂)
--     where
--   carrier x := x.IsBimoduleMap
--   add_mem' x y hx hy := hx.add hy
--   zero_mem' := LinearMap.isBimoduleMapZero
--   smul_mem' r x hx := hx.smul r

theorem LinearMap.isBimoduleMap_iff {T : l(R,H₁ ⊗[R] H₂)} :
    T.IsBimoduleMap ↔ ∀ a b x y, T ((a * x) ⊗ₜ[R] (y * b)) = a •ₗ T (x ⊗ₜ[R] y) •ᵣ b :=
⟨fun h a b x y => by rw [← h]; rfl, fun h a b x =>
  x.induction_on
    (by simp only [map_zero, Bimodule.lsmul_zero, Bimodule.zero_rsmul])
    (fun _ _ => h _ _ _ _)
    (fun _ _ hc hd => by simp only [map_add, Bimodule.lsmul_add, Bimodule.add_rsmul, hc, hd])⟩

theorem LinearMap.isBimoduleMap_iff_ltensor_lsmul_rtensor_rsmul {R H₁ H₂ : Type _} [Field R] [Ring H₁]
    [Ring H₂] [Algebra R H₁] [Algebra R H₂] {x : l(R,H₁)} {y : l(R,H₂)} :
    (x ⊗ₘ y).IsBimoduleMap ↔
      (x ⊗ₘ y) = 0 ∨ x = LinearMap.mulRight R (x 1) ∧ y = LinearMap.mulLeft R (y 1) :=
  by
  rw [← left_module_map_iff, ← right_module_map_iff]
  by_cases h : (x ⊗ₘ y) = 0
  · simp_rw [h, true_or, iff_true, LinearMap.isBimoduleMap.zero]
  simp_rw [isBimoduleMap_iff, TensorProduct.map_tmul, Bimodule.lsmul_apply, Bimodule.rsmul_apply, h,
    false_or]
  have hy : y ≠ 0 := by
    intro hy
    rw [hy, TensorProduct.map_zero] at h
    contradiction
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, TensorProduct.zero_map] at h
    contradiction
  simp_rw [ne_eq, LinearMap.ext_iff, LinearMap.zero_apply, Classical.not_forall] at hx hy
  refine' ⟨fun hxy => _, fun hxy a b c d => by rw [hxy.1, hxy.2]⟩
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have H : ∀ x_4 x_2 x_1 x_3, x (x_1 * x_3) ⊗ₜ y (x_4 * x_2) = (x_1 * x x_3) ⊗ₜ (y x_4 * x_2) :=
    fun x_4 x_2 x_1 x_3 => hxy x_1 x_2 x_3 x_4
  rw [Forall.rotate] at hxy
  specialize hxy a 1
  specialize H b 1
  simp_rw [mul_one, one_mul, ← @sub_eq_zero _ _ _ (_ ⊗ₜ[R] (_ * _) : H₁ ⊗[R] H₂), ←
    @sub_eq_zero _ _ _ ((_ * _) ⊗ₜ[R] _), ← TensorProduct.sub_tmul, ← TensorProduct.tmul_sub,
    TensorProduct.tmul_eq_zero, sub_eq_zero, ha, hb, false_or, or_false] at H hxy
  exact ⟨H, fun _ _ => hxy _ _⟩

-- noncomputable def LinearMap.IsBimoduleMap.sum {p : Type _} {s : Finset p}
--   (x : p → (IsBimoduleMaps R H₁ H₂)) :
--   (IsBimoduleMaps R H₁ H₂) :=
-- ⟨∑ i in s, (x i).1, fun a b c =>
--   by
--   simp_rw [LinearMap.sum_apply, Bimodule.lsmul_sum, Bimodule.sum_rsmul]
--   apply Finset.sum_congr rfl; intros
--   rw [Subtype.mem (x _)]⟩

theorem LinearMap.IsBimoduleMap.sum_coe {p : Type _} {s : Finset p}
  (x : p → (IsBimoduleMaps R H₁ H₂)) :
  (∑ i ∈ s, x i : IsBimoduleMaps R H₁ H₂).1 = ∑ i ∈ s, (x i).1 :=
Submodule.coe_sum _ _ _

theorem rmulMapLmul_apply_apply (x : H₁ ⊗[R] H₂) (a : H₁) (b : H₂) :
    rmulMapLmul x (a ⊗ₜ b) = a •ₗ x •ᵣ b :=
x.induction_on (by simp only [map_zero]; rfl)
  (fun α β => by
    simp_rw [rmulMapLmul_apply, TensorProduct.map_tmul, rmul_apply, lmul_apply]
    rfl)
  (fun α β hα hβ => by
    simp_rw [map_add, LinearMap.add_apply]
    rw [hα, hβ, Bimodule.lsmul_add, Bimodule.add_rsmul])

theorem LinearMap.isBimoduleMap_iff' {f : l(R,H₁ ⊗[R] H₂)} :
    f.IsBimoduleMap ↔ rmulMapLmul (f 1) = f :=
  by
  simp_rw [TensorProduct.ext_iff', rmulMapLmul_apply_apply]
  refine' ⟨fun h x y => by rw [← h, Bimodule.lsmul_one, Bimodule.rsmul_apply, one_mul], fun h => _⟩
  rw [isBimoduleMap_iff]
  intro a b c d
  rw [← h, ← Bimodule.lsmul_lsmul, ← Bimodule.rsmul_rsmul, Bimodule.lsmul_rsmul_assoc, h]

@[simp]
theorem rmulMapLmul_apply_one (x : H₁ ⊗[R] H₂) :
  rmulMapLmul x 1 = x := by
calc rmulMapLmul x 1 =  rmulMapLmul x (1 ⊗ₜ[R] 1) := rfl
  _ = 1 •ₗ x •ᵣ 1 := by rw [rmulMapLmul_apply_apply]
  _ = x := by simp_rw [Bimodule.one_lsmul, Bimodule.rsmul_one]

@[simp]
theorem LinearMap.mem_isBimoduleMaps_iff {x : l(R, H₁ ⊗[R] H₂)} :
  x ∈ LinearMap.IsBimoduleMaps R H₁ H₂ ↔ x.IsBimoduleMap :=
by rfl

theorem rmulMapLmul_mem_isBimoduleMaps (x : H₁ ⊗[R] H₂) :
  rmulMapLmul x ∈ LinearMap.IsBimoduleMaps R H₁ H₂ :=
by
  simp_rw [LinearMap.mem_isBimoduleMaps_iff, LinearMap.isBimoduleMap_iff',
    rmulMapLmul_apply_one]

@[simps]
noncomputable def TensorProduct.toIsBimoduleMap
  {R : Type*} {H₁ H₂ : Type*} [CommSemiring R] [Semiring H₁]
  [Semiring H₂] [Algebra R H₁] [Algebra R H₂] :
    (H₁ ⊗[R] H₂) ≃ₗ[R] LinearMap.IsBimoduleMaps R H₁ H₂ where
  toFun x := ⟨rmulMapLmul x, rmulMapLmul_mem_isBimoduleMaps _⟩
  invFun x := (x : l(R, H₁ ⊗[R] H₂)) 1
  map_add' _ _ := by simp only [_root_.map_add]; rfl
  map_smul' _ _ := by simp only [map_smulₛₗ]; rfl
  left_inv _ := by simp only [rmulMapLmul_apply_one]
  right_inv f := by
    simp only
    congr
    rw [LinearMap.isBimoduleMap_iff'.mp f.property]
