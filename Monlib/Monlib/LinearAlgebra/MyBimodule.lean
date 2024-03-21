/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyTensorProduct
import Algebra.Algebra.Bilinear
import LinearAlgebra.End
import RingTheory.TensorProduct
import Preq.Finset
import LinearAlgebra.LmulRmul

#align_import linear_algebra.my_bimodule

/-!
 # (A-A)-Bimodules

  We define (A-A)-bimodules, where A is a commutative semiring, and show basic properties of them.
-/


variable {R H₁ H₂ : Type _} [CommSemiring R] [Semiring H₁] [Semiring H₂] [Algebra R H₁]
  [Algebra R H₂]

open scoped TensorProduct

local notation x " ⊗ₘ " y => TensorProduct.map x y

def Bimodule.lsmul (x : H₁) (y : H₁ ⊗[R] H₂) : H₁ ⊗[R] H₂ :=
  (LinearMap.mulLeft R x ⊗ₘ 1) y

def Bimodule.rsmul (x : H₁ ⊗[R] H₂) (y : H₂) : H₁ ⊗[R] H₂ :=
  (1 ⊗ₘ LinearMap.mulRight R y) x

scoped[Bimodule] infixl:72 " •ₗ " => Bimodule.lsmul

scoped[Bimodule] infixl:72 " •ᵣ " => Bimodule.rsmul

-- open bimodule
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

theorem Bimodule.lsmul_sum (x : H₁) {k : Type _} [Fintype k] (a : k → H₁ ⊗[R] H₂) :
    x •ₗ ∑ i, a i = ∑ i, x •ₗ a i :=
  map_sum _ _ _

theorem Bimodule.sum_rsmul (x : H₂) {k : Type _} [Fintype k] (a : k → H₁ ⊗[R] H₂) :
    (∑ i, a i) •ᵣ x = ∑ i, a i •ᵣ x :=
  map_sum _ _ _

theorem Bimodule.one_lsmul (x : H₁ ⊗[R] H₂) : 1 •ₗ x = x := by
  rw [Bimodule.lsmul, LinearMap.mulLeft_one, ← LinearMap.one_eq_id, TensorProduct.map_one,
    LinearMap.one_apply]

theorem Bimodule.rsmul_one (x : H₁ ⊗[R] H₂) : x •ᵣ 1 = x := by
  rw [Bimodule.rsmul, LinearMap.mulRight_one, ← LinearMap.one_eq_id, TensorProduct.map_one,
    LinearMap.one_apply]

theorem Bimodule.lsmul_one (x : H₁) : x •ₗ (1 : H₁ ⊗[R] H₂) = x ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def, Bimodule.lsmul_apply, mul_one]

theorem Bimodule.one_rsmul (x : H₂) : (1 : H₁ ⊗[R] H₂) •ᵣ x = 1 ⊗ₜ x := by
  rw [Algebra.TensorProduct.one_def, Bimodule.rsmul_apply, one_mul]

theorem Bimodule.lsmul_smul (α : R) (x : H₁) (a : H₁ ⊗[R] H₂) : x •ₗ α • a = α • (x •ₗ a) := by
  simp_rw [Bimodule.lsmul, SMulHomClass.map_smul]

theorem Bimodule.smul_rsmul (α : R) (x : H₂) (a : H₁ ⊗[R] H₂) : α • a •ᵣ x = α • (a •ᵣ x) := by
  simp_rw [Bimodule.rsmul, SMulHomClass.map_smul]

theorem Bimodule.lsmul_lsmul (x y : H₁) (a : H₁ ⊗[R] H₂) : x •ₗ (y •ₗ a) = (x * y) •ₗ a := by
  simp_rw [Bimodule.lsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp, ←
      LinearMap.mulLeft_mul] <;>
    rfl

theorem Bimodule.rsmul_rsmul (x y : H₂) (a : H₁ ⊗[R] H₂) : a •ᵣ x •ᵣ y = a •ᵣ (x * y) := by
  simp_rw [Bimodule.rsmul, ← LinearMap.comp_apply, ← TensorProduct.map_comp, ←
      LinearMap.mulRight_mul] <;>
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

theorem LinearMap.isBimoduleMapZero : (0 : l(R,H₁ ⊗[R] H₂)).IsBimoduleMap :=
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
  simp only [LinearMap.smul_apply, nsmul_eq_smul_cast R k, Bimodule.lsmul_smul, Bimodule.smul_rsmul]
  rw [hx]

@[instance]
def IsBimoduleMap.addCommMonoid : AddCommMonoid { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }
    where
  add x y := ⟨↑x + ↑y, LinearMap.IsBimoduleMap.add (Subtype.mem x) (Subtype.mem y)⟩
  add_assoc x y z := by simp only [Subtype.coe_mk, add_assoc]
  zero := ⟨0, LinearMap.isBimoduleMapZero⟩
  zero_add x := by simp only [Subtype.coe_mk, zero_add, Subtype.coe_eta]
  add_zero x := by simp only [Subtype.coe_mk, add_zero, Subtype.coe_eta]
  nsmul k x := ⟨k • ↑x, LinearMap.IsBimoduleMap.nsmul (Subtype.mem x) k⟩
  nsmul_zero x := by simp only [Subtype.coe_mk, zero_smul]; rfl
  nsmul_succ k x :=
    by
    simp only [nsmul_eq_mul, Nat.cast_succ, add_mul, one_mul, add_comm]
    rfl
  add_comm x y := by
    rw [← Subtype.coe_inj]
    unfold_coes
    simp_rw [Subtype.val, add_comm]

@[instance]
def IsBimoduleMap.hasSmul : SMul R { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }
    where smul a x := ⟨a • ↑x, LinearMap.IsBimoduleMap.smul (Subtype.mem x) a⟩

theorem IsBimoduleMap.add_smul (a b : R) (x : { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }) :
    (a + b) • x = a • x + b • x := by
  rw [← Subtype.coe_inj]
  unfold_coes
  simp_rw [Subtype.val, add_smul]
  rfl

instance : MulAction R { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }
    where
  one_smul x := by
    simp_rw [← Subtype.coe_inj]
    unfold_coes
    simp_rw [Subtype.val, one_smul]
    rfl
  hMul_smul x y a := by
    simp_rw [← Subtype.coe_inj]
    unfold_coes
    simp_rw [Subtype.val, ← smul_smul]
    rfl

instance : DistribMulAction R { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }
    where
  smul_zero x := rfl
  smul_add x y z := by
    simp_rw [← Subtype.coe_inj]
    unfold_coes
    simp_rw [Subtype.val]
    unfold_coes
    simp_rw [Subtype.val, ← smul_add]

instance IsBimoduleMap.module : Module R { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }
    where
  add_smul r s x := by
    simp_rw [← Subtype.coe_inj]
    unfold_coes
    simp_rw [Subtype.val, add_smul]
    rfl
  zero_smul x := by
    simp_rw [← Subtype.coe_inj]
    unfold_coes
    simp_rw [Subtype.val, zero_smul]

def IsBimoduleMap.submodule : Submodule R l(R,H₁ ⊗[R] H₂)
    where
  carrier x := x.IsBimoduleMap
  add_mem' x y hx hy := hx.add hy
  zero_mem' := LinearMap.isBimoduleMapZero
  smul_mem' r x hx := hx.smul r

theorem isBimoduleMap_iff {T : l(R,H₁ ⊗[R] H₂)} :
    T.IsBimoduleMap ↔ ∀ a b x y, T ((a * x) ⊗ₜ[R] (y * b)) = a •ₗ T (x ⊗ₜ[R] y) •ᵣ b :=
  by
  refine' ⟨fun h a b x y => by rw [← h] <;> rfl, fun h a b x => _⟩
  apply x.induction_on
  · simp only [map_zero, Bimodule.lsmul_zero, Bimodule.zero_rsmul]
  · intro c d
    exact h _ _ _ _
  · intro c d hc hd
    simp only [map_add, Bimodule.lsmul_add, Bimodule.add_rsmul, hc, hd]

theorem isBimoduleMap_iff_ltensor_lsmul_rtensor_rsmul {R H₁ H₂ : Type _} [Field R] [Ring H₁]
    [Ring H₂] [Algebra R H₁] [Algebra R H₂] {x : l(R,H₁)} {y : l(R,H₂)} :
    (x ⊗ₘ y).IsBimoduleMap ↔
      (x ⊗ₘ y) = 0 ∨ x = LinearMap.mulRight R (x 1) ∧ y = LinearMap.mulLeft R (y 1) :=
  by
  rw [← left_module_map_iff, ← right_module_map_iff]
  by_cases h : (x ⊗ₘ y) = 0
  · simp_rw [h, eq_self_iff_true, true_or_iff, iff_true_iff, LinearMap.isBimoduleMapZero]
  simp_rw [isBimoduleMap_iff, TensorProduct.map_tmul, Bimodule.lsmul_apply, Bimodule.rsmul_apply, h,
    false_or_iff]
  have hy : y ≠ 0 := by
    intro hy
    rw [hy, TensorProduct.map_zero] at h
    contradiction
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, TensorProduct.zero_map] at h
    contradiction
  simp_rw [Ne.def, LinearMap.ext_iff, LinearMap.zero_apply, Classical.not_forall] at hx hy
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
    TensorProduct.tmul_eq_zero, sub_eq_zero, ha, hb, false_or_iff, or_false_iff] at H hxy
  exact ⟨H, fun _ _ => hxy _ _⟩

def IsBimoduleMap.sum {p : Type _} [Fintype p]
    (x : p → { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap }) :
    { x : l(R,H₁ ⊗[R] H₂) // x.IsBimoduleMap } :=
  ⟨∑ i, x i, fun a b c =>
    by
    simp_rw [LinearMap.sum_apply, Bimodule.lsmul_sum, Bimodule.sum_rsmul]
    apply Finset.sum_congr rfl; intros
    rw [Subtype.mem (x _)]⟩

theorem rmulMapLmul_apply_apply (x : H₁ ⊗[R] H₂) (a : H₁) (b : H₂) :
    rmulMapLmul x (a ⊗ₜ b) = a •ₗ x •ᵣ b :=
  by
  apply x.induction_on
  · simp only [map_zero]; rfl
  · intro α β
    simp_rw [rmulMapLmul_apply, TensorProduct.map_tmul, rmul_apply, lmul_apply]
    rfl
  · intro α β hα hβ
    simp_rw [map_add, LinearMap.add_apply]
    rw [hα, hβ, Bimodule.lsmul_add, Bimodule.add_rsmul]

theorem LinearMap.isBimoduleMap_iff' {f : l(R,H₁ ⊗[R] H₂)} :
    f.IsBimoduleMap ↔ rmulMapLmul (f 1) = f :=
  by
  simp_rw [TensorProduct.ext_iff, rmulMapLmul_apply_apply]
  refine' ⟨fun h x y => by rw [← h, Bimodule.lsmul_one, Bimodule.rsmul_apply, one_mul], fun h => _⟩
  rw [isBimoduleMap_iff]
  intro a b c d
  rw [← h, ← Bimodule.lsmul_lsmul, ← Bimodule.rsmul_rsmul, Bimodule.lsmul_rsmul_assoc, h]

