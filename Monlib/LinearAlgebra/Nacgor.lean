/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Analysis.Normed.Group.Basic
import Analysis.NormedSpace.PiLp
import Analysis.InnerProductSpace.Basic

#align_import linear_algebra.nacgor

/-!
 # Normed additive commutative groups of rings

 This file contains the definition of `normed_add_comm_group_of_ring` which is a structure
  combining the ring structure, the norm, and the metric space structure.
-/


/-- `normed_add_comm_group` structure extended by `ring` -/
@[class]
structure NormedAddCommGroupOfRing (B : Type _) extends Norm B, Ring B, MetricSpace B where
  dist := fun x y => ‖x - y‖
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by obviously

open scoped BigOperators

def NormedAddCommGroupOfRing.toNormedAddCommGroup {B : Type _} [h : NormedAddCommGroupOfRing B] :
    NormedAddCommGroup B where dist_eq := NormedAddCommGroupOfRing.dist_eq

attribute [instance] NormedAddCommGroupOfRing.toNormedAddCommGroup

attribute [instance] NormedAddCommGroupOfRing.toRing

def Algebra.ofIsScalarTowerSmulCommClass {R A : Type _} [CommSemiring R] [Semiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

noncomputable instance Pi.normedAddCommGroupOfRing {ι : Type _} [Fintype ι] {B : ι → Type _}
    [∀ i, NormedAddCommGroupOfRing (B i)] : NormedAddCommGroupOfRing (∀ i, B i)
    where
  toHasNorm := PiLp.instNorm 2 B
  toRing := Pi.ring
  toMetricSpace := PiLp.metricSpace 2 B
  dist_eq x y := by
    have : 0 < (2 : ENNReal).toReal := by norm_num
    simp_rw [PiLp.norm_eq_sum this, PiLp.dist_eq_sum this, dist_eq_norm]
    rfl

example {ι : Type _} [Fintype ι] {E : ι → Type _} [h : ∀ i, NormedAddCommGroupOfRing (E i)] :
    @AddCommGroup.toAddCommMonoid _
        (NormedAddCommGroupOfRing.toNormedAddCommGroup :
            NormedAddCommGroup (∀ i, E i)).toAddCommGroup =
      NonUnitalNonAssocSemiring.toAddCommMonoid _ :=
  rfl

-- set_option old_structure_cmd true
theorem Pi.normedAddCommGroupOfRing.norm_eq_sum {ι : Type _} [Fintype ι] {B : ι → Type _}
    [∀ i, NormedAddCommGroupOfRing (B i)] (x : ∀ i, B i) : ‖x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2) :=
  by
  have : 0 < (2 : ENNReal).toReal := by norm_num
  simp_rw [PiLp.norm_eq_sum this, ENNReal.toReal_bit0, ENNReal.one_toReal, Real.rpow_two,
    Real.sqrt_eq_rpow]

example {E : Type _} [h : NormedAddCommGroupOfRing E] :
    @AddCommGroupWithOne.toAddCommGroup E (Ring.toAddCommGroupWithOne E) =
      NormedAddCommGroup.toAddCommGroup :=
  rfl

example {E : Type _} [h : NormedAddCommGroupOfRing E] :
    (@AddCommGroup.toAddCommMonoid E NormedAddCommGroup.toAddCommGroup : AddCommMonoid E) =
      (NonUnitalNonAssocSemiring.toAddCommMonoid E : AddCommMonoid E) :=
  rfl

example {E : Type _} [Ring E] :
    @AddCommGroup.toAddCommMonoid E
        (@AddCommGroupWithOne.toAddCommGroup E (Ring.toAddCommGroupWithOne E)) =
      NonUnitalNonAssocSemiring.toAddCommMonoid E :=
  rfl

/-- `module` given by `algebra` is equal to that given by
  `inner_product_space`, but they are not definitionally equal.
  So this may cause some problems in the future.
  In Lean 4, they are definitionally equal. -/
example {E : Type _} [NormedAddCommGroupOfRing E] [h : InnerProductSpace ℂ E] [SMulCommClass ℂ E E]
    [IsScalarTower ℂ E E] : h.toModule = (Algebra.toModule : Module ℂ E) := by ext <;> rfl

