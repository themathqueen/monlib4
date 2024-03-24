/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.InnerProductSpace.Basic

#align_import linear_algebra.nacgor

/-!
 # Normed additive commutative groups of rings

 This file contains the definition of `normed_add_comm_group_of_ring` which is a structure
  combining the ring structure, the norm, and the metric space structure.
-/


/-- `normed_add_comm_group` structure extended by `ring` -/
@[reducible]
class NormedAddCommGroupOfRing (B : Type _) extends Ring B, NormedAddCommGroup B

open scoped BigOperators

attribute [instance, reducible] NormedAddCommGroupOfRing.toNormedAddCommGroup
attribute [instance, reducible] NormedAddCommGroupOfRing.toRing
attribute [instance, reducible] NormedAddCommGroupOfRing.toNorm

@[reducible]
def Algebra.ofIsScalarTowerSmulCommClass {R A : Type _} [CommSemiring R] [Semiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

@[instance]
noncomputable def PiNormedAddCommGroupOfRing {ι : Type _} [Fintype ι] {B : ι → Type _}
    [Π i, NormedAddCommGroupOfRing (B i)] : NormedAddCommGroupOfRing (Π i, B i)
    where
  toNorm := PiLp.instNorm 2 B
  toRing := Pi.ring
  toMetricSpace := PiLp.instMetricSpacePiLp 2 B
  dist_eq x y := by
    have : 0 < (2 : ENNReal).toReal := by norm_num
    simp_rw [PiLp.norm_eq_sum this, PiLp.dist_eq_sum this, dist_eq_norm]
    rfl

example {ι : Type _} [Fintype ι] {E : ι → Type _} [∀ i, NormedAddCommGroupOfRing (E i)] :
    @AddCommGroup.toAddCommMonoid _
        (PiNormedAddCommGroupOfRing.toNormedAddCommGroup :
            NormedAddCommGroup (∀ i, E i)).toAddCommGroup =
      NonUnitalNonAssocSemiring.toAddCommMonoid :=
  rfl

theorem Pi.normedAddCommGroupOfRing.norm_eq_sum {ι : Type _} [Fintype ι] {B : ι → Type _}
  [Π i, NormedAddCommGroupOfRing (B i)] (x : Π i, B i) :
  PiNormedAddCommGroupOfRing.norm x = Real.sqrt (∑ i, ‖x i‖ ^ 2) :=
  by
  have : 0 < (2 : ENNReal).toReal := by norm_num
  simp_rw [PiLp.norm_eq_sum this, ENNReal.toReal_ofNat,
    Real.rpow_two, Real.sqrt_eq_rpow]

example {E : Type _} [NormedAddCommGroupOfRing E] :
    @Ring.toAddCommGroup E _ =
      NormedAddCommGroup.toAddCommGroup :=
  rfl

example {E : Type _} [NormedAddCommGroupOfRing E] :
    (@AddCommGroup.toAddCommMonoid E NormedAddCommGroup.toAddCommGroup : AddCommMonoid E) =
      (NonUnitalNonAssocSemiring.toAddCommMonoid : AddCommMonoid E) :=
  rfl

example {E : Type _} [Ring E] :
  @AddCommGroup.toAddCommMonoid E (@Ring.toAddCommGroup E _) =
    NonUnitalNonAssocSemiring.toAddCommMonoid :=
rfl

/-- `module` given by `algebra` is equal to that given by
  `inner_product_space`, but they are not definitionally equal. -/
example {E : Type _} [NormedAddCommGroupOfRing E] [h : InnerProductSpace ℂ E] [SMulCommClass ℂ E E]
    [IsScalarTower ℂ E E] : h.toModule = (Algebra.toModule : Module ℂ E) := by ext; rfl
