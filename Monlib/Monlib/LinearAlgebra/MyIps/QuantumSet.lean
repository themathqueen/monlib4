/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyIps.RankOne
import LinearAlgebra.MyIps.Functional
import LinearAlgebra.Nacgor

#align_import linear_algebra.my_ips.quantum_set

/-!

# Quantum Set

This file defines the structure of a quantum set.

A quantum set is defined as a star-algebra `A` over `ℂ` with a positive element `Q` such that
  `Q` is invertible and a sum of rank-one operators (in other words, positive definite).
The quantum set is also equipped with a faithful positive linear functional `φ` on `A`,
  which is used to define the inner product on `A`, i.e., `⟪x, y⟫_ℂ = φ (star x * y)`.
The quantum set is also equipped with a `trace` functional on `A` such that `φ x = trace (Q * x)`.

## Main definitions

* `quantum_set A` is a structure that defines a quantum set.
* `quantum_set.mod_aut A t` defines the modular automorphism of a quantum set, which is
  a family of automorphisms of `A` parameterized by `t : ℝ`, given by `x ↦ Q^(-t) * x * Q^t`,
  where `Q` is the unique positive definite element in `A` given by the quantum set structure.

-/


-- def star_ordered_ring.pos_add_submonoid (A : Type*) [semiring A]
--   [partial_order A] [star_ordered_ring A] : submonoid A :=
-- { carrier := { x | 0 < x },
--   add_mem' := λ x y hx hy,
--   by { simp only [set.mem_set_of_eq, add_nonneg hx hy], }
--    }
-- local attribute [instance] algebra.of_is_scalar_tower_smul_comm_class
class QuantumSet (A : Type _) where
  toNormedAddCommGroupOfRing : NormedAddCommGroupOfRing A
  toInnerProductSpace : InnerProductSpace ℂ A
  toPartialOrder : PartialOrder A
  toStarOrderedRing : StarOrderedRing A
  toHasSmul_comm_class : SMulCommClass ℂ A A
  to_isScalarTower : IsScalarTower ℂ A A
  to_finiteDimensional : FiniteDimensional ℂ A
  toHasInv : Inv A
  φ : Module.Dual ℂ A
  hφ : φ.IsFaithfulPosMap
  inner_eq : ∀ x y : A, ⟪x, y⟫_ℂ = φ (star x * y)
  functional_adjoint_eq :
    let _inst : Algebra ℂ A := Algebra.ofIsScalarTowerSmulCommClass
    LinearMap.adjoint φ = Algebra.linearMap ℂ A
  APos := { x : A // 0 < x }
  -- (A_pos_has_one : has_one A_pos)
  aPosHasPow : Pow A_pos ℝ
  aPosHasInv : Inv A_pos
  A_pos_pow_hMul :
    ∀ (x : A_pos) (t s : ℝ), ((x ^ t : A_pos) : A) * ((x ^ s : A_pos) : A) = ↑(x ^ (t + s))
  A_pos_pow_zero : ∀ x : A_pos, ↑(x ^ (0 : ℝ)) = (1 : A)
  A_pos_pow_one : ∀ x : A_pos, x ^ (1 : ℝ) = x
  A_pos_pow_neg : ∀ (x : A_pos) (t : ℝ), x ^ (-t : ℝ) = (x ^ t)⁻¹
  A_pos_inv_coe : ∀ x : A_pos, (x : A)⁻¹ = (x⁻¹ : A_pos)
  q : A_pos
  -- (Q_is_pos : ∃ x : A, (Q : A) = star x * x)
  -- (has_lt : has_lt A)
  -- (Q_is_pos_def : 0 < Q)
  trace : Module.Dual ℂ A
  traceIsTracial : trace.IsTracial
  functional_eq : ∀ x : A, φ x = trace (Q * x)

attribute [instance] QuantumSet.toNormedAddCommGroupOfRing

attribute [instance] QuantumSet.toInnerProductSpace

attribute [instance] QuantumSet.toPartialOrder

attribute [instance] QuantumSet.toStarOrderedRing

attribute [instance] QuantumSet.toHasSmul_comm_class

attribute [instance] QuantumSet.to_isScalarTower

attribute [instance] QuantumSet.to_finiteDimensional

attribute [instance] QuantumSet.toHasInv

attribute [instance] QuantumSet.aPosHasPow

attribute [instance] QuantumSet.aPosHasInv

namespace QuantumSet

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

@[simps]
def modAut (A : Type _) [QuantumSet A] (t : ℝ) : A ≃ₐ[ℂ] A :=
  let A_pos := { x : A // 0 < x }
  let Q : A_pos := QuantumSet.q
  { toFun := fun x => ↑(Q ^ (-t) : A_pos) * x * ↑(Q ^ t : A_pos)
    invFun := fun x => ↑(Q ^ t : A_pos) * x * ↑(Q ^ (-t) : A_pos)
    left_inv := fun x => by
      calc
        ↑(Q ^ t) * (↑(Q ^ (-t)) * x * ↑(Q ^ t)) * ↑(Q ^ (-t)) =
            ↑(Q ^ t) * ↑(Q ^ t)⁻¹ * x * (↑(Q ^ t) * ↑(Q ^ t)⁻¹) :=
          by simp_rw [mul_assoc, A_pos_pow_neg]
        _ = ↑(Q ^ (t + -t)) * x * ↑(Q ^ (t + -t)) := by rw [← A_pos_pow_neg, A_pos_pow_mul]
        _ = x := by simp_rw [add_neg_self, A_pos_pow_zero, one_mul, mul_one]
    right_inv := fun x => by
      calc
        ↑(Q ^ (-t)) * (↑(Q ^ t) * x * ↑(Q ^ (-t))) * ↑(Q ^ t) =
            ↑(Q ^ t)⁻¹ * ↑(Q ^ t) * x * (↑(Q ^ t)⁻¹ * ↑(Q ^ t)) :=
          by simp only [mul_assoc, A_pos_pow_neg]
        _ = ↑(Q ^ (-t + t)) * x * ↑(Q ^ (-t + t)) := by simp_rw [← A_pos_pow_neg, A_pos_pow_mul]
        _ = x := by simp_rw [neg_add_self, A_pos_pow_zero, one_mul, mul_one]
    map_mul' := fun x y => by
      calc
        ↑(Q ^ (-t) : A_pos) * (x * y) * ↑(Q ^ t : A_pos) =
            ↑(Q ^ (-t)) * x * (↑(Q ^ t) * ↑(Q ^ (-t))) * y * ↑(Q ^ t) :=
          by simp_rw [A_pos_pow_mul, add_neg_self, A_pos_pow_zero, mul_one, mul_assoc]
        _ = ↑(Q ^ (-t)) * x * ↑(Q ^ t) * (↑(Q ^ (-t)) * y * ↑(Q ^ t)) := by simp_rw [mul_assoc]
    map_add' := fun x y => by simp_rw [mul_add, add_mul]
    commutes' := fun r => by
      simp_rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc,
        A_pos_pow_mul, neg_add_self, A_pos_pow_zero] }

variable {A : Type _} [QuantumSet A]

theorem modAut_trans (t s : ℝ) : (modAut A t).trans (modAut A s) = modAut A (t + s) :=
  by
  ext x
  simp_rw [AlgEquiv.trans_apply, mod_aut_apply, mul_assoc, A_pos_pow_mul, ← mul_assoc,
    A_pos_pow_mul, neg_add, add_comm]

theorem modAut_neg (t : ℝ) : modAut A (-t) = (modAut A t).symm :=
  by
  ext1
  simp_rw [mod_aut_apply, mod_aut_symm_apply, neg_neg]

end QuantumSet

