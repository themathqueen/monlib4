/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Logic.Basic
import Algebra.Group.Defs
import GroupTheory.GroupAction.Defs
import Algebra.Star.Basic
import LinearAlgebra.TensorProduct

#align_import preq.dite

/-!
 # Some stuff on dites
-/


theorem dite_add_dite {α : Type _} [Add α] (P : Prop) [Decidable P] (a b : P → α) (c d : ¬P → α) :
    ((dite P (fun x => a x) fun x => c x) + dite P (fun x => b x) fun x => d x) =
      dite P (fun x => a x + b x) fun x => c x + d x :=
  by
  rw [eq_comm]
  simp only [dite_eq_iff']
  constructor
  · intro h
    simp only [h, dif_pos]
  · intro h
    simp only [h, dif_neg, not_false_iff]

#print smul_dite /-
theorem smul_dite {α : Type _} (P : Prop) [Decidable P] (a : P → α) (c : ¬P → α) {β : Type _}
    (r : β) [SMul β α] :
    (r • dite P (fun x => a x) fun x => c x) = dite P (fun x => r • a x) fun x => r • c x :=
  by
  rw [eq_comm]
  simp only [dite_eq_iff']
  constructor
  · intro h
    simp only [h, dif_pos]
  · intro h
    simp only [h, dif_neg, not_false_iff]
-/

theorem hMul_dite {α : Type _} [Mul α] (P : Prop) [Decidable P] (a : α) (b : P → α) (c : ¬P → α) :
    (a * dite P (fun x => b x) fun x => c x) = dite P (fun x => a * b x) fun x => a * c x :=
  by
  rw [eq_comm]
  simp only [dite_eq_iff']
  constructor
  · intro h
    simp only [h, dif_pos]
  · intro h
    simp only [h, dif_neg, not_false_iff]

theorem dite_hMul {α : Type _} [Mul α] (P : Prop) [Decidable P] (a : α) (b : P → α) (c : ¬P → α) :
    (dite P (fun x => b x) fun x => c x) * a = dite P (fun x => b x * a) fun x => c x * a :=
  by
  rw [eq_comm]
  simp only [dite_eq_iff']
  constructor
  · intro h
    simp only [h, dif_pos]
  · intro h
    simp only [h, dif_neg, not_false_iff]

theorem dite_boole_add {α : Type _} [AddZeroClass α] (P : Prop) [Decidable P] (a b : P → α) :
    (dite P (fun x => a x + b x) fun x => 0) =
      (dite P (fun x => a x) fun x => 0) + dite P (fun x => b x) fun x => 0 :=
  by rw [dite_add_dite, add_zero]

theorem dite_boole_smul {α β : Type _} [Zero α] [SMulZeroClass β α] (P : Prop) [Decidable P]
    (a : P → α) (r : β) :
    (dite P (fun x => r • a x) fun x => 0) = r • dite P (fun x => a x) fun x => 0 := by
  rw [smul_dite, smul_zero]

theorem star_dite (P : Prop) [Decidable P] {α : Type _} [InvolutiveStar α] (a : P → α)
    (b : ¬P → α) :
    star (dite P (fun i => a i) fun i => b i) = dite P (fun i => star (a i)) fun i => star (b i) :=
  by
  rw [eq_comm, dite_eq_iff']
  constructor
  · intro h
    simp only [h, dif_pos]
  · intro h
    simp only [h, dif_neg, not_false_iff]

theorem dite_tmul {R N₁ N₂ : Type _} [CommSemiring R] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₁] [Module R N₂] (P : Prop) [Decidable P] (x₁ : P → N₁) (x₂ : N₂) :
    (dite P (fun h => x₁ h) fun h => 0) ⊗ₜ[R] x₂ = dite P (fun h => x₁ h ⊗ₜ[R] x₂) fun h => 0 := by
  split_ifs <;> simp

theorem tmul_dite {R N₁ N₂ : Type _} [CommSemiring R] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₁] [Module R N₂] (P : Prop) [Decidable P] (x₁ : N₁) (x₂ : P → N₂) :
    (x₁ ⊗ₜ[R] dite P (fun h => x₂ h) fun h => 0) = dite P (fun h => x₁ ⊗ₜ[R] x₂ h) fun h => 0 := by
  split_ifs <;> simp

theorem LinearMap.apply_dite {R H₁ H₂ : Type _} [Semiring R] [AddCommMonoid H₁] [AddCommMonoid H₂]
    [Module R H₁] [Module R H₂] (f : H₁ →ₗ[R] H₂) (P : Prop) [Decidable P] (a : P → H₁)
    (b : ¬P → H₁) :
    f (dite P (fun h => a h) fun h => b h) = dite P (fun h => f (a h)) fun h => f (b h) := by
  split_ifs <;> simp

