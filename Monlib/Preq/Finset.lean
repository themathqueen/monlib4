/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/-!

# finset

In this file we provide some elementary results for summations

-/


namespace Finset

open scoped BigOperators

theorem sum_rotate {α β γ ζ : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ} {u : Finset ζ}
    {f : α → γ → ζ → β} :
    ∑ x : α in s, ∑ y : γ in t, ∑ z : ζ in u, f x y z =
      ∑ z : ζ in u, ∑ x : α in s, ∑ y : γ in t, f x y z :=
  by
  nth_rw 2 [Finset.sum_comm]
  congr
  ext x
  rw [Finset.sum_comm]

theorem sum_3_comm {α β γ ζ : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ} {u : Finset ζ}
    {f : α → γ → ζ → β} :
    ∑ x : α in s, ∑ y : γ in t, ∑ z : ζ in u, f x y z =
      ∑ z : ζ in u, ∑ y : γ in t, ∑ x : α in s, f x y z :=
  by
  rw [Finset.sum_rotate]
  congr
  ext
  rw [Finset.sum_comm]

theorem sum_4_rotate {α β γ ζ ε : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ}
    {u : Finset ζ} {v : Finset ε} {f : α → γ → ζ → ε → β} :
    ∑ x : α in s, ∑ y : γ in t, ∑ z : ζ in u, ∑ w : ε in v, f x y z w =
      ∑ w : ε in v, ∑ x : α in s, ∑ y : γ in t, ∑ z : ζ in u, f x y z w :=
  by
  nth_rw 2 [Finset.sum_comm]
  congr
  ext x
  rw [Finset.sum_rotate]

theorem sum_sum_comm_sum {α β γ ζ ε : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ}
    {u : Finset ζ} {v : Finset ε} {f : α → γ → ζ → ε → β} :
    ∑ x : α in s, ∑ y : γ in t, ∑ z : ζ in u, ∑ w : ε in v, f x y z w =
      ∑ x : α in s, ∑ y : γ in t, ∑ w : ε in v, ∑ z : ζ in u, f x y z w :=
  by
  congr
  ext x
  congr
  ext y
  nth_rw 2 [Finset.sum_comm]

theorem sum_sum_sum {β α γ ζ : Type _} [AddCommMonoid β] {s : Finset γ} {t : Finset α}
    {g : Finset ζ} {f : γ → α → ζ → β} :
    ∑ x : γ in s, ∑ y : α in t, ∑ z : ζ in g, f x y z =
      ∑ z : ζ in g, ∑ x : γ in s, ∑ y : α in t, f x y z :=
  by
  symm
  rw [Finset.sum_comm]
  congr
  ext
  rw [Finset.sum_comm]

theorem sum_4_swap_2 {β α γ ζ ε : Type _} [AddCommMonoid β] {s : Finset γ} {t : Finset α}
    {u : Finset ζ} {v : Finset ε} {f : γ → α → ζ → ε → β} :
    ∑ x : γ in s, ∑ y : α in t, ∑ z : ζ in u, ∑ w : ε in v, f x y z w =
      ∑ z : ζ in u, ∑ w : ε in v, ∑ x : γ in s, ∑ y : α in t, f x y z w :=
  by
  rw [Finset.sum_rotate]
  congr
  ext
  rw [sum_rotate]

theorem sum_5_rotate {α β γ ζ ε κ : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ}
    {u : Finset ζ} {v : Finset ε} {k : Finset κ} {f : α → γ → ζ → ε → κ → β} :
    ∑ x : α in s, ∑ y : γ in t, ∑ z : ζ in u, ∑ w : ε in v, ∑ vz : κ in k, f x y z w vz =
      ∑ vz : κ in k, ∑ x : α in s, ∑ y : γ in t, ∑ z : ζ in u, ∑ w : ε in v, f x y z w vz :=
  by
  nth_rw 2 [Finset.sum_comm]
  congr
  ext x
  rw [Finset.sum_4_rotate]

end Finset

theorem Forall.rotate {α β γ : Sort _} {p : α → β → γ → Prop} :
    (∀ (x : α) (y : β) (z : γ), p x y z) ↔ ∀ (z : γ) (x : α) (y : β), p x y z :=
  ⟨fun h _ _ _ => h _ _ _, fun h _ _ _ => h _ _ _⟩

theorem forall_forall_comm {α β γ ζ : Sort _} {p : α → β → γ → ζ → Prop} :
    (∀ (x : α) (y : β) (z : γ) (w : ζ), p x y z w) ↔ ∀ (x : α) (z : γ) (y : β) (w : ζ), p x y z w :=
  ⟨fun h _ _ _ _ => h _ _ _ _, fun h _ _ _ _ => h _ _ _ _⟩

theorem Finset.sum_product_univ {β α γ : Type _} [AddCommMonoid β] [Fintype α] [Fintype γ]
    {f : γ × α → β} : ∑ x : γ × α, f x = ∑ x : γ, ∑ y : α, f (x, y) :=
  Finset.sum_product _ _ _
