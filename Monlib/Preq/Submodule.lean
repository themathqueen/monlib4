import Mathlib.Algebra.Module.Submodule.Basic

lemma _root_.Submodule.ext_iff {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  {p q : Submodule R M} :
  p = q ↔ ∀ x, x ∈ p ↔ x ∈ q :=
⟨λ h x => by rw [h], λ h => Submodule.ext h⟩
