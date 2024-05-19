import Mathlib.GroupTheory.Subsemigroup.Center

theorem _root_.Set.center_prod {A B : Type*} [Semigroup A] [Semigroup B] :
  Set.center (A × B) = (Set.center A) ×ˢ (Set.center B) :=
by
  ext x
  simp only [Set.mem_prod, Set.mem_center_iff, isMulCentral_iff, mul_assoc]
  simp only [Prod.forall, implies_true, and_self, and_true]
  nth_rw 2 [← Prod.eta x]
  nth_rw 1 [← Prod.eta x]
  simp only [Prod.mk_mul_mk, Prod.ext_iff]
  exact ⟨λ h => ⟨λ a => (h a x.2).1, λ b => (h x.1 b).2⟩, λ h a b => ⟨h.1 a, h.2 b⟩⟩

theorem _root_.Set.center_pi {ι : Type*} {A : ι → Type*} [Π i, Semigroup (A i)] [DecidableEq ι] :
  Set.center (Π i, A i) = Set.pi Set.univ (λ i => Set.center (A i)) :=
by
  ext x
  simp only [Set.mem_pi, Set.mem_center_iff, isMulCentral_iff, mul_assoc]
  simp only [implies_true, and_self, and_true, Set.mem_univ, forall_true_left]
  simp_rw [Function.funext_iff, Pi.mul_def]
  refine ⟨λ h i a => ?_, λ h _ _ => h _ _⟩
  let a' : Π j, A j := λ j => if h : j = i then (by rw [h]; exact a) else (x j)
  have ha' : a' i = a := by simp only [a', dif_pos]; rfl
  specialize h a' i
  rw [← ha', h]
