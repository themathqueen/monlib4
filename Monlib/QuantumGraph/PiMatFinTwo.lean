import Monlib.QuantumGraph.PiMat

open scoped Functional MatrixOrder ComplexOrder TensorProduct Matrix

def MatProd_algEquiv_PiMat (n' : Fin 2 → Type*) [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)] :
  (Matrix (n' 0) (n' 0) ℂ × Matrix (n' 1) (n' 1) ℂ)
    ≃ₐ[ℂ]
  PiMat ℂ (Fin 2) n' :=
matrixPiFinTwo_algEquiv_prod.symm

abbrev PiFinTwo.swap (n' : Fin 2 → Type*) :
  Fin 2 → Type _ :=
λ i => if i = 0 then (n' 1) else (n' 0)

instance {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] :
  Π i, Fintype ((PiFinTwo.swap n') i) :=
λ i => by simp [PiFinTwo.swap]; split_ifs <;> infer_instance
instance {n' : Fin 2 → Type*} [Π i, DecidableEq (n' i)] :
  Π i, DecidableEq ((PiFinTwo.swap n') i) :=
λ i => by simp [PiFinTwo.swap]; split_ifs <;> infer_instance

def MatProd_algEquiv_PiMat_swap (n' : Fin 2 → Type*) [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)] :
  (Matrix (n' 1) (n' 1) ℂ × Matrix (n' 0) (n' 0) ℂ)
    ≃ₐ[ℂ]
  PiMat ℂ (Fin 2) (PiFinTwo.swap n') :=
MatProd_algEquiv_PiMat (PiFinTwo.swap n')

@[simps]
def Prod.swap_algEquiv
  (α β : Type*) [Semiring α] [Semiring β] [Algebra ℂ α] [Algebra ℂ β] :
    (α × β) ≃ₐ[ℂ] (β × α) where
  toFun x := x.swap
  invFun x := x.swap
  left_inv _ := by simp
  right_inv _ := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  commutes' _ := by simp

def PiMat_finTwo_swapAlgEquiv
  {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)] :
    PiMat ℂ (Fin 2) n' ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo.swap n') :=
(MatProd_algEquiv_PiMat n').symm.trans ((Prod.swap_algEquiv _ _).trans (MatProd_algEquiv_PiMat_swap n'))

abbrev PiFinTwo_same (n : Type*) :
  Fin 2 → Type _ :=
λ _ => n

instance {n : Type*} [Fintype n] :
  Π i, Fintype ((PiFinTwo_same n) i) :=
λ i => by infer_instance
instance {n : Type*} [DecidableEq n] :
  Π i, DecidableEq ((PiFinTwo_same n) i) :=
λ i => by infer_instance

theorem PiMat_finTwo_swapAlgEquiv_apply {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)]
  (x : Matrix (n' 0) (n' 0) ℂ) (y : Matrix (n' 1) (n' 1) ℂ) :
  PiMat_finTwo_swapAlgEquiv (MatProd_algEquiv_PiMat n' (x, y))
    = MatProd_algEquiv_PiMat _ (y, x) :=
rfl

lemma PiFinTwo_same_swap {n : Type*} :
  PiFinTwo.swap (PiFinTwo_same n) = PiFinTwo_same n :=
by ext; simp only [ite_self, Fin.isValue]

def PiMat_finTwo_same_swapAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
    PiMat ℂ (Fin 2) (PiFinTwo_same n) ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n) :=
(MatProd_algEquiv_PiMat (PiFinTwo_same n)).symm.trans ((Prod.swap_algEquiv _ _).trans (MatProd_algEquiv_PiMat (PiFinTwo_same n)))


theorem PiMat_finTwo_same_swapAlgEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
  (x : Matrix n n ℂ) (y : Matrix n n ℂ) :
  PiMat_finTwo_same_swapAlgEquiv (MatProd_algEquiv_PiMat (PiFinTwo_same n) (x, y))
    = MatProd_algEquiv_PiMat _ (y, x) :=
rfl

variable {n : Type*}
  [Fintype n] [DecidableEq n]

theorem AlgEquiv.prod_map_inner_of {K R₁ R₂ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂] [Algebra K R₁] [Algebra K R₂]
  {f : R₁ ≃ₐ[K] R₁} (hf : f.IsInner) {g : R₂ ≃ₐ[K] R₂} (hg : g.IsInner) :
  (f.prod_map g).IsInner :=
by
  rw [AlgEquiv.prod_isInner_iff_prod_map]
  obtain ⟨U, hU, rfl⟩ := hf
  obtain ⟨V, hV, rfl⟩ := hg
  exact ⟨U, hU, V, hV, rfl⟩

instance MatProd_algEquiv_PiMat_same_invertible_of {U : Matrix n n ℂ × Matrix n n ℂ}
  (hU : Invertible U) :
  Invertible ((MatProd_algEquiv_PiMat (PiFinTwo_same n)) U) :=
by
  use (MatProd_algEquiv_PiMat _ ⅟U) <;>
  simp only [← map_mul, invOf_mul_self, mul_invOf_self, map_one]

theorem AlgEquiv.toPiMat_finTwo_same_inner_of_matrix_prod_inner
  {f : (Matrix n n ℂ × Matrix n n ℂ) ≃ₐ[ℂ] (Matrix n n ℂ × Matrix n n ℂ)}
  (hf : f.IsInner) :
  ((MatProd_algEquiv_PiMat (PiFinTwo_same n)).symm.trans
  (f.trans
  (MatProd_algEquiv_PiMat (PiFinTwo_same n)))).IsInner :=
by
  obtain ⟨U, hU, rfl⟩ := hf
  use ((MatProd_algEquiv_PiMat _) U), MatProd_algEquiv_PiMat_same_invertible_of hU
  ext1
  simp [MatProd_algEquiv_PiMat, Algebra.autInner_apply]
  congr
  simp only [PiMat.ext_iff, Fin.forall_fin_two]
  trivial

theorem AlgEquiv.PiMat_finTwo_same
  (f : PiMat ℂ (Fin 2) (PiFinTwo_same n) ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n)) :
  f.IsInner
  ∨
  (∃ (g : PiMat ℂ (Fin 2) (PiFinTwo_same n) ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n))
    (_ : AlgEquiv.IsInner g),
      f = PiMat_finTwo_same_swapAlgEquiv.trans g) :=
by
  let f' := ((MatProd_algEquiv_PiMat _).trans f).trans (MatProd_algEquiv_PiMat _).symm
  rcases (AlgEquiv.matrix_prod_aut' f') with (⟨f₁, f₂, hf⟩ | ⟨g₁, g₂, hg⟩)
  . left
    obtain ⟨U, hf₁⟩ := aut_mat_inner' f₁
    obtain ⟨V, hf₂⟩ := aut_mat_inner' f₂
    have hf₁' : f₁.IsInner := ⟨U, _, hf₁⟩
    have hf₂' : f₂.IsInner := ⟨V, _, hf₂⟩
    have hf' := AlgEquiv.toPiMat_finTwo_same_inner_of_matrix_prod_inner (AlgEquiv.prod_map_inner_of hf₁' hf₂')
    simp [← hf] at hf'
    have :
      (MatProd_algEquiv_PiMat _).symm.trans
      (f'.trans (MatProd_algEquiv_PiMat _)) = f :=
    by ext1; simp [f']
    rw [this] at hf'
    exact hf'
  . right
    obtain ⟨U, hg₁⟩ := aut_mat_inner' g₁
    obtain ⟨V, hg₂⟩ := aut_mat_inner' g₂
    have hg₁' : g₁.IsInner := ⟨U, _, hg₁⟩
    have hg₂' : g₂.IsInner := ⟨V, _, hg₂⟩
    have hg' := AlgEquiv.toPiMat_finTwo_same_inner_of_matrix_prod_inner (AlgEquiv.prod_map_inner_of hg₁' hg₂')
    use (MatProd_algEquiv_PiMat (PiFinTwo_same n)).symm.trans
      ((g₁.prod_map g₂).trans (MatProd_algEquiv_PiMat (PiFinTwo_same n))), hg'
    rw [funext_iff] at hg
    simp only [Fin.isValue, AlgEquiv.coe_trans, Function.comp_apply,
      AlgEquiv.prod_map_apply, Prod.swap, Prod.swap_prod_mk, Prod.map_apply, f',
      AlgEquiv.symm_apply_eq] at hg
    ext1 x
    specialize hg ((MatProd_algEquiv_PiMat _).symm x)
    simp only [AlgEquiv.apply_symm_apply] at hg
    rw [hg]
    rfl

variable {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)]

theorem PiMat.trace_eq_linearMap_trace_toEuclideanLM
  (y : (PiMat ℂ (ι × ι) fun i ↦ p i.1 × p i.2)) :
  PiMat.traceLinearMap y
    = ∑ x : ι × ι, LinearMap.trace ℂ (EuclideanSpace ℂ (p x.1 × p x.2))
      (PiMat_toEuclideanLM y x) :=
by
  simp only [StarAlgEquiv.piCongrRight_apply, StarAlgEquiv.ofAlgEquiv_coe,
    AlgEquiv.ofLinearEquiv_apply, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    Matrix.traceLinearMap_apply, Matrix.blockDiagonal'AlgHom_apply,
    Matrix.trace_blockDiagonal']
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (p i.1 × p i.2)),
    Matrix.toEuclideanLin_eq_toLin, LinearMap.toMatrix_toLin]

variable {φ : (i : ι) → Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : ∀ (i : ι), (φ i).IsFaithfulPosMap]

theorem QuantumGraph.Real.dim_of_piMat_submodule_eq
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hA : QuantumGraph.Real (PiMat ℂ ι p) A) :
  hA.toQuantumGraph.dim_of_piMat_submodule =
    ∑ i, Module.finrank ℂ (hA.PiMat_submodule i) :=
by
  rw [← Nat.cast_inj (R := ℂ)]
  rw [QuantumGraph.dim_of_piMat_submodule_eq_trace]
  simp only [Nat.cast_sum, ←
    orthogonalProjection_trace (R := ℂ),
    QuantumGraph.Real.PiMat_submoduleOrthogonalProjection,
    LinearMap.coe_toContinuousLinearMap]
  rw [← PiMat.trace_eq_linearMap_trace_toEuclideanLM]

theorem
  Module.Dual.pi.IsFaithfulPosMap.includeBlock_right_inner {i : ι}
   (x : PiMat ℂ ι p) (y : Matrix (p i) (p i) ℂ) :
    (inner x (Matrix.includeBlock y) : ℂ) = inner (x i) y :=
by rw [← LinearMap.adjoint_inner_left, includeBlock_adjoint]

variable
  {ψ : Π i : Fin 2, Module.Dual ℂ (Matrix (PiFinTwo_same n i) (PiFinTwo_same n i) ℂ)}
  [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  {A : (PiMat ℂ (Fin 2) (PiFinTwo_same n)) →ₗ[ℂ] (PiMat ℂ (Fin 2) (PiFinTwo_same n))}
  (hA : QuantumGraph.Real _ A)

theorem LinearMap.proj_adjoint_apply
  (i : ι) (x : Matrix (p i) (p i) ℂ) :
  (LinearMap.adjoint (LinearMap.proj (R := ℂ) i)) x
    = Matrix.includeBlock x :=
by
  apply ext_inner_left ℂ
  intro y
  simp [LinearMap.adjoint_inner_right]
  rw [Module.Dual.pi.IsFaithfulPosMap.includeBlock_right_inner]

theorem LinearMap.proj_adjoint
  (i : ι) :
  LinearMap.adjoint (LinearMap.proj (R := ℂ) i)
    = LinearMap.single ℂ (λ r => Mat ℂ (p r)) i :=
by ext1; rw [LinearMap.proj_adjoint_apply]; rfl

theorem LinearMap.single_adjoint
  (i : ι) :
  LinearMap.adjoint (LinearMap.single ℂ (λ r => Mat ℂ (p r)) i)
    = LinearMap.proj (R := ℂ) i :=
by rw [← proj_adjoint, adjoint_adjoint]

theorem LinearMap.eq_sum_conj_adjoint_proj_comp_proj
  (A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p) :
  A = ∑ i : ι × ι,
    LinearMap.adjoint (LinearMap.proj i.1)
      ∘ₗ (LinearMap.proj i.1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i.2))
      ∘ₗ LinearMap.proj i.2 :=
by
  simp_rw [LinearMap.proj_adjoint, Finset.sum_product_univ,
    LinearMap.comp_assoc]
  rw [LinearMap.lrsum_eq_single_proj_lrcomp]

private
lemma
  QuantumGraph.Real.PiFinTwo_same_exists_proj_conj_add_of_piMat_submodule_eq_bot
  (h₂ : hA.PiMat_submodule (1, 0) = ⊥)
  (h₃ : hA.PiMat_submodule (0, 1) = ⊥) :
  -- ∃ (f₁ f₂ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ),
    (LinearMap.adjoint (LinearMap.proj 0)
      ∘ₗ ((LinearMap.proj 0) ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj 0)) ∘ₗ LinearMap.proj 0)
    + (LinearMap.adjoint (LinearMap.proj 1)
      ∘ₗ ((LinearMap.proj 1) ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj 1)) ∘ₗ LinearMap.proj 1) = A :=
by
  simp only [Prod.fst_zero, Fin.isValue, Prod.snd_zero,
    QuantumGraph.Real.PiMat_submodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero] at h₂ h₃
  simp_all only [PiFinTwo_same]
  nth_rw 3 [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hψ) A]
  simp only [Finset.sum_product_univ, Fin.sum_univ_two,
    Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one,
    h₂, h₃, LinearMap.zero_comp, LinearMap.comp_zero, zero_add, add_zero]

private
lemma QuantumGraph.Real.piFinTwo_same_piMat_submodule_eq_bot_of_adjoint_and_dim_eq_one
  (hA₂ : LinearMap.adjoint A = A)
  (hd : hA.toQuantumGraph.dim_of_piMat_submodule = 1) :
    hA.PiMat_submodule (1, 0) = ⊥
    ∧ ((Module.finrank ℂ (hA.PiMat_submodule 0) = 1
      ∧ hA.PiMat_submodule 1 = ⊥)
      ∨
      (hA.PiMat_submodule 0 = ⊥
        ∧ Module.finrank ℂ (hA.PiMat_submodule 1) = 1)) :=
by
  simp only [QuantumGraph.Real.dim_of_piMat_submodule_eq,
    Finset.sum_product_univ, Fin.sum_univ_two,
    Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one] at hd
  simp only [Fin.isValue, Nat.add_eq_one_iff, AddLeftCancelMonoid.add_eq_zero,
    Submodule.finrank_eq_zero, Prod.fst_zero, Prod.snd_zero, Prod.fst_one, Prod.snd_one] at hd
  simp only [Fin.isValue, hA.PiMat_submodule_eq_bot_iff_swap_eq_bot_of_adjoint hA₂ (0, 1),
    Prod.swap_prod_mk] at hd
  rcases hd with (h | h)
  . obtain ⟨h₁, (h₂ | h₂)⟩ := h
    . exact ⟨h₂.1, Or.inr ⟨h₁.1, h₂.2⟩⟩
    . rw [h₁.2] at h₂
      simp only [finrank_bot, zero_ne_one, false_and] at h₂
  . obtain ⟨(h₁ | h₁), h₂⟩ := h
    . rw [hA.PiMat_submodule_eq_bot_iff_swap_eq_bot_of_adjoint hA₂ (1, 0),
        Prod.swap_prod_mk] at h₂
      rw [h₂.1, finrank_bot] at h₁
      simp only [zero_ne_one, and_false] at h₁
    . exact ⟨h₁.2, Or.inl ⟨h₁.1, h₂.2⟩⟩

lemma Pi.nat_eq_zero_of_sum_eq_one_and_unique_one
  {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℕ}
  (h : ∑ i, f i = 1) {i : ι} (hd : f i = 1)
  {j : ι} (hj : j ≠ i) : f j = 0 :=
by
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i), hd] at h
  simp only [add_right_eq_self, Finset.sum_eq_zero_iff, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_singleton, true_and] at h
  exact h _ hj

theorem Finset.sum_nat_eq_one_iff_exists_unique_eq_one
  {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℕ}
  (h : ∑ i, f i = 1) :
  (∃! i : ι, f i = 1) :=
by
  have this1 : ∀ i : ι, f i ≤ 1 :=
  by
    intro i
    by_contra!
    have :=
    calc 1 = ∑ j, f j := h.symm
      _ = f i
        + ∑ j ∈ Finset.univ \ {i}, f j :=
          by rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ _)]
      _ > 1 + ∑ j ∈ Finset.univ \ {i}, f j :=
        by
          nlinarith
      _ ≥ 1 := by norm_num
    linarith
  have : ∃! i, 1 ≤ f i :=
  by
    apply existsUnique_of_exists_of_unique
    . by_contra!
      simp only [Nat.lt_one_iff] at this
      simp only [this, Finset.sum_const_zero] at h
      norm_num at h
    . intro y₁ y₂ hy hd
      by_contra!
      have :=
      calc
        1 =  ∑ i : ι, f i := h.symm
        _ = f y₁ + f y₂
          + ∑ i ∈ (Finset.univ \ {y₁}) \ {y₂}, f i :=
            by
              have : y₂ ∈ Finset.univ \ {y₁} := by simp [this.symm]
              rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ y₁),
                Finset.sum_eq_add_sum_diff_singleton this, add_assoc]
        _ ≥ 1 + 1
          + ∑ i ∈ (Finset.univ \ {y₁}) \ {y₂}, f i :=
            by
              apply LE.le.ge
              linarith
        _ ≥ 2 := by norm_num
      linarith
  obtain ⟨i, ⟨hi, hii⟩⟩ := this
  simp_rw [le_antisymm_iff]
  use i
  simp only [this1, true_and, hi]
  exact hii

theorem QuantumGraph.Real.dim_of_piMat_submodule_eq_zero_iff_eq_zero
  {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)]
  {φ : (i : ι) → Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap]
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real _ A) :
  hA.toQuantumGraph.dim_of_piMat_submodule = 0 ↔ A = 0 :=
by
  simp only [QuantumGraph.Real.dim_of_piMat_submodule_eq]
  simp_rw [Finset.sum_eq_zero_iff,
    Submodule.finrank_eq_zero,
    QuantumGraph.Real.PiMat_submodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero]
  constructor
  . intro h
    rw [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hφ) A]
    simp only [h _ (Finset.mem_univ _), LinearMap.comp_zero, LinearMap.zero_comp,
      Finset.sum_const_zero]
  . rintro rfl
    simp only [LinearMap.zero_comp, LinearMap.comp_zero,
      Finset.mem_univ, imp_self, implies_true]

theorem QuantumGraph.Real.exists_unique_includeMap_of_adjoint_and_dim_ofPiMat_submodule_eq_one
  {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)]
  {φ : (i : ι) → Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap]
  {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real _ A)
  (hA₂ : LinearMap.adjoint A = A)
  (hd : hA.toQuantumGraph.dim_of_piMat_submodule = 1) :
  ∃! i : ι,
    LinearMap.adjoint (LinearMap.proj i)
      ∘ₗ LinearMap.proj i
      ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i) ∘ₗ LinearMap.proj i = A :=
by
  have hA_neZero :=
    (not_iff_not.mpr (hA.dim_of_piMat_submodule_eq_zero_iff_eq_zero)).mp
    (ne_zero_of_eq_one hd)
  simp only [QuantumGraph.Real.dim_of_piMat_submodule_eq] at hd
  obtain ⟨i, hi, hii⟩ := Finset.sum_nat_eq_one_iff_exists_unique_eq_one hd
  have this₁ : ∀ j ∈ Finset.univ \ {i},
    Module.finrank ℂ (hA.PiMat_submodule j) = 0 :=
  by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
    exact Pi.nat_eq_zero_of_sum_eq_one_and_unique_one hd hi hj
  have this₂ := (hA.piMat_submodule_finrank_eq_swap_of_adjoint hA₂)
  rw [this₂] at hi
  have this₃ := Prod.ext_iff.mp (hii _ hi)
  simp only [Prod.fst_swap, Prod.snd_swap] at this₃
  simp_rw [Submodule.finrank_eq_zero,
    QuantumGraph.Real.PiMat_submodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero] at this₁
  have : ∑ x ∈ Finset.univ \ {i},
      LinearMap.adjoint (LinearMap.proj x.1) ∘ₗ
        ((LinearMap.proj x.1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj x.2))) ∘ₗ LinearMap.proj x.2
      = (0 : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p) :=
  by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [this₁ _ hj, LinearMap.comp_zero, LinearMap.zero_comp]
  have hAA : A = LinearMap.adjoint (LinearMap.proj i.1)
    ∘ₗ (LinearMap.proj i.1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i.1))
    ∘ₗ LinearMap.proj i.1 :=
  by
    nth_rw 1 [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hφ) A]
    rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
    simp only [this, add_zero]
    rw [this₃.1]
  refine ⟨i.1, hAA.symm, λ j hj => ?_⟩
  . by_contra!
    specialize this₁ (j, j)
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Prod.ext_iff, this₃.1, and_self] at this₁
    have :=
    calc (0 : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p)
        = LinearMap.adjoint (LinearMap.proj j) ∘ₗ
          (LinearMap.proj j ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj j)) ∘ₗ LinearMap.proj j := by
            simp only [this₁ this, LinearMap.comp_zero, LinearMap.zero_comp]
      _ = A := by simp only [LinearMap.comp_assoc, hj]
      _ ≠ 0 := hA_neZero
    simp only [ne_eq, not_true_eq_false] at this

theorem QuantumGraph.Real.piFinTwo_same_exists_matrix_map_eq_map_of_adjoint_and_dim_eq_one
  (hA₂ : LinearMap.adjoint A = A)
  (hd : hA.toQuantumGraph.dim_of_piMat_submodule = 1) :
  -- (∃ f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
  LinearMap.adjoint (LinearMap.proj 0)
    ∘ₗ LinearMap.proj 0 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj 0) ∘ₗ LinearMap.proj 0 = A
  ∨
    -- ∃ f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
      LinearMap.adjoint (LinearMap.proj 1)
    ∘ₗ LinearMap.proj 1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj 1) ∘ₗ LinearMap.proj 1 = A :=
by
  obtain ⟨h₁, h⟩ := hA.piFinTwo_same_piMat_submodule_eq_bot_of_adjoint_and_dim_eq_one hA₂ hd
  have h₂ := h₁
  rw [hA.PiMat_submodule_eq_bot_iff_swap_eq_bot_of_adjoint hA₂,
    Prod.swap_prod_mk] at h₂
  obtain hf := hA.PiFinTwo_same_exists_proj_conj_add_of_piMat_submodule_eq_bot h₁ h₂
  simp only [hA.PiMat_submodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero,
    Prod.fst_one, Prod.snd_one, Prod.fst_zero, Prod.snd_zero] at h
  rcases h with (h | h)
  <;>
  simp only [h.1, h.2, LinearMap.comp_zero, LinearMap.zero_comp,
    add_zero, zero_add, LinearMap.comp_assoc] at hf
  exact Or.inl hf
  exact Or.inr hf
  -- exact Or.inl ⟨_, hf⟩
  -- exact Or.inr ⟨_, hf⟩

def AlgHom.proj
  (R : Type*) {ι : Type*} [CommSemiring R] {φ : ι → Type*}
  [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (i : ι) :
    (Π i, φ i) →ₐ[R] φ i where
  toFun x := x i
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  map_one' := by simp
  map_zero' := by simp
  commutes' _ := by simp

theorem AlgHom.proj_apply
  {R ι : Type*} [CommSemiring R] {φ : ι → Type*}
  [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (x : Π i, φ i) (i : ι) :
  AlgHom.proj R i x = x i :=
rfl

theorem AlgHom.proj_toLinearMap
  {R ι : Type*} [CommSemiring R] {φ : ι → Type*}
  [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (i : ι) :
  (AlgHom.proj R i).toLinearMap =
    @LinearMap.proj R ι _ φ _ _ i :=
rfl

def NonUnitalAlgHom.single (R : Type*) {ι : Type*} [CommSemiring R]
  [DecidableEq ι]
  (φ : ι → Type*) [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (i : ι) :
    φ i →ₙₐ[R] (Π i, φ i) where
  toFun x := LinearMap.single R φ i x
  map_add' _ _ := by simp [Pi.single_add]
  map_smul' _ _ := by simp [Pi.single_smul]
  map_mul' _ _ := by simp [Pi.single_mul]
  map_zero' := by simp [Pi.single_zero]

theorem NonUnitalAlgHom.single_apply
  {R ι : Type*} [CommSemiring R] [DecidableEq ι]
  {φ : ι → Type*} [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (i : ι) (x : φ i) :
  NonUnitalAlgHom.single R φ i x = Pi.single i x :=
rfl

set_option linter.deprecated false in
theorem NonUnitalAlgHom.single_toLinearMap
  {R ι : Type*} [CommSemiring R] [DecidableEq ι]
  {φ : ι → Type*} [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (i : ι) :
  (NonUnitalAlgHom.single R φ i).toLinearMap =
    LinearMap.single R φ i :=
rfl

theorem LinearMap.single_isReal
  {R ι : Type*} [DecidableEq ι] [Semiring R] {φ : ι → Type*}
  [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
  [(i : ι) → StarAddMonoid (φ i)] (i : ι) :
  LinearMap.IsReal (LinearMap.single R φ i) :=
by intro; simp [Pi.single_star]

theorem LinearMap.proj_isReal
  {R ι : Type*} [DecidableEq ι] [Semiring R] {φ : ι → Type*}
  [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
  [(i : ι) → StarAddMonoid (φ i)] (i : ι) :
  LinearMap.IsReal (LinearMap.proj (R := R) (φ := φ) i) :=
by intro; simp

theorem LinearMap.single_comp_inj
  {R ι B : Type*} [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)]
  [AddCommMonoid B] [Module R B] [(i : ι) → Module R (φ i)] [DecidableEq ι] (i : ι)
  (f g : B →ₗ[R] φ i) :
  LinearMap.single R φ i ∘ₗ f = LinearMap.single R φ i ∘ₗ g ↔ f = g :=
by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.single_apply, Pi.single_inj]

theorem LinearMap.comp_proj_inj
  {R ι B : Type*} [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)]
  [AddCommMonoid B] [Module R B] [(i : ι) → Module R (φ i)] [DecidableEq ι] (i : ι)
  (f g : φ i →ₗ[R] B) :
  f ∘ₗ LinearMap.proj (R := R) i = g ∘ₗ LinearMap.proj (R := R) i ↔ f = g :=
by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.proj_apply]
  refine ⟨λ h x => ?_, λ h _ => h _⟩
  simpa only [Pi.single_eq_same] using h (Pi.single i x)

theorem LinearMap.proj_comp_inj
  {R ι B : Type*} [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)]
  [AddCommMonoid B] [Module R B] [(i : ι) → Module R (φ i)] [DecidableEq ι]
  (f g : B →ₗ[R] Π r, φ r) :
  (∀ i, LinearMap.proj (R := R) i ∘ₗ f = LinearMap.proj (R := R) i ∘ₗ g) ↔ f = g :=
by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.proj_apply, funext_iff]
  rw [forall_comm]

theorem QuantumGraph.isReal_iff_conj_proj_adjoint_isReal
  (i : ι)
  (f : Mat ℂ (p i) →ₗ[ℂ] Mat ℂ (p i)) :
  QuantumGraph.Real _ f
    ↔
  QuantumGraph.Real (PiMat ℂ ι p)
    (LinearMap.adjoint (LinearMap.proj i) ∘ₗ f ∘ₗ LinearMap.proj i) :=
by
  simp only [QuantumGraph.real_iff,
    LinearMap.isReal_iff,
    LinearMap.real_comp,
    ]
  rw [LinearMap.proj_adjoint,
    ← LinearMap.single_adjoint (hφ := hφ),
    ← NonUnitalAlgHom.single_toLinearMap]
  simp_rw [schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint (NonUnitalAlgHom.single ℂ (fun r ↦ Mat ℂ (p r)) i)
    (NonUnitalAlgHom.single ℂ (fun r ↦ Mat ℂ (p r)) i),
    NonUnitalAlgHom.single_toLinearMap, LinearMap.single_adjoint]
  nth_rw 2 [LinearMap.real_of_isReal (LinearMap.single_isReal i)]
  nth_rw 3 [LinearMap.real_of_isReal (congrFun rfl)]
  simp_rw [LinearMap.single_comp_inj,
    LinearMap.comp_proj_inj (R := ℂ) (ι := ι)
      (φ := λ r => Mat ℂ (p r)) i]

theorem QuantumGraph.Real.conj_proj_isReal
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph.Real _ f) (i : ι) :
  QuantumGraph.Real _
    ((LinearMap.proj (R := ℂ) i) ∘ₗ f ∘ₗ LinearMap.adjoint (LinearMap.proj (R := ℂ) i)) :=
by
  simp only [QuantumGraph.real_iff, LinearMap.isReal_iff,
    LinearMap.real_comp]
  simp only [LinearMap.proj_adjoint,
    LinearMap.real_of_isReal (LinearMap.single_isReal (R := ℂ) (ι := ι) (φ := λ r => Mat ℂ (p r)) _),
    LinearMap.real_of_isReal (LinearMap.proj_isReal (R := ℂ) (ι := ι)
      (φ := λ r => Mat ℂ (p r)) _), LinearMap.real_of_isReal hf.2, and_true]
  rw [← LinearMap.proj_adjoint,
    ← AlgHom.proj_toLinearMap]
  simp_rw [schurMul_algHom_comp_algHom_adjoint, hf.1]

lemma schurMul_proj_adjoint_comp
  {B : Type*} [starAlgebra B] [QuantumSet B]
  (i : ι)
  (f g : B →ₗ[ℂ] Mat ℂ (p i)) :
  (LinearMap.adjoint (LinearMap.proj i) ∘ₗ f) •ₛ (LinearMap.adjoint (LinearMap.proj i) ∘ₗ g)
    = LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) i)
      ∘ₗ (f •ₛ g) :=
by
  simp only [LinearMap.proj_adjoint, ← NonUnitalAlgHom.single_toLinearMap,
    schurMul_apply_apply, TensorProduct.map_comp]
  simp only [← LinearMap.comp_assoc]
  congr 2
  exact Eq.symm (nonUnitalAlgHom_comp_mul (NonUnitalAlgHom.single ℂ (fun r ↦ Mat ℂ (p r)) i))

lemma schurMul_proj_comp
  {B : Type*} [starAlgebra B] [QuantumSet B]
  (f g : B →ₗ[ℂ] PiMat ℂ ι p) (i : ι) :
  ((LinearMap.proj i) ∘ₗ f) •ₛ ((LinearMap.proj i) ∘ₗ g)
    = (LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) i)
      ∘ₗ (f •ₛ g) :=
by
  simp only [schurMul_apply_apply, TensorProduct.map_comp]
  simp only [← LinearMap.comp_assoc]
  congr 2
  rw [← AlgHom.proj_toLinearMap]
  exact TensorProduct.map_mul'_commute_iff.mpr fun x ↦ congrFun rfl

lemma schurMul_comp_proj
  {B : Type*} [starAlgebra B] [QuantumSet B]
  (i : ι) (f g : Mat ℂ (p i) →ₗ[ℂ] B) :
  (f ∘ₗ (LinearMap.proj i)) •ₛ (g ∘ₗ (LinearMap.proj i))
    = (f •ₛ g) ∘ₗ (LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) i) :=
by
  apply_fun LinearMap.adjoint using LinearEquiv.injective _
  simp only [schurMul_adjoint, LinearMap.adjoint_comp]
  exact schurMul_proj_adjoint_comp i (LinearMap.adjoint f) (LinearMap.adjoint g)

lemma schurMul_comp_proj_adjoint
  {B : Type*} [starAlgebra B] [QuantumSet B]
  (f g : PiMat ℂ ι p →ₗ[ℂ] B) (i : ι) :
  (f ∘ₗ LinearMap.adjoint (LinearMap.proj i)) •ₛ (g ∘ₗ LinearMap.adjoint (LinearMap.proj i))
    = (f •ₛ g) ∘ₗ LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) i) :=
by
  apply_fun LinearMap.adjoint using LinearEquiv.injective _
  simp only [schurMul_adjoint, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  exact schurMul_proj_comp (LinearMap.adjoint f) (LinearMap.adjoint g) i

theorem QuantumGraph.Real.proj_adjoint_comp_proj_conj_isRealQuantumGraph
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph.Real (PiMat ℂ ι p) f)
  (i : ι × ι) :
  QuantumGraph.Real (PiMat ℂ ι p)
    (LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) i.1)
      ∘ₗ LinearMap.proj i.1
      ∘ₗ f
      ∘ₗ LinearMap.adjoint (LinearMap.proj i.2)
      ∘ₗ LinearMap.proj i.2) :=
by
  constructor
  . rw [schurMul_proj_adjoint_comp, schurMul_proj_comp]
    simp only [← LinearMap.comp_assoc]
    rw [schurMul_comp_proj, schurMul_comp_proj_adjoint]
    simp only [LinearMap.comp_assoc, hf.1]
  . simp only [LinearMap.isReal_iff, LinearMap.real_comp,
      LinearMap.proj_adjoint, LinearMap.real_of_isReal
        (LinearMap.single_isReal (R := ℂ) (φ := λ r => Mat ℂ (p r)) _),
      LinearMap.real_of_isReal (LinearMap.proj_isReal (R := ℂ) (φ := λ r => Mat ℂ (p r)) _),
      LinearMap.real_of_isReal hf.2]

theorem schurMul_proj_adjoint_comp_of_ne_eq_zero
  {B : Type*} [starAlgebra B] [QuantumSet B]
  {i j : ι} (hij : i ≠ j)
  (f : B →ₗ[ℂ] Mat ℂ (p i))
  (g : B →ₗ[ℂ] Mat ℂ (p j)) :
  (LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) i)
    ∘ₗ f)
  •ₛ
  (LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) j)
    ∘ₗ g)
  = 0 :=
by
  simp only [schurMul_apply_apply, TensorProduct.map_comp, ← LinearMap.comp_assoc]
  have : LinearMap.mul' ℂ ((i : ι) → Mat ℂ (p i))
    ∘ₗ TensorProduct.map
      (LinearMap.adjoint (LinearMap.proj (R := ℂ) i))
      (LinearMap.adjoint (LinearMap.proj j))
    = 0 :=
  by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      LinearMap.proj_adjoint_apply, LinearMap.zero_apply]
    exact Matrix.includeBlock_hMul_ne_same hij x y
  simp_rw [this, LinearMap.zero_comp]

theorem schurMul_comp_proj_of_ne_eq_zero
  {B : Type*} [starAlgebra B] [QuantumSet B]
  {i j : ι} (hij : i ≠ j)
  (f : Mat ℂ (p i) →ₗ[ℂ] B)
  (g : Mat ℂ (p j) →ₗ[ℂ] B) :
  (f ∘ₗ LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) i)
  •ₛ
  (g ∘ₗ LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) j)
  = 0 :=
by
  apply_fun LinearMap.adjoint using LinearEquiv.injective _
  simp only [schurMul_adjoint, LinearMap.adjoint_comp, map_zero]
  exact schurMul_proj_adjoint_comp_of_ne_eq_zero hij (LinearMap.adjoint f) (LinearMap.adjoint g)

theorem piMat_isRealQuantumGraph_iff_forall_conj_adjoint_proj_comp_proj
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} :
  QuantumGraph.Real (PiMat ℂ ι p) f
    ↔
  ∀ i : ι × ι, QuantumGraph.Real (PiMat ℂ ι p)
    (LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := λ r => Mat ℂ (p r)) i.1)
      ∘ₗ LinearMap.proj i.1
      ∘ₗ f
      ∘ₗ LinearMap.adjoint (LinearMap.proj i.2)
      ∘ₗ LinearMap.proj i.2) :=
by
  refine ⟨λ h i => h.proj_adjoint_comp_proj_conj_isRealQuantumGraph i, λ h => ?_⟩
  constructor
  . rw [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hφ) f]
    simp only [map_sum, LinearMap.sum_apply]
    congr
    ext1 i
    rw [Finset.sum_eq_add_sum_diff_singleton (i := i) (Finset.mem_univ i)]
    simp only [LinearMap.comp_assoc, (h i).1, add_right_eq_self]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
    rw [Prod.eq_iff_fst_eq_snd_eq, not_and_or] at hj
    rcases hj with (h | h)
    . rw [schurMul_proj_adjoint_comp_of_ne_eq_zero h]
    . simp only [← LinearMap.comp_assoc]
      rw [schurMul_comp_proj_of_ne_eq_zero h]
  . simp only [LinearMap.isReal_iff]
    rw [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hφ) f]
    simp only [LinearMap.real_sum,
      LinearMap.comp_assoc, LinearMap.real_of_isReal (h _).2]

theorem Pi.single_zero_piFinTwo_same_apply (x : Matrix n n ℂ) :
  (Pi.single 0 x : PiMat ℂ (Fin 2) _) =
  MatProd_algEquiv_PiMat (PiFinTwo_same n) (x, 0) :=
by
  ext1
  simp [MatProd_algEquiv_PiMat, Pi.single, Function.update]
  rfl
theorem Pi.single_one_piFinTwo_same_apply (x : Matrix n n ℂ) :
  (Pi.single 1 x : PiMat ℂ (Fin 2) _) =
  MatProd_algEquiv_PiMat (PiFinTwo_same n) (0, x) :=
by
  simp only [funext_iff, Fin.forall_fin_two, MatProd_algEquiv_PiMat,
    matrixPiFinTwo_algEquiv_prod_symm_apply,
    single_eq_same, dite_true, single_eq_of_ne (zero_ne_one' _),
    one_ne_zero, dite_false]
  exact ⟨rfl, rfl⟩

theorem
  PiMat_finTwo_same_swap_swap (x : PiMat ℂ (Fin 2) (PiFinTwo_same n)) :
  PiMat_finTwo_same_swapAlgEquiv
    (PiMat_finTwo_same_swapAlgEquiv x) = x :=
by simp [PiMat_finTwo_same_swapAlgEquiv]

theorem PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_zero (x : Matrix n n ℂ) :
  PiMat_finTwo_same_swapAlgEquiv (Pi.single 0 x) = (Pi.single 1 x : PiMat ℂ (Fin 2) (PiFinTwo_same n)) :=
by
  simp only [Pi.single_zero_piFinTwo_same_apply,
    PiMat_finTwo_same_swapAlgEquiv_apply, Pi.single_one_piFinTwo_same_apply]

theorem PiMat_finTwo_same_swapAlgEquiv_comp_linearMapSingle_zero :
  PiMat_finTwo_same_swapAlgEquiv.toLinearMap.comp (LinearMap.single ℂ _ 0) =
    (LinearMap.single ℂ _ 1 : _ →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n)) :=
by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.single_apply]
  exact PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_zero

theorem PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_one (x : Matrix n n ℂ) :
  PiMat_finTwo_same_swapAlgEquiv (Pi.single 1 x) = (Pi.single 0 x : PiMat ℂ (Fin 2) (PiFinTwo_same n)) :=
by
  rw [← PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_zero,
    PiMat_finTwo_same_swap_swap]

theorem PiMat_finTwo_same_swapAlgEquiv_comp_linearMapSingle_one :
  PiMat_finTwo_same_swapAlgEquiv.toLinearMap ∘ₗ (LinearMap.single ℂ _ 1) = (LinearMap.single ℂ _ 0 : _ →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo_same n)) :=
by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.single_apply]
  exact PiMat_finTwo_same_swapAlgEquiv_apply_piSingle_one

theorem QuantumGraph.Real.schurProjection_proj_conj
  {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}
  (hf : QuantumGraph.Real _ f)
  (i : ι × ι) :
  schurProjection (A := Mat ℂ (p i.2)) (B := Mat ℂ (p i.1))
  ((LinearMap.proj (R := ℂ) i.1) ∘ₗ f
    ∘ₗ (LinearMap.adjoint (LinearMap.proj i.2))) :=
by
  constructor
  . rw [schurMul_proj_comp, schurMul_comp_proj_adjoint, hf.1]
  . rw [LinearMap.isReal_iff]
    simp_rw [LinearMap.real_comp, LinearMap.real_of_isReal hf.2, LinearMap.proj_adjoint,
    LinearMap.real_of_isReal (LinearMap.proj_isReal (φ := λ r => Mat ℂ (p r)) _),
    LinearMap.real_of_isReal (LinearMap.single_isReal (φ := λ r => Mat ℂ (p r)) _)]
