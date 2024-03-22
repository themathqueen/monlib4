import LinearAlgebra.MyMatrix.Basic
import LinearAlgebra.InnerAut

#align_import linear_algebra.my_matrix.spectra

instance multisetCoe {α β : Type _} [Coe α β] : Coe (Multiset α) (Multiset β)
    where coe s := s.map (coe : α → β)

theorem Finset.val.map_coe {α β γ : Type _} (f : α → β) (s : Finset α) [Coe β γ] :
    ((s.val.map f : Multiset β) : Multiset γ) = s.val.map ↑f :=
  by
  unfold_coes
  simp only [Multiset.map_map, Function.comp_apply, AddMonoidHom.toFun_eq_coe]

noncomputable instance multisetCoeRToIsROrC {𝕜 : Type _} [IsROrC 𝕜] :
    Coe (Multiset ℝ) (Multiset 𝕜) :=
  @multisetCoe ℝ 𝕜 ⟨coe⟩

namespace Matrix

variable {n 𝕜 : Type _} [IsROrC 𝕜] [Fintype n] [DecidableEq n] [DecidableEq 𝕜]

open scoped Matrix

noncomputable def IsAlmostHermitian.scalar {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : 𝕜 := by choose α hα using hx <;> exact α

noncomputable def IsAlmostHermitian.matrix {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : Matrix n n 𝕜 := by
  choose y hy using is_almost_hermitian.scalar._proof_1 hx <;> exact y

theorem IsAlmostHermitian.eq_smul_matrix {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : x = hx.scalar • hx.Matrix :=
  (IsAlmostHermitian.Matrix._proof_1 hx).1.symm

theorem IsAlmostHermitian.matrix_isHermitian {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : hx.Matrix.IsHermitian :=
  (IsAlmostHermitian.Matrix._proof_1 hx).2

noncomputable def IsAlmostHermitian.eigenvalues {x : Matrix n n 𝕜} (hx : x.IsAlmostHermitian) :
    n → 𝕜 := by
  intro i
  exact hx.scalar • hx.matrix_is_hermitian.eigenvalues i

noncomputable def IsAlmostHermitian.spectra {A : Matrix n n 𝕜} (hA : A.IsAlmostHermitian) :
    Multiset 𝕜 :=
  Finset.univ.val.map fun i => hA.Eigenvalues i

noncomputable def IsHermitian.spectra {A : Matrix n n 𝕜} (hA : A.IsHermitian) : Multiset ℝ :=
  Finset.univ.val.map fun i => hA.Eigenvalues i

theorem IsHermitian.spectra_coe {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (hA.spectra : Multiset 𝕜) = Finset.univ.val.map fun i => hA.Eigenvalues i :=
  by
  unfold_coes
  simp only [Multiset.map_map, is_hermitian.spectra]

open scoped BigOperators

theorem IsHermitian.mem_coe_spectra_diagonal {A : n → 𝕜} (hA : (diagonal A).IsHermitian) (x : 𝕜) :
    x ∈ (hA.spectra : Multiset 𝕜) ↔ ∃ i : n, A i = x :=
  by
  simp_rw [is_hermitian.spectra_coe, Multiset.mem_map]
  simp only [Finset.mem_univ_val, true_and_iff]
  have :
    ((x : 𝕜) ∈ {b : 𝕜 | ∃ a, ↑(hA.eigenvalues a) = b} ↔ (x : 𝕜) ∈ {b : 𝕜 | ∃ a, A a = b}) ↔
      ((∃ a, (hA.eigenvalues a : 𝕜) = x) ↔ ∃ a, A a = x) :=
    by simp_rw [Set.mem_setOf]
  rw [← this]
  clear this
  revert x
  rw [← Set.ext_iff, ← is_hermitian.spectrum, diagonal.spectrum]

theorem IsHermitian.spectra_set_eq_spectrum {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    {x : 𝕜 | x ∈ (hA.spectra : Multiset 𝕜)} = spectrum 𝕜 (toLin' A) :=
  by
  ext
  simp_rw [is_hermitian.spectra_coe, hA.spectrum, Set.mem_setOf, Multiset.mem_map,
    Finset.mem_univ_val, true_and_iff]

theorem IsHermitian.of_innerAut {A : Matrix n n 𝕜} (hA : A.IsHermitian) (U : unitaryGroup n 𝕜) :
    (innerAut U A).IsHermitian :=
  (IsHermitian.innerAut_iff U A).mp hA

theorem isAlmostHermitian_iff_smul {A : Matrix n n 𝕜} :
    A.IsAlmostHermitian ↔ ∀ α : 𝕜, (α • A).IsAlmostHermitian :=
  by
  constructor
  · rintro ⟨β, y, rfl, hy⟩ α
    rw [smul_smul]
    exact ⟨α * β, y, rfl, hy⟩
  · intro h
    specialize h 1
    rw [one_smul] at h
    exact h

theorem IsAlmostHermitian.smul {A : Matrix n n 𝕜} (hA : A.IsAlmostHermitian) (α : 𝕜) :
    (α • A).IsAlmostHermitian :=
  isAlmostHermitian_iff_smul.mp hA _

theorem IsAlmostHermitian.of_innerAut {A : Matrix n n 𝕜} (hA : A.IsAlmostHermitian)
    (U : unitaryGroup n 𝕜) : (innerAut U A).IsAlmostHermitian :=
  by
  obtain ⟨α, y, rfl, hy⟩ := hA
  refine' ⟨α, inner_aut U y, _, hy.of_inner_aut _⟩
  simp_rw [SMulHomClass.map_smul]

theorem isAlmostHermitian_iff_of_innerAut {A : Matrix n n 𝕜} (U : unitaryGroup n 𝕜) :
    A.IsAlmostHermitian ↔ (innerAut U A).IsAlmostHermitian :=
  by
  refine' ⟨fun h => h.of_innerAut _, _⟩
  rintro ⟨α, y, h, hy⟩
  rw [eq_comm, inner_aut_eq_iff] at h
  rw [h, SMulHomClass.map_smul]
  clear h
  revert α
  rw [← is_almost_hermitian_iff_smul]
  apply is_almost_hermitian.of_inner_aut
  exact hy.is_almost_hermitian

/-- we say a matrix $x$ _has almost equal spectra to_ another matrix $y$ if
  there exists some scalar $0\neq\beta \in \mathbb{C}$ such that $x$ and $\beta y$ have equal spectra -/
def IsAlmostHermitian.HasAlmostEqualSpectraTo {x y : Matrix n n 𝕜} (hx : x.IsAlmostHermitian)
    (hy : y.IsAlmostHermitian) : Prop :=
  ∃ β : 𝕜ˣ, hx.spectra = (hy.smul β).spectra

end Matrix

