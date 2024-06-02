import Monlib.LinearAlgebra.MyMatrix.Basic
import Monlib.LinearAlgebra.InnerAut

#align_import linear_algebra.my_matrix.spectra

instance multisetCoe {α β : Type _} [Coe α β] : Coe (Multiset α) (Multiset β)
    where coe s := s.map (Coe.coe : α → β)

instance multisetCoeTC {α β : Type _} [CoeTC α β] : CoeTC (Multiset α) (Multiset β)
    where coe s := s.map (CoeTC.coe : α → β)

theorem Finset.val.map_coe {α β γ : Type _} (f : α → β) (s : Finset α) [CoeTC β γ] :
    ((s.val.map f : Multiset β) : Multiset γ) = s.val.map ↑f :=
  by
  simp only [Multiset.map_map, Function.comp_apply, AddMonoidHom.toFun_eq_coe]
theorem Finset.val.map_coe' {α β γ : Type _} (f : α → β) (s : Finset α) [Coe β γ] :
    ((s.val.map f : Multiset β) : Multiset γ) = s.val.map ↑f :=
Finset.val.map_coe f s

noncomputable instance multisetCoeTC_RToRCLike {𝕜 : Type _} [RCLike 𝕜] :
  CoeTC (Multiset ℝ) (Multiset 𝕜) :=
@multisetCoeTC ℝ 𝕜 ⟨RCLike.ofReal⟩
noncomputable instance multisetCoeRToRCLike {𝕜 : Type _} [RCLike 𝕜] :
  Coe (Multiset ℝ) (Multiset 𝕜) where
  coe := (@multisetCoeTC_RToRCLike 𝕜 _).coe

namespace Matrix

variable {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n] [DecidableEq 𝕜]

open scoped Matrix

noncomputable def IsAlmostHermitian.scalar {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : 𝕜 := by choose α _ using hx; exact α

noncomputable def IsAlmostHermitian.matrix {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : Matrix n n 𝕜 := by
  choose y _ using IsAlmostHermitian.scalar.proof_1 hx; exact y

theorem IsAlmostHermitian.eq_smul_matrix {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : x = hx.scalar • hx.matrix :=
  (IsAlmostHermitian.matrix.proof_1 hx).1.symm

theorem IsAlmostHermitian.matrix_isHermitian {n : Type _} {x : Matrix n n 𝕜}
    (hx : x.IsAlmostHermitian) : hx.matrix.IsHermitian :=
  (IsAlmostHermitian.matrix.proof_1 hx).2

noncomputable def IsAlmostHermitian.eigenvalues {x : Matrix n n 𝕜} (hx : x.IsAlmostHermitian) :
    n → 𝕜 :=
fun i => hx.scalar • hx.matrix_isHermitian.eigenvalues i

noncomputable def IsAlmostHermitian.spectra {A : Matrix n n 𝕜} (hA : A.IsAlmostHermitian) :
    Multiset 𝕜 :=
  Finset.univ.val.map fun i => hA.eigenvalues i

noncomputable def IsHermitian.spectra {A : Matrix n n 𝕜} (hA : A.IsHermitian) : Multiset ℝ :=
  Finset.univ.val.map fun i => hA.eigenvalues i

theorem IsHermitian.spectra_coe {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (hA.spectra : Multiset 𝕜) = Finset.univ.val.map fun i => hA.eigenvalues i :=
  by
  simp only [Multiset.map_map, IsHermitian.spectra]

open scoped BigOperators

theorem IsHermitian.mem_coe_spectra_diagonal {A : n → 𝕜} (hA : (diagonal A).IsHermitian) (x : 𝕜) :
    x ∈ (hA.spectra : Multiset 𝕜) ↔ ∃ i : n, A i = x :=
  by
  simp_rw [IsHermitian.spectra_coe, Multiset.mem_map,
    Finset.mem_univ_val, true_and_iff, exists_exists_eq_and]
  have :
    ((x : 𝕜) ∈ {b : 𝕜 | ∃ a, ↑(hA.eigenvalues a) = b} ↔ (x : 𝕜) ∈ {b : 𝕜 | ∃ a, A a = b}) ↔
      ((∃ a, (hA.eigenvalues a : 𝕜) = x) ↔ ∃ a, A a = x) :=
    by simp_rw [Set.mem_setOf]
  rw [← this]
  clear this
  revert x
  rw [← Set.ext_iff, ← IsHermitian.spectrum, diagonal.spectrum]

theorem IsHermitian.spectra_set_eq_spectrum {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    {x : 𝕜 | x ∈ (hA.spectra : Multiset 𝕜)} = _root_.spectrum 𝕜 (toLin' A) :=
  by
  ext
  simp_rw [IsHermitian.spectra_coe, hA.spectrum, Set.mem_setOf, Multiset.mem_map,
    Finset.mem_univ_val, true_and_iff, exists_exists_eq_and]

theorem IsHermitian.of_innerAut {A : Matrix n n 𝕜} (hA : A.IsHermitian) (U : unitaryGroup n 𝕜) :
    (innerAut U A).IsHermitian :=
  (innerAut_isHermitian_iff U A).mp hA

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
  refine' ⟨α, innerAut U y, _, hy.of_innerAut _⟩
  simp_rw [_root_.map_smul]

theorem isAlmostHermitian_iff_of_innerAut {A : Matrix n n 𝕜} (U : unitaryGroup n 𝕜) :
    A.IsAlmostHermitian ↔ (innerAut U A).IsAlmostHermitian :=
  by
  refine' ⟨fun h => h.of_innerAut _, _⟩
  rintro ⟨α, y, h, hy⟩
  rw [eq_comm, innerAut_eq_iff] at h
  rw [h, _root_.map_smul]
  clear h
  revert α
  rw [← isAlmostHermitian_iff_smul]
  apply IsAlmostHermitian.of_innerAut
  exact hy.isAlmostHermitian

/-- we say a matrix $x$ _has almost equal spectra to_ another matrix $y$ if
  there exists some scalar $0\neq\beta \in \mathbb{C}$ such that $x$ and $\beta y$ have equal spectra -/
def IsAlmostHermitian.HasAlmostEqualSpectraTo {x y : Matrix n n 𝕜} (hx : x.IsAlmostHermitian)
    (hy : y.IsAlmostHermitian) : Prop :=
  ∃ β : 𝕜ˣ, hx.spectra = (hy.smul β).spectra

end Matrix
