import Monlib.LinearAlgebra.QuantumSet.Basic

section Pi
  variable {ι : Type*}
   {A : ι → Type*} [Fintype ι] [hA : Π i, starAlgebra (A i)]
   [Π i, QuantumSet (A i)]

  -- instance piStar :
  --     Ring (PiQ A) :=
  abbrev PiQ (A : ι → Type*) [Fintype ι] [Π i, starAlgebra (A i)]
   [Π i, QuantumSet (A i)]
    := PiLp 2 A

  @[default_instance] instance : Ring (PiQ A) := Pi.ring
  @[default_instance] instance : Algebra ℂ (PiQ A) := Pi.algebra _ _
  @[default_instance] instance : StarRing (PiQ A) := Pi.instStarRingForall
  @[default_instance] instance : StarModule ℂ (PiQ A) := Pi.instStarModuleForall

  lemma PiLp.mul_apply (x y : PiQ A) (i : ι) :
    (x * y) i = x i * y i := rfl

  def Pi.modAut (r : ℝ) :
    PiQ A ≃ₐ[ℂ] PiQ A :=
  AlgEquiv.Pi (λ i => (hA i).modAut r)

  lemma Pi.modAut_apply (r : ℝ) (x : PiQ A) (i : ι) :
    Pi.modAut r x i = (hA i).modAut r (x i) :=
  rfl
  -- lemma Pi.modAut_apply_modAut (r s : ℝ) :
  --   (Pi.modAut r).trans (Pi.modAut s) = Pi.modAut (r + s) :=
  -- by
  --   {}
  -- -- calc

  @[instance]
  def piStarAlgebra :
    starAlgebra (PiQ A) where
  modAut r := Pi.modAut r
  modAut_trans r s := by
    simp_rw [AlgEquiv.ext_iff]
    intro x
    apply PiLp.ext
    intro i
    simp_rw [AlgEquiv.trans_apply, Pi.modAut_apply,
      QuantumSet.modAut_apply_modAut, add_comm]
  modAut_star r x := by
    ext i
    simp only [Pi.modAut_apply, Pi.star_apply, star, starAlgebra.modAut_star]

  lemma piStarAlgebra.modAut (r : ℝ) (x : PiQ A) (i : ι) :
    piStarAlgebra.modAut r x i = (hA i).modAut r (x i) := rfl

  open scoped ComplexOrder

  -- attribute [-instance] pseudoMetricSpacePi
  @[instance]
  noncomputable def piInnerProductAlgebra :
    -- letI : starAlgebra (PiQ A) := piStarAlgebra
    InnerProductAlgebra (PiQ A) where
  -- toMetricSpace := (PiLp.normedAddCommGroup 2 A).toMetricSpace
  -- inner x y := ∑ i, ⟪x i, y i⟫_ℂ

  -- toMetricSpace := (PiLp.normedAddCommGroup 2 A).toMetricSpace
  toInner := (PiLp.innerProductSpace (𝕜 := ℂ) A).toInner
  -- toNorm :=  (PiLp.normedAddCommGroup 2 A).toNorm
  dist_eq _ _ := by
    simp [dist_eq_norm]
  --   -- congr
  -- dist_self _ := by
  --   simp only [dist_self]
  -- eq_of_dist_eq_zero := by
  --   simp only [dist_eq_zero, imp_self, implies_true]
  -- dist_comm x y := by
  --   simp only [dist_comm]
  -- dist_triangle x y z := by
  --   simp only [dist_triangle]
  -- edist x y :=
  --   (PiLp.normedAddCommGroup 2 A).edist x y
  -- edist_dist _ _ := by
  --   simp only [edist_dist, PseudoMetricSpace.edist]
  -- dist_smul_pair' r x y := by
  --   simp only [OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.two_ne_top, ENNReal.toReal_ofNat,
  --     Real.rpow_two, one_div, dist_zero_right, Complex.norm_eq_abs]
  --   simp_rw [dist_eq_norm]
  --   -- rw [← @smul_sub]
  --   calc
  --     (PiLp.normedAddCommGroup 2 A).norm (r • x - r • y)
  --     = (PiLp.normedAddCommGroup 2 A).norm (r • (x - y)) := ?_
  --     _ ≤ ‖r‖ * (PiLp.normedAddCommGroup 2 A).norm (x - y) := ?_
  --   rw [smul_sub]
  --   congr
  --   exact NormedSpace.norm_smul_le _ _
  -- dist_pair_smul' r s x := by
  --   simp only [OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.two_ne_top, ENNReal.toReal_ofNat,
  --     Real.rpow_two, one_div, dist_zero_right]
  --   simp_rw [dist_eq_norm]
  --   calc
  --     (PiLp.normedAddCommGroup 2 A).norm (r • x - s • x)
  --     = (PiLp.normedAddCommGroup 2 A).norm ((r - s) • x) := ?_
  --     _ ≤ ‖r - s‖ * (PiLp.normedAddCommGroup 2 A).norm x := ?_
  --   rw [sub_smul]
  --   congr
  --   exact NormedSpace.norm_smul_le _ _

    -- simp [edist_dist]
  norm_sq_eq_inner := λ x =>
    by simp [PiLp.norm_sq_eq_of_L2, inner_self_eq_norm_sq]
  conj_symm := λ _ _ => by simp only [map_sum, inner_conj_symm]
  add_left := λ _ _ _ => by simp only [Pi.add_apply, Finset.sum_add_distrib,
    inner_add_left]
  smul_left := λ _ _ _ => by simp only [Pi.smul_apply, inner_smul_left, Finset.mul_sum]

  open scoped InnerProductSpace

  theorem piInnerProductAlgebra.inner_apply (a b : PiQ A) :
    -- letI :=
    -- letI : NormedAddCommGroup (PiQ A) := piInnerProductAlgebra.toNormedAddCommGroup
    -- letI : InnerProductSpace ℂ (PiQ A) := piInnerProductAlgebra.toInnerProductSpace
    piInnerProductAlgebra.inner a b = ∑ i, ⟪a i, b i⟫_ℂ :=
  rfl

  noncomputable instance Pi.quantumSet [hA : Π i, QuantumSet (A i)] [gns:Fact (∀ i, (hA i).k = 0)] :
    QuantumSet (PiQ A) where
  modAut_isSymmetric r x y :=
  by simp_rw [piInnerProductAlgebra.inner_apply,
    piStarAlgebra.modAut,
    QuantumSet.modAut_isSymmetric]
  k := 0 --(λ i ↦ (hA i).k)
  inner_star_left x y z := by
    simp_rw [piInnerProductAlgebra.inner_apply,
      PiLp.mul_apply,
      piStarAlgebra.modAut, QuantumSet.inner_star_left,
      gns.out]
    rfl
  inner_conj_left x y z := by
    simp_rw [piInnerProductAlgebra.inner_apply,
      PiLp.mul_apply,
      QuantumSet.inner_conj_left,
      gns.out]
    rfl
  n := (Σ i, (hA i).n)
  n_isFintype := by infer_instance
  n_isDecidableEq := by exact Classical.typeDecidableEq ((i : ι) × n (A i))
  onb := Pi.orthonormalBasis (λ i => (hA i).onb)

end Pi
