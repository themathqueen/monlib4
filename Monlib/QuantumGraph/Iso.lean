/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Monlib.QuantumGraph.Basic
import Monlib.QuantumGraph.Example

#align_import quantum_graph.iso

/-!
 # Isomorphisms between quantum graphs

 This file defines isomorphisms between quantum graphs.
-/


open TensorProduct Matrix

open scoped TensorProduct BigOperators Kronecker Functional

variable {p n : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

local notation "⊗K" => Matrix (n × n) (n × n) ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

variable {φ : Module.Dual ℂ (Matrix n n ℂ)} {ψ : Module.Dual ℂ (Matrix p p ℂ)}

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ (Matrix n n ℂ)

local notation "η" => Algebra.linearMap ℂ (Matrix n n ℂ)

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ) :
    (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "υ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ)) :
    Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ)

local notation "ϰ" =>
  ((TensorProduct.comm ℂ (Matrix n n ℂ) ℂ) : Matrix n n ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "ϰ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.comm ℂ (Matrix n n ℂ) ℂ) : ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] ℂ)

local notation "τ" => (TensorProduct.lid ℂ (Matrix n n ℂ) : ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

local notation "τ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.lid ℂ (Matrix n n ℂ)) : Matrix n n ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

private theorem commutes_with_mul''_adjoint [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    {f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)} (hf : f φ.matrix = φ.matrix) :
    TensorProduct.map f.toLinearMap f.toLinearMap
      ∘ₗ Coalgebra.comul =
    Coalgebra.comul ∘ₗ f.toLinearMap :=
  by
  rw [Coalgebra.comul_eq_mul_adjoint, LinearMap.commutes_with_mul_adjoint_iff
    f.toLinearMap]
  -- rw [LinearMap.comp_assoc]
  have :=
    (List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 0
          1).mp
      hf
  simp_rw [this, StarAlgEquiv.toLinearMap_apply, _root_.map_mul, implies_true]

open scoped Matrix

theorem innerAut_adjoint_eq_iff [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    (U : unitaryGroup n ℂ) : LinearMap.adjoint (innerAut U) = innerAut (star U) ↔ Commute φ.matrix U :=
  by
  have hf : ∀ U : unitaryGroup n ℂ, innerAut U = (innerAutStarAlg U).toLinearMap :=
    fun _ => rfl
  have hh : ∀ U : unitaryGroup n ℂ, (innerAutStarAlg U).symm = innerAutStarAlg (star U) :=
    by
    intro V
    ext1
    simp_rw [innerAutStarAlg_symm_apply, innerAutStarAlg_apply, unitary.star_eq_inv,
      UnitaryGroup.inv_apply, star_star]
  have hf' : innerAut (star U) = (innerAutStarAlg U).symm.toLinearMap := by
    rw [hh, hf]
  have := List.TFAE.out
      (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ hφ _
        (innerAutStarAlg U))
      1 0
  rw [hf, hf', this,
    innerAutStarAlg_apply, unitaryGroup.injective_hMul U, Matrix.mul_assoc, ←
    unitaryGroup.star_coe_eq_coe_star, UnitaryGroup.star_mul_self, Matrix.mul_one]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem Qam.mul'_adjoint_commutes_with_innerAut_lm [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    {x : Matrix.unitaryGroup n ℂ} (hx : Commute φ.matrix x) :
    TensorProduct.map (innerAut x) (innerAut x) ∘ₗ Coalgebra.comul = Coalgebra.comul ∘ₗ innerAut x :=
by
  rw [innerAut]
  apply commutes_with_mul''_adjoint
  rw [innerAutStarAlg_apply, ← hx, mul_assoc, ← unitaryGroup.star_coe_eq_coe_star,
    UnitaryGroup.mul_star_self, mul_one]

theorem Qam.unit_commutes_with_innerAut_lm (U : Matrix.unitaryGroup n ℂ) :
  innerAut U ∘ₗ η = η := by
  rw [commutes_with_unit_iff, innerAut_apply_one]

theorem Qam.mul'_commutes_with_innerAut_lm (x : Matrix.unitaryGroup n ℂ) :
    m ∘ₗ ((innerAut x) ⊗ₘ (innerAut x)) = innerAut x ∘ₗ m :=
by simp_rw [commutes_with_mul'_iff, innerAut.map_mul, forall₂_true_iff]

theorem Qam.unit_adjoint_commutes_with_innerAut_lm [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.matrix U) :
  Coalgebra.counit ∘ₗ innerAut U = Coalgebra.counit :=
  by
  rw [← innerAut_adjoint_eq_iff] at hU
  apply_fun LinearMap.adjoint using LinearMap.adjoint.injective
  rw [LinearMap.adjoint_comp, Coalgebra.counit_eq_unit_adjoint, LinearMap.adjoint_adjoint, hU]
  ext1
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
  one_smul, innerAut, StarAlgEquiv.toLinearMap_apply, _root_.map_one]

local notation "f_{" x "}" => innerAut x

theorem innerAutIsReal (U : unitaryGroup n ℂ) : LinearMap.IsReal (innerAut U) := fun _ =>
  (innerAut.map_star _ _).symm

-- def StarAlgEquiv.IsIsometry [hφ : φ.IsFaithfulPosMap] (f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)) : Prop :=
  -- ∀ x, ‖f x‖ = ‖x‖
@[reducible]
alias StarAlgEquiv.IsIsometry := Isometry

theorem Module.Dual.IsFaithfulPosMap.inner_coord' [hφ : φ.IsFaithfulPosMap] (ij : n × n)
    (x : ℍ) : ⟪hφ.basis ij, x⟫_ℂ = (x * hφ.matrixIsPosDef.rpow (1 / 2)) ij.1 ij.2 := by
  rw [IsFaithfulPosMap.basis_apply, ← IsFaithfulPosMap.orthonormalBasis_apply,
    IsFaithfulPosMap.inner_coord _ ij x]

theorem InnerAut.toMatrix [hφ : φ.IsFaithfulPosMap] (U : unitaryGroup n ℂ) :
    hφ.toMatrix (innerAut U) = U ⊗ₖ (modAut (-(1 / 2)) U)ᴴᵀ :=
  by
  ext
  simp only [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply,
    StarAlgEquiv.toLinearMap_apply,
    modAut, innerAutStarAlg_apply,
    Module.Dual.IsFaithfulPosMap.inner_coord', Module.Dual.IsFaithfulPosMap.basis_repr_apply,
    Module.Dual.IsFaithfulPosMap.inner_coord']
  simp only [innerAutStarAlg_apply, mul_apply, stdBasisMatrix, mul_ite, ite_mul,
    MulZeroClass.mul_zero, MulZeroClass.zero_mul, mul_one, one_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_const_zero, Finset.mem_univ, if_true, ite_and,
    kroneckerMap, of_apply, conj_apply, sig_apply, star_sum,
    star_mul', neg_neg, Finset.mul_sum, Finset.sum_mul, mul_assoc, innerAut_apply',
    Module.Dual.IsFaithfulPosMap.basis_apply]
  simp_rw [← star_apply, star_eq_conjTranspose, (PosDef.rpow.isHermitian _ _).eq]
  -- rw [Finset.sum_comm]
  repeat' apply Finset.sum_congr rfl; intros
  simp_rw [← star_eq_conjTranspose, ← unitaryGroup.star_coe_eq_coe_star]
  congr 1
  nth_rw 1 [mul_rotate', ← mul_assoc]
  rw [mul_comm _ (PosDef.rpow _ (1 / 2) _ _), mul_assoc]

theorem unitary_commutes_with_hφ_matrix_iff_isIsometry (hφ : φ.IsFaithfulPosMap) [Nontrivial n]
    (U : unitaryGroup n ℂ) :
    Commute φ.matrix U ↔ StarAlgEquiv.IsIsometry (innerAutStarAlg U) := by
  rw [← innerAut_adjoint_eq_iff, ← innerAutStarAlg_equiv_toLinearMap, ← innerAut_inv_eq_star,
    ← innerAutStarAlg_equiv_symm_toLinearMap]
  have := List.TFAE.out
      (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _
        (innerAutStarAlg U))
      1 4
  rw [this, StarAlgEquiv.IsIsometry, iff_comm]
  exact isometry_iff_norm _

theorem Qam.symm_apply_starAlgEquiv_conj [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    {f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)} (hf : StarAlgEquiv.IsIsometry f) (A : l((Matrix n n ℂ))) :
    symmMap ℂ (Matrix n n ℂ) _ (f.toLinearMap ∘ₗ A ∘ₗ f.symm.toLinearMap) =
      f.toLinearMap ∘ₗ (symmMap ℂ (Matrix n n ℂ) _ A) ∘ₗ f.symm.toLinearMap :=
  by
  have := List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 4 1
  rw [StarAlgEquiv.IsIsometry, isometry_iff_norm, this] at hf
  simp_rw [symmMap_apply, LinearMap.real_starAlgEquiv_conj, LinearMap.adjoint_comp, hf]
  nth_rw 1 [← hf]
  simp only [LinearMap.adjoint_adjoint, LinearMap.comp_assoc]

theorem InnerAut.symmetric_eq [hφ : φ.IsFaithfulPosMap] [Nontrivial n] (A : l((Matrix n n ℂ)))
    {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.matrix U) :
    symmMap ℂ (Matrix n n ℂ) _ (f_{U} ∘ₗ A ∘ₗ f_{star U}) =
      f_{U} ∘ₗ symmMap ℂ (Matrix n n ℂ) _ A ∘ₗ f_{star U} :=
  by
  rw [← innerAut_inv_eq_star, ← innerAutStarAlg_equiv_symm_toLinearMap, ←
    innerAutStarAlg_equiv_toLinearMap]
  exact
    Qam.symm_apply_starAlgEquiv_conj ((unitary_commutes_with_hφ_matrix_iff_isIsometry hφ U).mp hU) _

theorem StarAlgEquiv.commutes_with_mul' (f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)) :
    (LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ f.toLinearMap ⊗ₘ f.toLinearMap) =
      f.toLinearMap ∘ₗ LinearMap.mul' ℂ (Matrix n n ℂ) :=
  by
  rw [commutes_with_mul'_iff]
  intro x y
  simp only [StarAlgEquiv.toLinearMap_apply, _root_.map_mul]

theorem StarAlgEquiv.IsIsometry.commutes_with_mul'_adjoint
  [hφ : φ.IsFaithfulPosMap] [Nontrivial n] {f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)}
    (hf : StarAlgEquiv.IsIsometry f) :
    (f.toLinearMap ⊗ₘ f.toLinearMap) ∘ₗ LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ)) =
      LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ)) ∘ₗ f.toLinearMap :=
  by
  have := List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 4 1
  rw [StarAlgEquiv.IsIsometry, isometry_iff_norm, this] at hf
  rw [← LinearMap.adjoint_adjoint (f.toLinearMap ⊗ₘ f.toLinearMap), ←
    LinearMap.adjoint_comp, TensorProduct.map_adjoint, hf, f.symm.commutes_with_mul',
    LinearMap.adjoint_comp, ← hf, LinearMap.adjoint_adjoint]

theorem Qam.reflIdempotent_starAlgEquiv_conj [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    {f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)} (hf : StarAlgEquiv.IsIsometry f) (A B : l((Matrix n n ℂ))) :
    (f.toLinearMap ∘ₗ A ∘ₗ f.symm.toLinearMap) •ₛ (f.toLinearMap ∘ₗ B ∘ₗ f.symm.toLinearMap) =
      f.toLinearMap ∘ₗ (A •ₛ B) ∘ₗ f.symm.toLinearMap :=
  by
  simp only [schurMul_apply_apply, TensorProduct.map_comp, ←
    LinearMap.comp_assoc, f.commutes_with_mul']
  have : StarAlgEquiv.IsIsometry f.symm :=
    by
    simp_rw [StarAlgEquiv.IsIsometry, isometry_iff_norm] at hf ⊢
    have := List.TFAE.out
        (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f.symm) 4 1
    rw [this]
    have this' := List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 4 1
    rw [this'] at hf
    rw [StarAlgEquiv.symm_symm, ← hf, LinearMap.adjoint_adjoint]
  simp only [LinearMap.comp_assoc, Coalgebra.comul_eq_mul_adjoint,
    this.commutes_with_mul'_adjoint, hf.commutes_with_mul'_adjoint]


theorem InnerAut.reflIdempotent [hφ : φ.IsFaithfulPosMap]
  [Nontrivial n] {U : unitaryGroup n ℂ} (hU : Commute φ.matrix U)
    (A B : l((Matrix n n ℂ))) :
    (f_{U} ∘ₗ A ∘ₗ f_{star U}) •ₛ (f_{U} ∘ₗ B ∘ₗ f_{star U}) =
      f_{U} ∘ₗ (A •ₛ B) ∘ₗ f_{star U} :=
  by
  rw [← innerAut_inv_eq_star, ← innerAutStarAlg_equiv_symm_toLinearMap, ←
    innerAutStarAlg_equiv_toLinearMap]
  rw [unitary_commutes_with_hφ_matrix_iff_isIsometry hφ U] at hU
  exact Qam.reflIdempotent_starAlgEquiv_conj hU _ _

def Qam.Iso (A B : l((Matrix n n ℂ))) : Prop :=
  ∃ f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ),
    A ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ B ∧ f φ.matrix = φ.matrix

-- structure QamIso [hφ : φ.IsFaithfulPosMap] {A B : l((Matrix n n ℂ))} (hA : Qam φ A) (hB : Qam φ B) extends
--     StarAlgEquiv ℂ (Matrix n n ℂ) (Matrix n n ℂ) where
--   IsHom :=
--     A ∘ₗ toStarAlgEquiv.toLinearMap = toStarAlgEquiv.toLinearMap ∘ₗ B
--   is_iso := toFun φ.matrix = φ.matrix

-- -- TODO:
-- def qam.lm.reflexive.iso {A B : l((Matrix n n ℂ))} (hA : qam_lm_is_reflexive A)
--   (hB : qam_lm_is_reflexive B) :
--   Prop :=
-- ∃ f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ), A ∘ f = f ∘ B
-- def qam.lm.unreflexive.iso {A B : l((Matrix n n ℂ))} (hA : qam_lm_is_unreflexive A)
--   (hB : qam_lm_is_unreflexive B) : Prop :=
-- ∃ f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ), A ∘ f = f ∘ B
theorem Qam.iso_iff [hφ : φ.IsFaithfulPosMap] {A B : l((Matrix n n ℂ))} [Nontrivial n] :
    @Qam.Iso n _ _ φ A B ↔
      ∃ U : unitaryGroup n ℂ, A ∘ₗ innerAut U = innerAut U ∘ₗ B ∧ Commute φ.matrix U :=
  by
  simp_rw [← innerAut_adjoint_eq_iff]
  have hf : ∀ U : unitaryGroup n ℂ, f_{U} = (innerAutStarAlg U).toLinearMap :=
    fun _ => rfl
  have hh : ∀ U : unitaryGroup n ℂ, (innerAutStarAlg U).symm = innerAutStarAlg (star U) :=
    by
    intro V
    ext1
    simp_rw [innerAutStarAlg_symm_apply, innerAutStarAlg_apply, unitary.star_eq_inv,
      UnitaryGroup.inv_apply, star_star]
  have := fun U =>
    List.TFAE.out
      (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _
        (innerAutStarAlg U))
      1 0
  simp_rw [hf, ← hh, this]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨U, rfl⟩ := StarAlgEquiv.of_matrix_is_inner f
    exact ⟨U, hf⟩
  · rintro ⟨U, hU⟩
    exact ⟨innerAutStarAlg U, hU⟩

theorem Qam.iso_preserves_spectrum (A B : l((Matrix n n ℂ))) (h : @Qam.Iso n _ _ φ A B) :
    spectrum ℂ A = spectrum ℂ B := by
  obtain ⟨f, ⟨hf, _⟩⟩ := h
  let f' := f.toLinearMap
  let f'' := f.symm.toLinearMap
  have hh' : f'' ∘ₗ f' = LinearMap.id :=
    by
    rw [LinearMap.ext_iff]
    intro x
    simp_rw [LinearMap.comp_apply, f', f'', StarAlgEquiv.toLinearMap_apply,
      StarAlgEquiv.symm_apply_apply, LinearMap.id_apply]
  have : B = f'' ∘ₗ A ∘ₗ f' := by rw [hf, ← LinearMap.comp_assoc, hh', LinearMap.id_comp]
  rw [this, ← spectrum.comm, LinearMap.comp_assoc, LinearMap.comp_eq_id_comm.mp hh',
    LinearMap.comp_id]

-- MOVE:
theorem innerAut_lm_rankOne [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.matrix U) (x y : (Matrix n n ℂ)) :
    f_{U} ∘ₗ (|x⟩⟨y| : l((Matrix n n ℂ))) ∘ₗ f_{star U} = |f_{U} x⟩⟨f_{U} y| :=
  by
  rw [← innerAut_adjoint_eq_iff] at hU
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    _root_.map_smul, ← hU, LinearMap.adjoint_inner_right, forall_true_iff]

local notation "e_{" x "," y "}" => Matrix.stdBasisMatrix x y (1 : ℂ)

--MOVE:
theorem innerAut_lm_basis_apply (U : Matrix.unitaryGroup n ℂ) (i j k l : n) :
    (f_{U} e_{i,j}) k l = (U ⊗ₖ star U) (k, j) (i, l) :=
  by
  simp_rw [Matrix.innerAut_apply, Matrix.mul_apply, Matrix.UnitaryGroup.inv_apply,
    Matrix.stdBasisMatrix, mul_boole, Finset.sum_mul, ite_mul, MulZeroClass.zero_mul, ite_and,
    Matrix.kroneckerMap, Matrix.of_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem Qam.rankOne_toMatrix_of_star_algEquiv_coord [hφ : φ.IsFaithfulPosMap]
  (x y : Matrix n n ℂ) (i j k l : n) :
  hφ.toMatrix |x⟩⟨y| (i, j) (k, l) =
    ((x * hφ.matrixIsPosDef.rpow (1 / 2)) ⊗ₖ (y * hφ.matrixIsPosDef.rpow (1 / 2))ᴴᵀ)
      (i, k) (j, l) :=
by
  simp_rw [rankOne_toMatrix, conjTranspose_col, mul_apply, col_apply, row_apply, Pi.star_apply,
    reshape_apply, kronecker_apply, conj_apply]
  simp only [Fintype.univ_punit, Finset.sum_const, Finset.card_singleton, nsmul_eq_mul,
    Nat.cast_one, one_mul]
