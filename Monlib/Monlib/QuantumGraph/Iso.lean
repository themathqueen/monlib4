/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import QuantumGraph.Example

#align_import quantum_graph.iso

/-!
 # Isomorphisms between quantum graphs

 This file defines isomorphisms between quantum graphs.
-/


open TensorProduct Matrix

open scoped TensorProduct BigOperators Kronecker Functional

variable {p n : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

local notation "ℍ" => Matrix n n ℂ

local notation "⊗K" => Matrix (n × n) (n × n) ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

variable {φ : Module.Dual ℂ ℍ} [hφ : Fact φ.IsFaithfulPosMap] {ψ : Module.Dual ℂ (Matrix p p ℂ)}
  (hψ : ψ.IsFaithfulPosMap)

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ) :
    (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "υ⁻¹" =>
  ((TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ)).symm :
    Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ)

local notation "ϰ" =>
  (↑(TensorProduct.comm ℂ (Matrix n n ℂ) ℂ) : Matrix n n ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "ϰ⁻¹" =>
  ((TensorProduct.comm ℂ (Matrix n n ℂ) ℂ).symm : ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] ℂ)

local notation "τ" => (TensorProduct.lid ℂ (Matrix n n ℂ) : ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

local notation "τ⁻¹" =>
  ((TensorProduct.lid ℂ (Matrix n n ℂ)).symm : Matrix n n ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)

local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

private theorem commutes_with_mul''_adjoint [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : f φ.Matrix = φ.Matrix) :
    TensorProduct.map (f.toAlgEquiv.toLinearMap : ℍ →ₗ[ℂ] ℍ)
          (f.toAlgEquiv.toLinearMap : ℍ →ₗ[ℂ] ℍ) ∘ₗ
        (m.adjoint : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) =
      (m.adjoint : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) ∘ₗ f.toAlgEquiv.toLinearMap :=
  by
  simp_rw [LinearMap.comp_assoc]
  nth_rw_rhs 1 [←
    LinearMap.adjoint_adjoint ((m.adjoint : ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ) ∘ₗ f.to_alg_equiv.to_linear_map)]
  have :=
    (List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 0
          1).mp
      hf
  have this' :
    ∀ x y,
      f.symm.to_alg_equiv.to_linear_map (x * y) =
        f.symm.to_alg_equiv.to_linear_map x * f.symm.to_alg_equiv.to_linear_map y :=
    fun x y => by simp_rw [AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv, _root_.map_mul]
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, this, ←
    (commutes_with_mul'_iff _).mpr this', LinearMap.adjoint_comp, map_adjoint, ← this,
    LinearMap.adjoint_adjoint]

open scoped Matrix

theorem innerAut_adjoint_eq_iff [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    (U : unitaryGroup n ℂ) : (innerAut U).adjoint = innerAut (star U) ↔ Commute φ.Matrix U :=
  by
  have hf : ∀ U : unitary_group n ℂ, inner_aut U = (inner_aut_star_alg U).toAlgEquiv.toLinearMap :=
    fun _ => rfl
  have hh : ∀ U : unitary_group n ℂ, (inner_aut_star_alg U).symm = inner_aut_star_alg (star U) :=
    by
    intro V
    ext1
    simp_rw [inner_aut_star_alg_symm_apply, inner_aut_star_alg_apply, unitary.star_eq_inv,
      unitary_group.inv_apply, star_star]
  have hf' : inner_aut (star U) = (inner_aut_star_alg U).symm.toAlgEquiv.toLinearMap := by
    rw [hh, hf]
  rw [hf, hf',
    List.TFAE.out
      (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _
        (inner_aut_star_alg U))
      1 0,
    inner_aut_star_alg_apply, unitary_group.injective_mul U, Matrix.mul_assoc, ←
    unitary_group.star_coe_eq_coe_star, unitary_group.star_mul_self, Matrix.mul_one]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem Qam.mul'_adjoint_commutes_with_innerAut_lm [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    {x : Matrix.unitaryGroup n ℂ} (hx : Commute φ.Matrix x) :
    TensorProduct.map (innerAut x) (innerAut x) ∘ₗ m.adjoint = m.adjoint ∘ₗ innerAut x :=
  by
  simp_rw [Commute, SemiconjBy, mul_eq_mul] at hx
  rw [unitary_group.injective_mul x⁻¹] at hx
  simp_rw [unitary_group.inv_apply, Matrix.mul_assoc, unitary_group.mul_star_self, Matrix.mul_one, ←
    Matrix.mul_assoc, unitary_group.star_coe_eq_coe_star, ← inner_aut_apply',
    @eq_comm _ _ ((inner_aut x) _)] at hx
  have hf : ∀ U : unitary_group n ℂ, inner_aut U = (inner_aut_star_alg U).toAlgEquiv.toLinearMap :=
    fun _ => rfl
  have hh : ∀ U : unitary_group n ℂ, (inner_aut_star_alg U).symm = inner_aut_star_alg (star U) :=
    by
    intro V
    ext1
    simp_rw [inner_aut_star_alg_symm_apply, inner_aut_star_alg_apply, unitary.star_eq_inv,
      unitary_group.inv_apply, star_star]
  have hf' : inner_aut (star x) = (inner_aut_star_alg x).symm.toAlgEquiv.toLinearMap := by
    rw [hh, hf]
  simp_rw [hf', hf] at *
  rw [commutes_with_mul''_adjoint hx]

theorem Qam.unit_commutes_with_innerAut_lm (U : Matrix.unitaryGroup n ℂ) : innerAut U ∘ₗ η = η := by
  rw [commutes_with_unit_iff, inner_aut_apply_one]

theorem Qam.mul'_commutes_with_innerAut_lm (x : Matrix.unitaryGroup n ℂ) :
    m ∘ₗ (TensorProduct.map (innerAut x) (innerAut x) : l(ℍ ⊗[ℂ] ℍ)) =
      innerAut x ∘ₗ (m : ℍ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ) :=
  by
  simp_rw [commutes_with_mul'_iff, mul_eq_mul, inner_aut.map_mul, eq_self_iff_true,
    forall₂_true_iff]

theorem Qam.unit_adjoint_commutes_with_innerAut_lm [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.Matrix U) : η.adjoint ∘ₗ innerAut U = η.adjoint :=
  by
  rw [← innerAut_adjoint_eq_iff] at hU
  apply_fun LinearMap.adjoint using linear_map.adjoint.injective
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, hU, Qam.unit_commutes_with_innerAut_lm]

local notation "f_{" x "}" => innerAut x

theorem innerAutIsReal (U : unitaryGroup n ℂ) : (innerAut U).IsReal := fun x =>
  (innerAut.map_star _ _).symm

def StarAlgEquiv.IsIsometry [hφ : Fact φ.IsFaithfulPosMap] (f : ℍ ≃⋆ₐ[ℂ] ℍ) : Prop :=
  ∀ x, ‖f x‖ = ‖x‖

theorem InnerAut.toMatrix [hφ : Fact φ.IsFaithfulPosMap] (U : unitaryGroup n ℂ) :
    hφ.elim.toMatrix (innerAut U) = U ⊗ₖ (hφ.elim.sig (-(1 / 2)) U)ᴴᵀ :=
  by
  ext1
  simp only [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply,
    AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv,
    Module.Dual.IsFaithfulPosMap.inner_coord', Module.Dual.IsFaithfulPosMap.basis_repr_apply,
    Module.Dual.IsFaithfulPosMap.inner_coord']
  simp only [inner_aut_star_alg_apply, mul_apply, std_basis_matrix, mul_ite, ite_mul,
    MulZeroClass.mul_zero, MulZeroClass.zero_mul, mul_one, one_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_const_zero, Finset.mem_univ, if_true, ite_and,
    kronecker_map, of_apply, conj_apply, Module.Dual.IsFaithfulPosMap.sig_apply, star_sum,
    star_mul', neg_neg, Finset.mul_sum, Finset.sum_mul, mul_assoc, inner_aut_apply',
    Module.Dual.IsFaithfulPosMap.basis_apply]
  simp_rw [← star_apply, star_eq_conj_transpose, (pos_def.rpow.is_hermitian _ _).Eq]
  rw [Finset.sum_comm]
  repeat' apply Finset.sum_congr rfl; intros
  simp_rw [← star_eq_conj_transpose, ← unitary_group.star_coe_eq_coe_star]
  ring_nf

theorem unitary_commutes_with_hφ_matrix_iff_isIsometry [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    (U : unitaryGroup n ℂ) :
    Commute φ.Matrix U ↔ @StarAlgEquiv.IsIsometry n _ _ φ _ (innerAutStarAlg U) := by
  rw [← innerAut_adjoint_eq_iff, ← inner_aut_star_alg_equiv_to_linear_map, ← inner_aut_inv_eq_star,
    ← inner_aut_star_alg_equiv_symm_to_linear_map,
    List.TFAE.out
      (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _
        (inner_aut_star_alg U))
      1 4,
    StarAlgEquiv.IsIsometry]

theorem Qam.symm_apply_starAlgEquiv_conj [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @StarAlgEquiv.IsIsometry n _ _ φ _ f) (A : l(ℍ)) :
    LinearEquiv.symmMap ℂ ℍ (f.toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ f.symm.toAlgEquiv.toLinearMap) =
      f.toAlgEquiv.toLinearMap ∘ₗ LinearEquiv.symmMap ℂ ℍ A ∘ₗ f.symm.toAlgEquiv.toLinearMap :=
  by
  rw [StarAlgEquiv.IsIsometry,
    List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 4
      1] at
    hf
  simp only [LinearEquiv.symmMap_apply, LinearMap.adjoint_comp, ←
    AlgEquiv.toLinearEquiv_toLinearMap, LinearMap.real_starAlgEquiv_conj]
  simp_rw [AlgEquiv.toLinearEquiv_toLinearMap, hf]
  nth_rw 1 [← hf]
  simp only [LinearMap.adjoint_adjoint, LinearMap.comp_assoc]

theorem InnerAut.symmetric_eq [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n] (A : l(ℍ))
    {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.Matrix U) :
    LinearEquiv.symmMap ℂ ℍ (f_{U} ∘ₗ A ∘ₗ f_{star U}) =
      f_{U} ∘ₗ LinearEquiv.symmMap ℂ ℍ A ∘ₗ f_{star U} :=
  by
  rw [← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map, ←
    inner_aut_star_alg_equiv_to_linear_map]
  exact
    Qam.symm_apply_starAlgEquiv_conj ((unitary_commutes_with_hφ_matrix_iff_isIsometry U).mp hU) _

theorem StarAlgEquiv.commutes_with_mul' (f : ℍ ≃⋆ₐ[ℂ] ℍ) :
    (LinearMap.mul' ℂ ℍ ∘ₗ f.toAlgEquiv.toLinearMap ⊗ₘ f.toAlgEquiv.toLinearMap) =
      f.toAlgEquiv.toLinearMap ∘ₗ LinearMap.mul' ℂ ℍ :=
  by
  rw [commutes_with_mul'_iff]
  intro x y
  simp only [AlgEquiv.toLinearMap_apply, _root_.map_mul]

theorem StarAlgEquiv.IsIsometry.commutes_with_mul'_adjoint [Nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ}
    (hf : @StarAlgEquiv.IsIsometry n _ _ φ hφ f) :
    (f.toAlgEquiv.toLinearMap ⊗ₘ f.toAlgEquiv.toLinearMap) ∘ₗ (LinearMap.mul' ℂ ℍ).adjoint =
      (LinearMap.mul' ℂ ℍ).adjoint ∘ₗ f.toAlgEquiv.toLinearMap :=
  by
  rw [StarAlgEquiv.IsIsometry,
    List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 4
      1] at
    hf
  rw [← LinearMap.adjoint_adjoint (f.to_alg_equiv.to_linear_map ⊗ₘ f.to_alg_equiv.to_linear_map), ←
    LinearMap.adjoint_comp, TensorProduct.map_adjoint, hf, f.symm.commutes_with_mul',
    LinearMap.adjoint_comp, ← hf, LinearMap.adjoint_adjoint]

theorem Qam.reflIdempotent_starAlgEquiv_conj [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    {f : ℍ ≃⋆ₐ[ℂ] ℍ} (hf : @StarAlgEquiv.IsIsometry n _ _ φ _ f) (A B : l(ℍ)) :
    Qam.reflIdempotent hφ.elim (f.toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ f.symm.toAlgEquiv.toLinearMap)
        (f.toAlgEquiv.toLinearMap ∘ₗ B ∘ₗ f.symm.toAlgEquiv.toLinearMap) =
      f.toAlgEquiv.toLinearMap ∘ₗ Qam.reflIdempotent hφ.elim A B ∘ₗ f.symm.toAlgEquiv.toLinearMap :=
  by
  simp only [Qam.reflIdempotent, schurIdempotent, LinearMap.coe_mk, TensorProduct.map_comp, ←
    LinearMap.comp_assoc, f.commutes_with_mul']
  have : f.symm.is_isometry :=
    by
    simp_rw [StarAlgEquiv.IsIsometry] at hf ⊢
    rw [List.TFAE.out
        (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f.symm) 4 1]
    rw [List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 4
        1] at
      hf
    rw [StarAlgEquiv.symm_symm, ← hf, LinearMap.adjoint_adjoint]
  simp only [LinearMap.comp_assoc, this.commutes_with_mul'_adjoint]

theorem InnerAut.reflIdempotent [Nontrivial n] {U : unitaryGroup n ℂ} (hU : Commute φ.Matrix U)
    (A B : l(ℍ)) :
    Qam.reflIdempotent hφ.elim (f_{U} ∘ₗ A ∘ₗ f_{star U}) (f_{U} ∘ₗ B ∘ₗ f_{star U}) =
      f_{U} ∘ₗ Qam.reflIdempotent hφ.elim A B ∘ₗ f_{star U} :=
  by
  rw [← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map, ←
    inner_aut_star_alg_equiv_to_linear_map]
  exact
    Qam.reflIdempotent_starAlgEquiv_conj ((unitary_commutes_with_hφ_matrix_iff_isIsometry U).mp hU)
      _ _

theorem qam_starAlgEquiv_conj_iff [Nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ}
    (hf : @StarAlgEquiv.IsIsometry n _ _ φ hφ f) (A : l(ℍ)) :
    Qam φ (f.toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ f.symm.toAlgEquiv.toLinearMap) ↔ Qam φ A := by
  simp_rw [Qam, Qam.reflIdempotent_starAlgEquiv_conj hf, AlgEquiv.comp_inj, AlgEquiv.inj_comp]

theorem qam_symm_starAlgEquiv_conj_iff [Nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ}
    (hf : @StarAlgEquiv.IsIsometry n _ _ φ hφ f) (A : l(ℍ)) :
    @Qam.IsSymm n _ _ φ _ (f.toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ f.symm.toAlgEquiv.toLinearMap) ↔
      @Qam.IsSymm n _ _ φ _ A :=
  by
  simp only [Qam.IsSymm, Qam.symm_apply_starAlgEquiv_conj hf, AlgEquiv.comp_inj, AlgEquiv.inj_comp]

theorem qam_isSelfAdjoint_starAlgEquiv_conj_iff [Nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ}
    (hf : @StarAlgEquiv.IsIsometry n _ _ φ hφ f) (A : l(ℍ)) :
    IsSelfAdjoint (f.toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ f.symm.toAlgEquiv.toLinearMap) ↔
      IsSelfAdjoint A :=
  by
  simp only [LinearMap.isSelfAdjoint_iff', LinearMap.adjoint_comp]
  rw [StarAlgEquiv.IsIsometry,
    List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 4
      1] at
    hf
  simp_rw [hf, ← LinearMap.comp_assoc, AlgEquiv.inj_comp, ← hf, LinearMap.adjoint_adjoint,
    AlgEquiv.comp_inj]

theorem qam_ir_reflexive_starAlgEquiv_conj [Nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ}
    (hf : @StarAlgEquiv.IsIsometry n _ _ φ hφ f) (A : l(ℍ)) :
    Qam.reflIdempotent hφ.elim (f.toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ f.symm.toAlgEquiv.toLinearMap) 1 =
      f.toAlgEquiv.toLinearMap ∘ₗ Qam.reflIdempotent hφ.elim A 1 ∘ₗ f.symm.toAlgEquiv.toLinearMap :=
  by
  calc
    Qam.reflIdempotent hφ.elim
          (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map) 1 =
        Qam.reflIdempotent hφ.elim
          (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map)
          (f.to_alg_equiv.to_linear_map ∘ₗ 1 ∘ₗ f.symm.to_alg_equiv.to_linear_map) :=
      _
    _ =
        f.to_alg_equiv.to_linear_map ∘ₗ
          Qam.reflIdempotent hφ.elim A 1 ∘ₗ f.symm.to_alg_equiv.to_linear_map :=
      Qam.reflIdempotent_starAlgEquiv_conj hf _ _
  congr
  simp only [LinearMap.one_comp, ← StarAlgEquiv.comp_eq_iff]

theorem qam_ir_reflexive'_starAlgEquiv_conj [Nontrivial n] {f : ℍ ≃⋆ₐ[ℂ] ℍ}
    (hf : @StarAlgEquiv.IsIsometry n _ _ φ hφ f) (A : l(ℍ)) :
    Qam.reflIdempotent hφ.elim 1 (f.toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ f.symm.toAlgEquiv.toLinearMap) =
      f.toAlgEquiv.toLinearMap ∘ₗ Qam.reflIdempotent hφ.elim 1 A ∘ₗ f.symm.toAlgEquiv.toLinearMap :=
  by
  calc
    Qam.reflIdempotent hφ.elim (1 : l(ℍ))
          (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map) =
        Qam.reflIdempotent hφ.elim
          (f.to_alg_equiv.to_linear_map ∘ₗ 1 ∘ₗ f.symm.to_alg_equiv.to_linear_map)
          (f.to_alg_equiv.to_linear_map ∘ₗ A ∘ₗ f.symm.to_alg_equiv.to_linear_map) :=
      _
    _ =
        f.to_alg_equiv.to_linear_map ∘ₗ
          Qam.reflIdempotent hφ.elim 1 A ∘ₗ f.symm.to_alg_equiv.to_linear_map :=
      Qam.reflIdempotent_starAlgEquiv_conj hf _ _
  -- congr,
  simp only [LinearMap.one_comp]
  have : 1 = f.to_alg_equiv.to_linear_map.comp f.symm.to_alg_equiv.to_linear_map := by
    simp only [← StarAlgEquiv.comp_eq_iff, LinearMap.one_comp]
  simp only [← this]

theorem InnerAut.qam [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n] {U : Matrix.unitaryGroup n ℂ}
    (hU : Commute φ.Matrix U) (A : l(ℍ)) : Qam φ (f_{U} ∘ₗ A ∘ₗ f_{star U}) ↔ Qam φ A :=
  by
  rw [← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map, ←
    inner_aut_star_alg_equiv_to_linear_map]
  exact qam_starAlgEquiv_conj_iff ((unitary_commutes_with_hφ_matrix_iff_isIsometry U).mp hU) _

theorem InnerAut.ir_reflexive [Nontrivial n] {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.Matrix U)
    (A : l(ℍ)) :
    Qam.reflIdempotent hφ.elim (f_{U} ∘ₗ A ∘ₗ f_{star U}) 1 =
      f_{U} ∘ₗ Qam.reflIdempotent hφ.elim A 1 ∘ₗ f_{star U} :=
  by
  rw [← inner_aut_inv_eq_star, ← inner_aut_star_alg_equiv_symm_to_linear_map, ←
    inner_aut_star_alg_equiv_to_linear_map]
  exact
    qam_ir_reflexive_starAlgEquiv_conj ((unitary_commutes_with_hφ_matrix_iff_isIsometry U).mp hU) _

theorem InnerAut.qam_is_reflexive [Nontrivial n] {U : Matrix.unitaryGroup n ℂ}
    (hU : Commute φ.Matrix U) {A : l(ℍ)} :
    @QamLmNontracialIsReflexive n _ _ φ _ (f_{U} ∘ₗ A ∘ₗ f_{star U}) ↔
      @QamLmNontracialIsReflexive _ _ _ _ hφ A :=
  by
  simp_rw [QamLmNontracialIsReflexive, InnerAut.ir_reflexive hU]
  nth_rw_lhs 1 [LinearMap.ext_iff]
  simp_rw [LinearMap.comp_apply, inner_aut_eq_iff, LinearMap.one_apply, ← LinearMap.comp_apply, ←
    LinearMap.ext_iff]
  rw [← LinearMap.one_comp (inner_aut U⁻¹)]
  simp_rw [inner_aut_inv_eq_star, ← inner_aut.inj_comp (star U)]

theorem InnerAut.qam_is_irreflexive [Nontrivial n] {U : Matrix.unitaryGroup n ℂ}
    (hU : Commute φ.Matrix U) {A : l(ℍ)} :
    @QamLmNontracialIsUnreflexive _ _ _ _ hφ (f_{U} ∘ₗ A ∘ₗ f_{star U}) ↔
      @QamLmNontracialIsUnreflexive _ _ _ _ hφ A :=
  by
  simp_rw [QamLmNontracialIsUnreflexive, InnerAut.ir_reflexive hU, LinearMap.ext_iff,
    LinearMap.comp_apply, inner_aut_eq_iff, LinearMap.zero_apply, LinearMap.map_zero]
  refine' ⟨fun h x => _, fun h x => by rw [h]⟩
  specialize h (f_{U} x)
  simp_rw [← inner_aut_inv_eq_star, inner_aut_inv_apply_inner_aut_self] at h
  exact h

def Qam.Iso (A B : l(ℍ)) : Prop :=
  ∃ f : ℍ ≃⋆ₐ[ℂ] ℍ,
    A ∘ₗ f.toAlgEquiv.toLinearMap = f.toAlgEquiv.toLinearMap ∘ₗ B ∧ f φ.Matrix = φ.Matrix

structure QamIso [hφ : Fact φ.IsFaithfulPosMap] {A B : l(ℍ)} (hA : Qam φ A) (hB : Qam φ B) extends
    StarAlgEquiv ℂ ℍ ℍ where
  IsHom :=
    A ∘ₗ to_star_alg_equiv.toAlgEquiv.toLinearMap = to_star_alg_equiv.toAlgEquiv.toLinearMap ∘ₗ B
  is_iso := to_fun φ.Matrix = φ.Matrix

-- -- TODO:
-- def qam.lm.reflexive.iso {A B : l(ℍ)} (hA : qam_lm_is_reflexive A)
--   (hB : qam_lm_is_reflexive B) :
--   Prop :=
-- ∃ f : ℍ ≃⋆ₐ[ℂ] ℍ, A ∘ f = f ∘ B
-- def qam.lm.unreflexive.iso {A B : l(ℍ)} (hA : qam_lm_is_unreflexive A)
--   (hB : qam_lm_is_unreflexive B) : Prop :=
-- ∃ f : ℍ ≃⋆ₐ[ℂ] ℍ, A ∘ f = f ∘ B
theorem Qam.iso_iff [hφ : Fact φ.IsFaithfulPosMap] {A B : l(ℍ)} [Nontrivial n] :
    @Qam.Iso n _ _ φ A B ↔
      ∃ U : unitaryGroup n ℂ, A ∘ₗ innerAut U = innerAut U ∘ₗ B ∧ Commute φ.Matrix U :=
  by
  simp_rw [← innerAut_adjoint_eq_iff]
  have hf : ∀ U : unitary_group n ℂ, f_{U} = (inner_aut_star_alg U).toAlgEquiv.toLinearMap :=
    fun _ => rfl
  have hh : ∀ U : unitary_group n ℂ, (inner_aut_star_alg U).symm = inner_aut_star_alg (star U) :=
    by
    intro V
    ext1
    simp_rw [inner_aut_star_alg_symm_apply, inner_aut_star_alg_apply, unitary.star_eq_inv,
      unitary_group.inv_apply, star_star]
  have := fun U =>
    List.TFAE.out
      (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _
        (inner_aut_star_alg U))
      1 0
  simp_rw [hf, ← hh, this]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨U, rfl⟩ := star_alg_equiv.of_matrix_is_inner f
    exact ⟨U, hf⟩
  · rintro ⟨U, hU⟩
    exact ⟨inner_aut_star_alg U, hU⟩

theorem Qam.iso_preserves_spectrum (A B : l(ℍ)) (h : @Qam.Iso n _ _ φ A B) :
    spectrum ℂ A = spectrum ℂ B := by
  obtain ⟨f, ⟨hf, hh⟩⟩ := h
  let f' := f.to_alg_equiv.to_linear_map
  let f'' := f.symm.to_alg_equiv.to_linear_map
  have hh' : f'' ∘ₗ f' = LinearMap.id :=
    by
    rw [LinearMap.ext_iff]
    intro x
    simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv,
      StarAlgEquiv.symm_apply_apply, LinearMap.id_apply]
  have : B = f'' ∘ₗ A ∘ₗ f' := by rw [hf, ← LinearMap.comp_assoc, hh', LinearMap.id_comp]
  rw [this, ← spectrum.comm, LinearMap.comp_assoc, linear_map.comp_eq_id_comm.mp hh',
    LinearMap.comp_id]

-- MOVE:
theorem innerAut_lm_rankOne [hφ : Fact φ.IsFaithfulPosMap] [Nontrivial n]
    {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.Matrix U) (x y : ℍ) :
    f_{U} ∘ₗ (|x⟩⟨y| : l(ℍ)) ∘ₗ f_{star U} = |f_{U} x⟩⟨f_{U} y| :=
  by
  rw [← innerAut_adjoint_eq_iff] at hU
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    SMulHomClass.map_smul, ← hU, LinearMap.adjoint_inner_right, eq_self_iff_true, forall_true_iff]

local notation "e_{" x "," y "}" => Matrix.stdBasisMatrix x y (1 : ℂ)

--MOVE:
theorem innerAut_lm_basis_apply (U : Matrix.unitaryGroup n ℂ) (i j k l : n) :
    (f_{U} e_{i,j}) k l = (U ⊗ₖ star U) (k, j) (i, l) :=
  by
  simp_rw [Matrix.innerAut_apply, Matrix.mul_apply, Matrix.UnitaryGroup.inv_apply,
    Matrix.stdBasisMatrix, mul_boole, Finset.sum_mul, ite_mul, MulZeroClass.zero_mul, ite_and,
    Matrix.kroneckerMap, Matrix.of_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem Qam.rankOne_toMatrix_of_star_algEquiv_coord (x y : Matrix n n ℂ) (i j k l : n) :
    hφ.elim.toMatrix ↑|x⟩⟨y| (i, j) (k, l) =
      ((x ⬝ hφ.elim.matrixIsPosDef.rpow (1 / 2)) ⊗ₖ (y ⬝ hφ.elim.matrixIsPosDef.rpow (1 / 2))ᴴᵀ)
        (i, k) (j, l) :=
  by
  simp_rw [rankOne_toMatrix, conj_transpose_col, mul_apply, col_apply, row_apply, Pi.star_apply,
    reshape_apply, kronecker_apply, conj_apply]
  simp only [Fintype.univ_punit, Finset.sum_const, Finset.card_singleton, nsmul_eq_mul,
    algebraMap.coe_one, one_mul]

