/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LinearAlgebra.MyIps.Nontracial
import LinearAlgebra.MyIps.MatIps
import LinearAlgebra.MyIps.TensorHilbert
import LinearAlgebra.IsReal
import LinearAlgebra.MyIps.Frob
import LinearAlgebra.TensorFinite
import LinearAlgebra.MyIps.OpUnop
import LinearAlgebra.LmulRmul
import LinearAlgebra.Nacgor

#align_import quantum_graph.schur_idempotent

/-!
 # Schur idempotent operator

 In this file we define the Schur idempotent operator and prove some basic properties.
-/


variable {n : Type _} [Fintype n] [DecidableEq n] {s : n → Type _} [∀ i, Fintype (s i)]
  [∀ i, DecidableEq (s i)]

open scoped TensorProduct BigOperators Kronecker

local notation "𝔹" => ∀ i, Matrix (s i) (s i) ℂ

local notation "l(" x ")" => x →ₗ[ℂ] x

-- local notation `L(`x`)` := x →L[ℂ] x
-- variables {℘ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ}
open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

local notation "m" x => LinearMap.mul' ℂ x

-- local notation `η` x := algebra.linear_map ℂ x
local notation x " ⊗ₘ " y => TensorProduct.map x y

-- local notation `υ` B :=
--   ((tensor_product.assoc ℂ B B B) : (B ⊗[ℂ] B ⊗[ℂ] B) →ₗ[ℂ] B ⊗[ℂ] (B ⊗[ℂ] B))
-- local notation `υ⁻¹` B :=
--   ((tensor_product.assoc ℂ B B B).symm : B ⊗[ℂ] (B ⊗[ℂ] B) →ₗ[ℂ] (B ⊗[ℂ] B ⊗[ℂ] B))
-- local notation x`ϰ`y := (↑(tensor_product.comm ℂ x y) : (x ⊗[ℂ] y) →ₗ[ℂ] (y ⊗[ℂ] x))
-- local notation x`ϰ⁻¹`y := ((tensor_product.comm ℂ x y).symm : (y ⊗[ℂ] x) →ₗ[ℂ] (x ⊗[ℂ] y))
-- local notation `τ` x  := ((tensor_product.lid ℂ x) : (ℂ ⊗[ℂ] x) →ₗ[ℂ] x)
-- local notation `τ⁻¹` x := ((tensor_product.lid ℂ x).symm : x →ₗ[ℂ] (ℂ ⊗[ℂ] x))
-- local notation `id` x := (1 : x →ₗ[ℂ] x)
open scoped Functional

noncomputable instance Module.Dual.isNormedAddCommGroupOfRing {n : Type _} [Fintype n]
    [DecidableEq n] {ψ : Module.Dual ℂ (Matrix n n ℂ)} [hψ : Fact ψ.IsFaithfulPosMap] :
    NormedAddCommGroupOfRing (Matrix n n ℂ)
    where
  toHasNorm := NormedAddCommGroup.toHasNorm
  toMetricSpace := NormedAddCommGroup.toMetricSpace
  dist_eq := NormedAddCommGroup.dist_eq

noncomputable instance Pi.module.Dual.isNormedAddCommGroupOfRing
    {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] :
    NormedAddCommGroupOfRing 𝔹
    where
  toHasNorm := NormedAddCommGroup.toHasNorm
  toMetricSpace := NormedAddCommGroup.toMetricSpace
  dist_eq := NormedAddCommGroup.dist_eq

noncomputable def schurIdempotent {B : Type _} [NormedAddCommGroupOfRing B] [InnerProductSpace ℂ B]
    [SMulCommClass ℂ B B] [IsScalarTower ℂ B B] [FiniteDimensional ℂ B] : l(B) →ₗ[ℂ] l(B) →ₗ[ℂ] l(B)
    where
  toFun x :=
    { toFun := fun y => (m B) ∘ₗ (x ⊗ₘ y) ∘ₗ (m B).adjoint
      map_add' := fun x y => by
        simp only [TensorProduct.map_apply, TensorProduct.map_add_right, LinearMap.add_comp,
          LinearMap.comp_add]
      map_smul' := fun r x => by
        simp only [TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul,
          RingHom.id_apply] }
  map_add' x y :=
    by
    simp only [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.ext_iff, LinearMap.add_apply, LinearMap.coe_mk]
    intro _ _; rfl
  map_smul' r x :=
    by
    simp only [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.coe_mk, RingHom.id_apply]
    intro _ _; rfl

theorem schurIdempotent.apply_rankOne {B : Type _} [NormedAddCommGroupOfRing B]
    [InnerProductSpace ℂ B] [SMulCommClass ℂ B B] [IsScalarTower ℂ B B] [FiniteDimensional ℂ B]
    (a b c d : B) : schurIdempotent ↑|a⟩⟨b| ↑|c⟩⟨d| = (|a * c⟩⟨b * d| : B →ₗ[ℂ] B) :=
  by
  rw [schurIdempotent, LinearMap.ext_iff_inner_map]
  intro x
  simp only [ContinuousLinearMap.coe_coe, LinearMap.coe_mk, rankOne_apply, LinearMap.comp_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span ((LinearMap.mul' ℂ B).adjoint x)
  rw [← h]
  simp_rw [map_sum, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, rankOne_apply,
    LinearMap.mul'_apply, smul_mul_smul, ← TensorProduct.inner_tmul, ← Finset.sum_smul, ← inner_sum,
    h, LinearMap.adjoint_inner_right, LinearMap.mul'_apply]

-- @[elab_as_eliminator]
-- theorem linear_map.induction_on
--   {𝕜 B : Type*} [is_R_or_C 𝕜] [normed_add_comm_group B] [inner_product_space 𝕜 B]
--   [finite_dimensional 𝕜 B] {C : (B →ₗ[𝕜] B) → Prop}
--   (z : B →ₗ[𝕜] B) (C0 : C 0) (C1 : ∀ {x y}, C $ ((rank_one x y : B →L[𝕜] B) : B →ₗ[𝕜] B))
--   (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
-- begin
--   -- let f := std_orthonormal_basis 𝕜 B,
--   let n := finite_dimensional.finrank 𝕜 B * finite_dimensional.finrank 𝕜 B,
--   obtain ⟨α, β, rfl⟩ :
--     ∃ x y : fin n → B, z = ∑ i, ↑(rank_one (x i) (y i) : B →L[𝕜] B) :=
--   begin
--     let n' := finite_dimensional.finrank 𝕜 B,
--     let σ : fin (n' * n') ≃ fin n' × fin n' := fin_prod_fin_equiv.symm,
--     obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one z,
--     refine ⟨λ i, α (σ i), λ i, β (σ i), _⟩,
--     apply fintype.sum_bijective σ.symm,
--     { exact (equiv.symm σ).bijective, },
--     { simp only [equiv.apply_symm_apply, eq_self_iff_true, forall_true_iff], },
--   end,
-- end
theorem schurIdempotent_one_one_right {B : Type _} [NormedAddCommGroupOfRing B]
    [InnerProductSpace ℂ B] [SMulCommClass ℂ B B] [IsScalarTower ℂ B B] [FiniteDimensional ℂ B]
    (A : l(B)) : schurIdempotent (A : l(B)) (|(1 : B)⟩⟨(1 : B)| : l(B)) = A :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp_rw [map_sum, LinearMap.sum_apply, schurIdempotent.apply_rankOne, mul_one]

theorem schurIdempotent_one_one_left {B : Type _} [NormedAddCommGroupOfRing B]
    [InnerProductSpace ℂ B] [SMulCommClass ℂ B B] [IsScalarTower ℂ B B] [FiniteDimensional ℂ B]
    (A : l(B)) : schurIdempotent (|(1 : B)⟩⟨(1 : B)| : l(B)) A = A :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp_rw [map_sum, schurIdempotent.apply_rankOne, one_mul]

private theorem schur_idempotent_one_right_aux {B : Type _} [NormedAddCommGroupOfRing B]
    [InnerProductSpace ℂ B] [SMulCommClass ℂ B B] [IsScalarTower ℂ B B] [FiniteDimensional ℂ B]
    [StarMul B] {ψ : Module.Dual ℂ B} (hψ : ∀ a b, ⟪a, b⟫_ℂ = ψ (star a * b)) (a b c : B) :
    ⟪a * b, c⟫_ℂ = ⟪b, star a * c⟫_ℂ := by simp_rw [hψ, StarMul.star_hMul, ← mul_assoc]

theorem lmul_adjoint {B : Type _} [NormedAddCommGroupOfRing B] [InnerProductSpace ℂ B]
    [SMulCommClass ℂ B B] [IsScalarTower ℂ B B] [FiniteDimensional ℂ B] [StarMul B]
    {ψ : Module.Dual ℂ B} (hψ : ∀ a b, ⟪a, b⟫_ℂ = ψ (star a * b)) (a : B) :
    (lmul a : l(B)).adjoint = lmul (star a) :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro u
  simp_rw [LinearMap.adjoint_inner_left, lmul_apply, schur_idempotent_one_right_aux hψ, star_star]

theorem rmul_adjoint {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (a : 𝔹) :
    (rmul a : l(𝔹)).adjoint = rmul (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star a)) :=
  by
  rw [LinearMap.ext_iff_inner_map]
  intro u
  simp_rw [LinearMap.adjoint_inner_left, rmul_apply,
    Module.Dual.pi.IsFaithfulPosMap.inner_left_conj']

theorem ContinuousLinearMap.linearMap_adjoint {𝕜 B C : Type _} [IsROrC 𝕜] [NormedAddCommGroup B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 B]
    [FiniteDimensional 𝕜 C] (x : B →L[𝕜] C) :
    (x : B →ₗ[𝕜] C).adjoint =
      @ContinuousLinearMap.adjoint 𝕜 _ _ _ _ _ _ _ (FiniteDimensional.complete 𝕜 B)
        (FiniteDimensional.complete 𝕜 C) x :=
  rfl

theorem schurIdempotent_adjoint {B : Type _} [NormedAddCommGroupOfRing B] [InnerProductSpace ℂ B]
    [SMulCommClass ℂ B B] [IsScalarTower ℂ B B] [FiniteDimensional ℂ B] (x y : l(B)) :
    (schurIdempotent x y).adjoint = schurIdempotent x.adjoint y.adjoint :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  obtain ⟨γ, δ, rfl⟩ := LinearMap.exists_sum_rankOne y
  simp only [map_sum, LinearMap.sum_apply]
  repeat' apply Finset.sum_congr rfl; intros
  simp_rw [schurIdempotent.apply_rankOne, ContinuousLinearMap.linearMap_adjoint, rankOne.adjoint,
    schurIdempotent.apply_rankOne]

theorem schurIdempotent_real
    -- {B : Type*}
    --   [normed_add_comm_group_of_ring B]
    --   [inner_product_space ℂ B]
    --   [smul_comm_class ℂ B B]
    --   [is_scalar_tower ℂ B B]
    --   [finite_dimensional ℂ B]
    --   [star_ring B]
    --   [star_module ℂ B]
    -- {ψ : module.dual ℂ B} (hψ : ∀ a b, ⟪a, b⟫_ℂ = ψ (star a * b))
    {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (x y : l(𝔹)) :
    (schurIdempotent x y : l(𝔹)).Real = schurIdempotent y.Real x.Real :=
  by
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one
  obtain ⟨γ, ζ, rfl⟩ := y.exists_sum_rank_one
  simp only [map_sum, LinearMap.real_sum, LinearMap.sum_apply, schurIdempotent.apply_rankOne]
  simp_rw [← rankOneLm_eq_rankOne, Pi.rankOneLm_real_apply, rankOneLm_eq_rankOne,
    schurIdempotent.apply_rankOne, ← _root_.map_mul, ← StarMul.star_hMul]
  rw [Finset.sum_comm]

theorem schurIdempotent_one_right_rankOne {B : Type _} [NormedAddCommGroupOfRing B]
    [InnerProductSpace ℂ B] [SMulCommClass ℂ B B] [IsScalarTower ℂ B B] [FiniteDimensional ℂ B]
    [StarMul B] {ψ : Module.Dual ℂ B} (hψ : ∀ a b, ⟪a, b⟫_ℂ = ψ (star a * b)) (a b : B) :
    schurIdempotent (↑|a⟩⟨b|) 1 = lmul a * (lmul b : l(B)).adjoint :=
  by
  simp_rw [LinearMap.ext_iff_inner_map]
  intro u
  let f := stdOrthonormalBasis ℂ B
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm f]
  simp_rw [map_sum, LinearMap.sum_apply, schurIdempotent.apply_rankOne, ContinuousLinearMap.coe_coe,
    rankOne_apply, LinearMap.mul_apply, lmul_apply, sum_inner, inner_smul_left,
    schur_idempotent_one_right_aux hψ, inner_conj_symm, OrthonormalBasis.sum_inner_mul_inner,
    lmul_adjoint hψ, lmul_apply]

theorem Module.Dual.pi.IsFaithfulPosMap.basis.apply_cast_eq_mp
    {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    {i j : n} (h : i = j) (p : s i × s i) :
    (by rw [h] : Matrix (s i) (s i) ℂ = Matrix (s j) (s j) ℂ).mp ((hψ i).elim.Basis p) =
      (hψ j).elim.Basis (by rw [← h] <;> exact p) :=
  by tidy

theorem pi_lmul_toMatrix {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (x : 𝔹) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix (fun i => (hψ i).elim) (lmul x : l(𝔹)) :
        Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) =
      blockDiagonal' fun i => x i ⊗ₖ 1 :=
  by
  ext1 r l
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.toMatrix_apply', lmul_apply, mul_include_block,
    include_block_apply, mul_apply, dite_apply, dite_hMul, Pi.zero_apply, MulZeroClass.zero_mul,
    Finset.sum_dite_irrel, ← mul_apply, block_diagonal'_apply, kronecker_map, of_apply,
    @eq_comm _ r.fst, one_apply, mul_boole, Matrix.cast_hMul,
    Module.Dual.pi.IsFaithfulPosMap.basis.apply_cast_eq_mp, mul_eq_mul, Matrix.mul_assoc,
    Module.Dual.IsFaithfulPosMap.basis_apply, Matrix.mul_assoc, pos_def.rpow_mul_rpow, neg_add_self,
    pos_def.rpow_zero, Matrix.mul_one, mul_apply, std_basis_matrix, mul_boole, ite_and,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, @eq_comm _ r.snd.snd, Finset.sum_const_zero,
    eq_mpr_eq_cast]
  congr 2
  ext1 h
  tidy

example {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap]
    (x : 𝔹) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix (fun i => (hψ i).elim) (lmul x : l(𝔹)) :
        Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) =
      blockDiagonal' fun i => (hψ i).elim.toMatrix (lmul (x i)) :=
  by simp_rw [pi_lmul_toMatrix, lmul_eq_mul, LinearMap.mulLeft_toMatrix]

theorem pi_rmul_toMatrix {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (x : 𝔹) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix (fun i => (hψ i).elim) (rmul x : l(𝔹)) :
        Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) =
      blockDiagonal' fun i => 1 ⊗ₖ ((hψ i).elim.sig (1 / 2) (x i))ᵀ :=
  by
  ext1 r l
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.toMatrix_apply', rmul_apply, include_block_mul,
    include_block_apply, mul_apply, dite_apply, dite_hMul, Pi.zero_apply, MulZeroClass.zero_mul,
    Finset.sum_dite_irrel, ← mul_apply, block_diagonal'_apply, kronecker_map, of_apply,
    @eq_comm _ r.fst, one_apply, mul_boole, Matrix.cast_hMul,
    Module.Dual.pi.IsFaithfulPosMap.basis.apply_cast_eq_mp, mul_eq_mul, Matrix.mul_assoc,
    Module.Dual.IsFaithfulPosMap.basis_apply, Matrix.mul_assoc, ←
    Matrix.mul_assoc (pos_def.rpow _ _) _ (pos_def.rpow _ (1 / 2 : ℝ)), ←
    Module.Dual.IsFaithfulPosMap.sig_apply, mul_apply, std_basis_matrix, boole_mul, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    transpose_apply, Finset.sum_const_zero, eq_mpr_eq_cast, @eq_comm _ r.snd.1]
  congr 2
  ext1 h
  tidy

theorem unitary.coe_pi (U : ∀ i, unitaryGroup (s i) ℂ) :
    (unitary.pi U : ∀ i, Matrix (s i) (s i) ℂ) = ↑U :=
  rfl

theorem unitary.coe_pi_apply (U : ∀ i, unitaryGroup (s i) ℂ) (i : n) :
    (↑U : ∀ i, Matrix (s i) (s i) ℂ) i = U i :=
  rfl

theorem pi_inner_aut_toMatrix {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (U : ∀ i, unitaryGroup (s i) ℂ) :
    (Module.Dual.pi.IsFaithfulPosMap.toMatrix (fun i => (hψ i).elim)
          ((unitary.innerAutStarAlg ℂ (unitary.pi U)).toAlgEquiv.toLinearMap : l(𝔹)) :
        Matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ) =
      blockDiagonal' fun i =>
        U i ⊗ₖ ((hψ i).elim.sig (-(1 / 2 : ℝ)) (U i : Matrix (s i) (s i) ℂ))ᴴᵀ :=
  by
  have :
    ((unitary.innerAutStarAlg ℂ (unitary.pi U)).toAlgEquiv.toLinearMap : l(𝔹)) =
      (lmul ↑U : l(𝔹)) * (rmul (star ↑U) : l(𝔹)) :=
    by
    ext1
    simp_rw [AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv, LinearMap.mul_apply,
      lmul_apply, rmul_apply, unitary.innerAutStarAlg_apply, mul_assoc, unitary.coe_star,
      unitary.coe_pi]
  rw [this, _root_.map_mul, pi_lmul_toMatrix, pi_rmul_toMatrix, mul_eq_mul, ← block_diagonal'_mul]
  simp_rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Pi.star_apply,
    star_eq_conj_transpose, block_diagonal'_inj, unitary.coe_pi_apply]
  ext1 i
  nth_rw 1 [← neg_neg (1 / 2 : ℝ)]
  simp_rw [← Module.Dual.IsFaithfulPosMap.sig_conjTranspose]
  rfl

theorem schurIdempotent_one_left_rankOne {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (a b : 𝔹) :
    schurIdempotent (1 : l(𝔹)) |a⟩⟨b| = (rmul a : l(𝔹)) * (rmul b : l(𝔹)).adjoint :=
  by
  simp_rw [← ext_inner_map]
  intro u
  let f := stdOrthonormalBasis ℂ 𝔹
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm f, map_sum, LinearMap.sum_apply]
  simp_rw [schurIdempotent.apply_rankOne, LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, LinearMap.mul_apply, rmul_apply, sum_inner, inner_smul_left,
    Module.Dual.pi.IsFaithfulPosMap.inner_right_conj', inner_conj_symm,
    OrthonormalBasis.sum_inner_mul_inner, ← Module.Dual.pi.IsFaithfulPosMap.inner_right_conj',
    rmul_adjoint, rmul_apply]

theorem Psi.symm_map {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    [hψ : ∀ i, Fact (ψ i).IsFaithfulPosMap] (r₁ r₂ : ℝ)
    (f g : (∀ i, Matrix (s i) (s i) ℂ) →ₗ[ℂ] ∀ i, Matrix (s i) (s i) ℂ) :
    Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ (schurIdempotent f g) =
      Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ f *
        Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ g :=
  by
  suffices
    ∀ a b c d : 𝔹,
      Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ (schurIdempotent (↑|a⟩⟨b| : l(𝔹)) |c⟩⟨d|) =
        Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ |a⟩⟨b| *
          Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ |c⟩⟨d|
    by
    obtain ⟨α, β, rfl⟩ := f.exists_sum_rank_one
    obtain ⟨γ, δ, rfl⟩ := g.exists_sum_rank_one
    simp_rw [map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_mul, map_sum, this]
  intro a b c d
  simp_rw [Module.Dual.pi.IsFaithfulPosMap.psi_apply, schurIdempotent.apply_rankOne,
    Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply, Algebra.TensorProduct.tmul_mul_tmul, op_apply,
    ← MulOpposite.op_mul, ← StarMul.star_hMul, ← _root_.map_mul]

-- lemma pi.qam.symm_adjoint_eq_symm'_of_adjoint [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (x : l(𝔹)) :
--   (qam.symm (λ i, (h℘ i).elim) x).adjoint = qam.symm' (λ i, (h℘ i).elim) (x.adjoint) :=
-- begin
--   obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one x,
--   simp_rw [map_sum, ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint, rank_one_lm_eq_rank_one,
--     qam.rank_one.symmetric_eq, qam.rank_one.symmetric'_eq, ← rank_one_lm_eq_rank_one,
--     rank_one_lm_adjoint],
-- end
-- private lemma commute.adjoint_adjoint {K E : Type*} [is_R_or_C K] [normed_add_comm_group E]
--   [inner_product_space K E] [complete_space E] {f g : E →L[K] E} :
--   commute f.adjoint g.adjoint ↔ commute f g :=
-- commute_star_star
-- private lemma commute.adjoint_adjoint_lm {K E : Type*} [is_R_or_C K] [normed_add_comm_group E]
--   [inner_product_space K E] [finite_dimensional K E] {f g : E →ₗ[K] E} :
--   commute f.adjoint g.adjoint ↔ commute f g :=
-- commute_star_star
-- @[instance] def B.star_module :
--   star_module ℂ 𝔹 :=
-- by {
--   apply @pi.star_module _ _ ℂ _ _ _ _,
--   exact λ i, matrix.star_module,
-- }
-- lemma linear_map.direct_sum.is_real.adjoint_is_real_iff_commute_with_sig
--   [h℘ : Π i, fact (℘ i).is_faithful_pos_map] {f : 𝔹 →ₗ[ℂ] 𝔹} (hf : f.is_real) :
--   (f.adjoint).is_real ↔
--   commute f (linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map :=
-- begin
--   rw linear_map.is_real_iff at hf,
--   have : commute f (linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map
--     ↔ commute (f.adjoint) (linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map,
--   { simp_rw [linear_map.is_faithful_pos_map.direct_sum.sig h℘],
--     nth_rewrite_rhs 0 ← linear_map.is_faithful_pos_map.direct_sum.sig_adjoint,
--     rw commute.adjoint_adjoint_lm, },
--   rw this,
--   clear this,
--   rw [linear_map.is_real_iff, linear_map.direct_sum.adjoint_real_eq, hf, ← linear_map.comp_assoc,
--     direct_sum.comp_sig_eq, neg_neg],
--   simp_rw [commute, semiconj_by, linear_map.mul_eq_comp, @eq_comm _ _ ((linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map ∘ₗ _)],
-- end
-- lemma direct_sum.sig_apply_pos_def_matrix [h℘ : Π i, fact (℘ i).is_faithful_pos_map]
--   (t s : ℝ) :
--   (linear_map.is_faithful_pos_map.direct_sum.sig h℘) t (pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘) s)
--   = pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘) s :=
-- begin
--   simp_rw [linear_map.is_faithful_pos_map.direct_sum.sig_apply h℘, pi.pos_def.rpow_mul_rpow,
--     neg_add_cancel_comm],
-- end
-- -- lemma direct_sum.sig_apply_pos_def_matrix' [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (t : ℝ) :
-- --   (linear_map.is_faithful_pos_map.direct_sum.sig h℘) t (linear_map.direct_sum_matrix_block ℘) = linear_map.direct_sum_matrix_block ℘ :=
-- -- begin
-- --   have : linear_map.direct_sum_matrix_block ℘ = λ i, (℘ i).matrix :=
-- --   by { ext1 i, simp only [linear_map.direct_sum_matrix_block_apply], },
-- --   rw [this],
-- --   nth_rewrite_rhs 0 [← pi.pos_def.rpow_one_eq_self (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘)],
-- --   rw [← direct_sum.sig_apply_pos_def_matrix t (1 : ℝ)],
-- --   rw [← this],
-- -- end
