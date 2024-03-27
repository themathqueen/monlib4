import Monlib.LinearAlgebra.IsReal
import Monlib.LinearAlgebra.MyIps.Nontracial

#align_import quantum_graph.symm

@[simps]
noncomputable def LinearEquiv.symmMap (R : Type _) [IsROrC R] (M : Type _) [NormedAddCommGroup M]
    [InnerProductSpace R M] [StarAddMonoid M] [StarModule R M] [FiniteDimensional R M] :
    (M →ₗ[R] M) ≃ₗ[R] M →ₗ[R] M
    where
  toFun f := LinearMap.adjoint (LinearMap.real f)
  invFun f := (LinearMap.adjoint f).real
  left_inv f := by simp only [LinearMap.adjoint_adjoint, LinearMap.real_real]
  right_inv f := by simp only [LinearMap.real_real, LinearMap.adjoint_adjoint]
  map_add' f g := by simp only [LinearMap.real_add, map_add]
  map_smul' c f := by
    simp only [LinearMap.real_smul, LinearMap.adjoint_smul, starRingEnd_self_apply,
      RingHom.id_apply]

theorem LinearEquiv.symmMap_real {R : Type _} [IsROrC R] {M : Type _} [NormedAddCommGroup M]
    [InnerProductSpace R M] [StarAddMonoid M] [StarModule R M] [FiniteDimensional R M] :
    LinearMap.real (LinearEquiv.symmMap R M : (M →ₗ[R] M) →ₗ[R] M →ₗ[R] M) =
      (LinearEquiv.symmMap R M).symm :=
  by
  ext1 f
  simp_rw [LinearMap.real_apply, LinearEquiv.coe_coe, LinearMap.star_eq_adjoint,
    LinearEquiv.symmMap_apply, LinearMap.adjoint_adjoint]
  rfl

open scoped TensorProduct Kronecker Matrix Functional

variable {n : Type _} [Fintype n] [DecidableEq n] {s : n → Type _} [∀ i, Fintype (s i)]
  [∀ i, DecidableEq (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}

local notation "𝔹" => PiMat n s

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ x y

local notation "m" x => LinearMap.mul' ℂ x

local notation "η" x => Algebra.linearMap ℂ x

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" B => (TensorProduct.assoc ℂ B B B : (B ⊗[ℂ] B) ⊗[ℂ] B →ₗ[ℂ] B ⊗[ℂ] B ⊗[ℂ] B)

local notation "υ⁻¹" B =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.assoc ℂ B B B))

local notation x "ϰ" y =>
  LinearEquiv.toLinearMap (TensorProduct.comm ℂ x y)

local notation x "ϰ⁻¹" y =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ x y))

local notation "τ" x =>
  LinearEquiv.toLinearMap (TensorProduct.lid ℂ x)

local notation "τ⁻¹" x =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ x))

local notation "id" x => (1 : x →ₗ[ℂ] x)

theorem LinearEquiv.symmMap_rankOne_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (a b : 𝔹) :
    LinearEquiv.symmMap _ _ (|a⟩⟨b| : 𝔹 →ₗ[ℂ] 𝔹) =
      |Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star b)⟩⟨star a| :=
  by
  rw [LinearEquiv.symmMap_apply, ← rankOneLm_eq_rankOne, Pi.rankOneLm_real_apply, rankOneLm_adjoint]
  rfl

theorem LinearEquiv.symmMap_symm_rankOne_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (a b : 𝔹) :
    (LinearEquiv.symmMap _ _).symm (|a⟩⟨b| : 𝔹 →ₗ[ℂ] 𝔹) =
      |star b⟩⟨Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star a)| :=
  by
  rw [LinearEquiv.symmMap_symm_apply, ← rankOneLm_eq_rankOne, rankOneLm_adjoint,
    Pi.rankOneLm_real_apply]
  rfl

open scoped BigOperators

open TensorProduct

set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 0 in
theorem Pi.symmMap_eq [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (f : (∀ i, Matrix (s i) (s i) ℂ) →ₗ[ℂ] ∀ i, Matrix (s i) (s i) ℂ) :
    (LinearEquiv.symmMap ℂ (∀ i, Matrix (s i) (s i) ℂ)) f =
      (τ 𝔹) ∘ₗ
        (𝔹 ϰ ℂ) ∘ₗ
          ((id 𝔹) ⊗ₘ LinearMap.adjoint (Algebra.linearMap ℂ 𝔹) ∘ₗ m 𝔹) ∘ₗ
            (υ 𝔹) ∘ₗ
              (((id 𝔹) ⊗ₘ f) ⊗ₘ id 𝔹) ∘ₗ
                ((LinearMap.adjoint (m 𝔹) ∘ₗ Algebra.linearMap ℂ 𝔹) ⊗ₘ id 𝔹) ∘ₗ (τ⁻¹ 𝔹) :=
  by
  obtain ⟨a, b, rfl⟩ := f.exists_sum_rankOne
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, TensorProduct.sum_map,
    TensorProduct.map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [LinearEquiv.symmMap_rankOne_apply, eq_comm, LinearMap.ext_iff_inner_map]
  intro a_1
  obtain ⟨α, β, this⟩ := TensorProduct.eq_span
    (LinearMap.adjoint (LinearMap.mul' ℂ 𝔹) (1 : 𝔹))
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, lid_symm_apply, map_tmul,
    LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, one_smul]
  rw [← this]
  simp_rw [_root_.map_sum, map_tmul, LinearMap.one_apply, sum_tmul, _root_.map_sum, assoc_tmul,
    map_tmul, comm_tmul, lid_tmul, sum_inner, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, ← smul_tmul', SMulHomClass.map_smul, LinearMap.one_apply,
    Nontracial.Pi.unit_adjoint_eq, smul_eq_mul, LinearMap.mul'_apply]
  calc
    ∑ x_1, ⟪(⟪b x, β x_1⟫_ℂ * (Module.Dual.pi ψ) (a x * a_1 : 𝔹)) • α x_1, a_1⟫_ℂ =
        starRingEnd ℂ ((Module.Dual.pi ψ) (a x * a_1 : 𝔹)) *
          ∑ x_1, ⟪α x_1, a_1⟫_ℂ * ⟪β x_1, b x⟫_ℂ :=
      by
      simp_rw [inner_smul_left, _root_.map_mul, inner_conj_symm, mul_comm, Finset.mul_sum,
        mul_rotate']
    _ =
        starRingEnd ℂ (Module.Dual.pi ψ (a x * a_1)) *
          ⟪∑ x_1, α x_1 ⊗ₜ[ℂ] β x_1, a_1 ⊗ₜ[ℂ] b x⟫_ℂ :=
      by simp_rw [← inner_tmul, ← sum_inner]
    _ = starRingEnd ℂ (Module.Dual.pi ψ (a x * a_1)) * ⟪1, a_1 * b x⟫_ℂ := by
      simp_rw [this, LinearMap.adjoint_inner_left, LinearMap.mul'_apply]
    _ = ⟪⟪star (a x), a_1⟫_ℂ • Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star (b x)), a_1⟫_ℂ :=
      by
      simp_rw [Module.Dual.pi.IsFaithfulPosMap.inner_left_conj', one_mul,
        Module.Dual.pi.IsFaithfulPosMap.inner_eq, star_smul, smul_mul_assoc, SMulHomClass.map_smul,
        star_star, starRingEnd_apply, smul_eq_mul]

set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 0 in
theorem Pi.symmMap_symm_eq [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (f : (∀ i, Matrix (s i) (s i) ℂ) →ₗ[ℂ] ∀ i, Matrix (s i) (s i) ℂ) :
    (LinearEquiv.symmMap ℂ _).symm f =
      (τ 𝔹) ∘ₗ
        ((LinearMap.adjoint (η 𝔹) ∘ₗ m 𝔹) ⊗ₘ id 𝔹) ∘ₗ
          (((id 𝔹) ⊗ₘ f) ⊗ₘ id 𝔹) ∘ₗ
            (υ⁻¹𝔹) ∘ₗ ((id 𝔹) ⊗ₘ LinearMap.adjoint (m 𝔹) ∘ₗ η 𝔹) ∘ₗ (𝔹 ϰ⁻¹ ℂ) ∘ₗ τ⁻¹ 𝔹 :=
  by
  symm
  obtain ⟨a, b, rfl⟩ := f.exists_sum_rankOne
  simp only [map_sum, LinearMap.sum_comp, LinearMap.comp_sum, TensorProduct.sum_map,
    TensorProduct.map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [LinearEquiv.symmMap_symm_rankOne_apply, LinearMap.ext_iff_inner_map]
  intro x
  obtain ⟨α, β, this⟩ := TensorProduct.eq_span (LinearMap.adjoint (LinearMap.mul' ℂ 𝔹) (1 : 𝔹))
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, lid_symm_apply, comm_symm_tmul, map_tmul,
    LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, one_smul]
  rw [← this]
  simp_rw [tmul_sum, _root_.map_sum, assoc_symm_tmul, map_tmul, LinearMap.one_apply, lid_tmul,
    sum_inner, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply, ← smul_tmul, ←
    smul_tmul', SMulHomClass.map_smul, Nontracial.Pi.unit_adjoint_eq, smul_eq_mul,
    LinearMap.mul'_apply]
  calc
    ∑ x_1, inner ((inner (b p) (α x_1) * (Module.Dual.pi ψ) (x * a p)) • β x_1) x =
        starRingEnd ℂ ((Module.Dual.pi ψ) (x * a p)) *
          ∑ x_1, inner (α x_1) (b p) * inner (β x_1) x :=
      by
      simp only [inner_smul_left, _root_.map_mul, inner_conj_symm, Finset.mul_sum]
      simp_rw [mul_assoc, mul_rotate', mul_comm]
    _ =
        starRingEnd ℂ ((Module.Dual.pi ψ) (x * a p)) *
          inner (∑ x_1, α x_1 ⊗ₜ[ℂ] β x_1) (b p ⊗ₜ[ℂ] x) :=
      by simp_rw [← inner_tmul, ← sum_inner]
    _ = starRingEnd ℂ ((Module.Dual.pi ψ) (x * a p)) * inner 1 (b p * x) := by
      simp_rw [this, LinearMap.adjoint_inner_left, LinearMap.mul'_apply]
    _ = starRingEnd ℂ ((Module.Dual.pi ψ) (x * a p)) * inner (star (b p)) x := by
      rw [Module.Dual.pi.IsFaithfulPosMap.inner_right_hMul, mul_one]
    _ = starRingEnd ℂ (inner (star x) (a p)) * inner (star (b p)) x := by
      rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq (star x) (a p), star_star]
    _ =
        starRingEnd ℂ (inner (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star (a p))) x) *
          inner (star (b p)) x :=
      by rw [Pi.inner_symm, star_star]
    _ = inner (inner (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1) (star (a p))) x • star (b p)) x :=
      by rw [inner_smul_left]

theorem Pi.symmMap_tfae [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (A : 𝔹 →ₗ[ℂ] 𝔹) :
    List.TFAE
      [LinearEquiv.symmMap _ _ A = A, (LinearEquiv.symmMap _ _).symm A = A, A.real = LinearMap.adjoint A,
        ∀ x y, Module.Dual.pi ψ (A x * y) = Module.Dual.pi ψ (x * A y)] :=
  by
  tfae_have 1 ↔ 2
  · rw [← LinearEquiv.eq_symm_apply, eq_comm]
  tfae_have 2 ↔ 3
  · rw [LinearEquiv.symmMap_symm_apply, LinearMap.real_inj_eq, LinearMap.real_real, eq_comm]
  tfae_have 3 → 4
  · intro h x y
    calc
      Module.Dual.pi ψ (A x * y) = ⟪star (A x), y⟫_ℂ := by
        rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq, star_star]
      _ = ⟪A.real (star x), y⟫_ℂ := by simp_rw [LinearMap.real_apply, star_star]
      _ = ⟪LinearMap.adjoint A (star x), y⟫_ℂ := by rw [h]
      _ = ⟪star x, A y⟫_ℂ := by rw [LinearMap.adjoint_inner_left]
      _ = Module.Dual.pi ψ (x * A y) := by rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq, star_star]
  tfae_have 4 → 3
  · intro h
    rw [LinearMap.ext_iff_inner_map]
    intro u
    rw [LinearMap.adjoint_inner_left]
    nth_rw 2 [Module.Dual.pi.IsFaithfulPosMap.inner_eq]
    rw [← h, LinearMap.real_apply, Module.Dual.pi.IsFaithfulPosMap.inner_eq, star_star]
  tfae_finish

theorem commute_real_real {R A : Type _} [Semiring R] [StarRing R] [AddCommMonoid A] [Module R A]
    [StarAddMonoid A] [StarModule R A] (f g : A →ₗ[R] A) :
    Commute (f.real : A →ₗ[R] A) (g.real : A →ₗ[R] A) ↔ Commute f g := by
  simp_rw [Commute, SemiconjBy, LinearMap.mul_eq_comp, ← LinearMap.real_comp, ←
    LinearMap.real_inj_eq]

theorem Module.Dual.pi.IsFaithfulPosMap.sig_real [hψ : ∀ i, (ψ i).IsFaithfulPosMap] :
    (Module.Dual.pi.IsFaithfulPosMap.sig hψ 1).toLinearMap.real =
      (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-1)).toLinearMap :=
  by
  rw [LinearMap.ext_iff]; intro
  simp_rw [LinearMap.real_apply, AlgEquiv.toLinearMap_apply,
    Module.Dual.pi.IsFaithfulPosMap.sig_star, star_star]

theorem Pi.commute_sig_pos_neg [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (r : ℝ) (x : 𝔹 →ₗ[ℂ] 𝔹) :
    Commute x (Module.Dual.pi.IsFaithfulPosMap.sig hψ r).toLinearMap ↔
      Commute x (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-r)).toLinearMap :=
  by
  simp_rw [Commute, SemiconjBy, LinearMap.mul_eq_comp]
  rw [Pi.comp_sig_eq_iff]
  nth_rw 1 [← Pi.sig_comp_eq_iff r]
  rw [eq_comm]
  simp_rw [LinearMap.comp_assoc]

theorem Pi.symmMap_apply_eq_symmMap_symm_apply_iff [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
    (A : 𝔹 →ₗ[ℂ] 𝔹) :
    LinearEquiv.symmMap ℂ (∀ i, Matrix (s i) (s i) ℂ) A = (LinearEquiv.symmMap ℂ _).symm A ↔
      Commute A (Module.Dual.pi.IsFaithfulPosMap.sig hψ 1).toLinearMap :=
  by
  rw [LinearEquiv.symmMap_apply, LinearEquiv.symmMap_symm_apply, LinearMap.pi.adjoint_real_eq, ←
    commute_real_real, ← commute_star_star]
  simp_rw [LinearMap.star_eq_adjoint, Module.Dual.pi.IsFaithfulPosMap.sig_real,
    Module.Dual.pi.IsFaithfulPosMap.sig_adjoint, ← Pi.commute_sig_pos_neg 1]
  simp_rw [Commute, SemiconjBy, LinearMap.mul_eq_comp, Pi.comp_sig_eq_iff, LinearMap.comp_assoc]

set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 0 in
theorem Psi.real_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (r₁ r₂ : ℝ) (A : 𝔹 →ₗ[ℂ] 𝔹) :
    Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ A.real =
      ((Module.Dual.pi.IsFaithfulPosMap.sig hψ (2 * r₁)).toLinearMap ⊗ₘ
          (op ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (1 - 2 * r₂)).toLinearMap) ∘ₗ unop)
        (star (Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ A)) :=
  by
  suffices
    ∀ a b : 𝔹,
      Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ (LinearMap.real |a⟩⟨b|) =
        ((Module.Dual.pi.IsFaithfulPosMap.sig hψ (2 * r₁)).toLinearMap ⊗ₘ
            (op ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (1 - 2 * r₂)).toLinearMap) ∘ₗ unop)
          (star (Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ |a⟩⟨b|))
    by
    obtain ⟨α, β, rfl⟩ := A.exists_sum_rankOne
    letI this11 : StarAddMonoid 𝔹ᵐᵒᵖ := by infer_instance
    letI this12 : StarModule ℂ 𝔹ᵐᵒᵖ := by infer_instance
    let this1 : StarAddMonoid (𝔹 ⊗[ℂ] 𝔹ᵐᵒᵖ) := by infer_instance
    simp only [map_sum, LinearMap.real_sum, star_sum, this]
  intro a b
  simp_rw [← rankOneLm_eq_rankOne, Pi.rankOneLm_real_apply, rankOneLm_eq_rankOne,
    Module.Dual.pi.IsFaithfulPosMap.psi_apply, Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply,
    star_tmul, map_tmul, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, unop_apply, op_apply, ←
    MulOpposite.op_star, MulOpposite.unop_op, star_star, Module.Dual.pi.IsFaithfulPosMap.sig_star,
    Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig, star_star, two_mul, neg_neg, sub_eq_add_neg,
    add_assoc, neg_add, add_neg_cancel_comm_assoc, neg_add_cancel_comm, add_comm]

set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 0 in
theorem Psi.adjoint_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (r₁ r₂ : ℝ) (A : 𝔹 →ₗ[ℂ] 𝔹) :
    Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ (LinearMap.adjoint A) =
      ((Module.Dual.pi.IsFaithfulPosMap.sig hψ (r₁ - r₂)).toLinearMap ⊗ₘ
          op ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (r₁ - r₂)).toLinearMap ∘ₗ unop)
        (tenSwap (star (Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ A))) :=
  by
  suffices
    ∀ a b : 𝔹,
      Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ (LinearMap.adjoint ↑|a⟩⟨b|) =
        ((Module.Dual.pi.IsFaithfulPosMap.sig hψ (r₁ - r₂)).toLinearMap ⊗ₘ
            op ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (r₁ - r₂)).toLinearMap ∘ₗ unop)
          (tenSwap (star (Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ |a⟩⟨b|)))
    by
    obtain ⟨α, β, rfl⟩ := A.exists_sum_rankOne
    letI this11 : StarAddMonoid 𝔹ᵐᵒᵖ := by infer_instance
    letI this12 : StarModule ℂ 𝔹ᵐᵒᵖ := by infer_instance
    let this1 : StarAddMonoid (𝔹 ⊗[ℂ] 𝔹ᵐᵒᵖ) := by infer_instance
    simp only [map_sum, star_sum, this]
  intro a b
  simp_rw [← rankOneLm_eq_rankOne, rankOneLm_adjoint, rankOneLm_eq_rankOne,
    Module.Dual.pi.IsFaithfulPosMap.psi_apply, Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply,
    star_tmul, op_apply, ← MulOpposite.op_star, tenSwap_apply', star_star, map_tmul,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, unop_apply, MulOpposite.unop_op,
    Module.Dual.pi.IsFaithfulPosMap.sig_star, Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig,
    op_apply, sub_eq_add_neg, add_assoc, add_neg_cancel_comm_assoc, neg_add_self, add_zero]

theorem Psi.symmMap_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (r₁ r₂ : ℝ) (A : 𝔹 →ₗ[ℂ] 𝔹) :
    Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ (LinearEquiv.symmMap _ _ A) =
      ((Module.Dual.pi.IsFaithfulPosMap.sig hψ (r₁ + r₂ - 1)).toLinearMap ⊗ₘ
          op ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (-r₁ - r₂)).toLinearMap ∘ₗ unop)
        (tenSwap (Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ A)) :=
  by
  simp_rw [← LinearEquiv.coe_coe, ← LinearMap.comp_apply]
  revert A
  simp_rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symmMap_rankOne_apply,
    Module.Dual.pi.IsFaithfulPosMap.psi_apply, Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply,
    op_apply, tenSwap_apply', map_tmul, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    unop_apply, MulOpposite.unop_op, Module.Dual.pi.IsFaithfulPosMap.sig_star,
    Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig, star_star, op_apply, sub_eq_add_neg,
    neg_add_cancel_comm, add_assoc, add_neg_cancel_comm_assoc]

theorem Psi.symmMap_symm_apply [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (r₁ r₂ : ℝ) (A : 𝔹 →ₗ[ℂ] 𝔹) :
    Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ ((LinearEquiv.symmMap _ _).symm A) =
      ((Module.Dual.pi.IsFaithfulPosMap.sig hψ (r₁ + r₂)).toLinearMap ⊗ₘ
          op ∘ₗ (Module.Dual.pi.IsFaithfulPosMap.sig hψ (1 - r₁ - r₂)).toLinearMap ∘ₗ unop)
        (tenSwap (Module.Dual.pi.IsFaithfulPosMap.psi hψ r₁ r₂ A)) :=
  by
  simp_rw [← LinearEquiv.coe_coe, ← LinearMap.comp_apply]
  revert A
  simp_rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro a b
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symmMap_symm_rankOne_apply,
    Module.Dual.pi.IsFaithfulPosMap.psi_apply, Module.Dual.pi.IsFaithfulPosMap.psiToFun'_apply,
    op_apply, tenSwap_apply', map_tmul, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    unop_apply, MulOpposite.unop_op, Module.Dual.pi.IsFaithfulPosMap.sig_star,
    Module.Dual.pi.IsFaithfulPosMap.sig_apply_sig, star_star, op_apply, sub_eq_add_neg, add_assoc,
    neg_add_cancel_comm_assoc, add_neg_self, add_zero, neg_neg, add_comm]
