import Monlib.LinearAlgebra.MyTensorProduct

open scoped TensorProduct

theorem Algebra.TensorProduct.map_apply_map_apply {R : Type _} [CommSemiring R]
    {A B C D E F : Type _} [Semiring A] [Semiring B] [Semiring C] [Semiring D] [Semiring E]
    [Semiring F] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R F]
    (f : A →ₐ[R] B) (g : C →ₐ[R] D) (z : B →ₐ[R] E) (w : D →ₐ[R] F) (x : A ⊗[R] C) :
    (Algebra.TensorProduct.map z w) (Algebra.TensorProduct.map f g x) =
      Algebra.TensorProduct.map (z.comp f) (w.comp g) x :=
x.induction_on
  (map_zero _)
  (fun a b => by simp only [Algebra.TensorProduct.map_tmul]; rfl)
  (fun a b ha hb => by simp only [map_add, ha, hb])

theorem TensorProduct.map_apply_map_apply {R : Type _} [CommSemiring R] {A B C D E F : Type _}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [AddCommMonoid E]
    [AddCommMonoid F] [Module R A] [Module R B] [Module R C] [Module R D] [Module R E] [Module R F]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D) (z : B →ₗ[R] E) (w : D →ₗ[R] F) (x : A ⊗[R] C) :
    (TensorProduct.map z w) (TensorProduct.map f g x) = TensorProduct.map (z.comp f) (w.comp g) x :=
  by
  revert x
  simp_rw [← LinearMap.comp_apply, ← LinearMap.ext_iff]
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul]

noncomputable def AlgEquiv.TensorProduct.map {R : Type _} [CommSemiring R] {A B C D : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) : A ⊗[R] C ≃ₐ[R] B ⊗[R] D
    where
  toFun x := Algebra.TensorProduct.map f.toAlgHom g.toAlgHom x
  invFun x := Algebra.TensorProduct.map f.symm.toAlgHom g.symm.toAlgHom x
  left_inv x := by
    simp_rw [Algebra.TensorProduct.map_apply_map_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.symm_comp, Algebra.TensorProduct.map_id, AlgHom.id_apply]
  right_inv x := by
    simp_rw [Algebra.TensorProduct.map_apply_map_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.comp_symm, Algebra.TensorProduct.map_id, AlgHom.id_apply]
  map_add' x y := by simp_rw [map_add]
  map_mul' x y := by simp_rw [_root_.map_mul]
  commutes' r := by simp_rw [Algebra.algebraMap_eq_smul_one, _root_.map_smul, _root_.map_one]

@[simp]
lemma AlgEquiv.TensorProduct.map_tmul {R : Type _} [CommSemiring R] {A B C D : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x : A) (y : C) :
  AlgEquiv.TensorProduct.map f g (x ⊗ₜ[R] y) = f x ⊗ₜ[R] g y :=
rfl

@[simps]
noncomputable def LinearEquiv.TensorProduct.map {R : Type _} [CommSemiring R] {A B C D : Type _} [AddCommMonoid A]
    [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C]
    [Module R D] (f : A ≃ₗ[R] B) (g : C ≃ₗ[R] D) : A ⊗[R] C ≃ₗ[R] B ⊗[R] D
    where
  toFun x := _root_.TensorProduct.map (f) (g) x
  invFun x := _root_.TensorProduct.map (f.symm) (g.symm) x
  left_inv x := by
    simp_rw [TensorProduct.map_apply_map_apply, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, TensorProduct.map_id, LinearMap.id_apply]
  right_inv x := by
    simp_rw [TensorProduct.map_apply_map_apply, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, TensorProduct.map_id, LinearMap.id_apply]
  map_add' x y := by simp_rw [map_add]
  map_smul' r x := by
    simp_rw [_root_.map_smul]
    rfl


local notation
  f " ⊗ₘ " g => TensorProduct.map f g

@[simp]
lemma AlgEquiv.TensorProduct.map_toLinearMap
    {R : Type _} [CommSemiring R] {A B C D : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) :
  (AlgEquiv.TensorProduct.map f g).toLinearMap = f.toLinearMap ⊗ₘ g.toLinearMap :=
rfl
lemma AlgEquiv.TensorProduct.map_map_toLinearMap
  {R : Type _} [CommSemiring R] {A B C D E F : Type _} [Semiring A]
    [Semiring B] [Semiring C] [Semiring D] [Semiring E] [Semiring F]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R F]
    (h : B ≃ₐ[R] E) (i : D ≃ₐ[R] F) (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x : A ⊗[R] C) :
  (AlgEquiv.TensorProduct.map h i) ((AlgEquiv.TensorProduct.map f g) x)
    = (AlgEquiv.TensorProduct.map (f.trans h) (g.trans i)) x :=
by
  simp only [TensorProduct.map, toAlgHom_eq_coe, coe_mk, Algebra.TensorProduct.map_apply_map_apply]
  rfl

lemma AlgEquiv.op_trans {R A B C : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
  (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
  (AlgEquiv.op f).trans (AlgEquiv.op g) = AlgEquiv.op (f.trans g) :=
rfl
@[simp]
lemma AlgEquiv.op_one {R A : Type*} [CommSemiring R] [Semiring A]
  [Algebra R A] :
  AlgEquiv.op (1 : A ≃ₐ[R] A) = 1 :=
rfl

@[simp]
lemma AlgEquiv.TensorProduct.map_one {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] :
  AlgEquiv.TensorProduct.map (1 : A ≃ₐ[R] A) (1 : B ≃ₐ[R] B) = 1 :=
by
  rw [AlgEquiv.ext_iff]
  simp_rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.ext_iff]
  simp only [map_toLinearMap, one_toLinearMap, _root_.TensorProduct.map_one]
