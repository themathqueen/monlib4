import Monlib.LinearAlgebra.TensorFinite
import Monlib.LinearAlgebra.Ips.TensorHilbert

variable  {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

open scoped TensorProduct
noncomputable def OrthonormalBasis.tensorProduct
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ × ι₂) 𝕜 (E ⊗[𝕜] F) :=
by
  refine (b₁.toBasis.tensorProduct b₂.toBasis).toOrthonormalBasis
    (orthonormal_iff_ite.mpr ?_)
  rintro ⟨i1,i2⟩ ⟨j1,j2⟩
  simp only [Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis, TensorProduct.inner_tmul,
    Prod.mk.injEq, ← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_self]
  simp only [EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero, ← ite_and, and_comm]

@[simp]
lemma OrthonormalBasis.tensorProduct_apply
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
  (i : ι₁) (j : ι₂) :
  b₁.tensorProduct b₂ (i,j) = b₁ i ⊗ₜ[𝕜] b₂ j :=
by
  simp only [OrthonormalBasis.tensorProduct, Basis.coe_toOrthonormalBasis,
    Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis]

lemma OrthonormalBasis.tensorProduct_apply'
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
  (i : ι₁ × ι₂) :
  b₁.tensorProduct b₂ i = b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 :=
OrthonormalBasis.tensorProduct_apply _ _ _ _

@[simp]
lemma OrthonormalBasis.tensorProduct_repr_tmul_apply
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
  (x : E) (y : F) (i : ι₁) (j : ι₂) :
  ((b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y)) (i, j) = (b₁.repr x i) * (b₂.repr y j) :=
by
  simp only [tensorProduct, Basis.coe_toOrthonormalBasis_repr, Basis.equivFun_apply,
    Basis.tensorProduct_repr_tmul_apply, OrthonormalBasis.coe_toBasis_repr_apply]

lemma OrthonormalBasis.tensorProduct_repr_tmul_apply'
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
  (x : E) (y : F) (i : ι₁ × ι₂) :
  ((b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y)) i = (b₁.repr x i.1) * (b₂.repr y i.2) :=
tensorProduct_repr_tmul_apply _ _ _ _ _ _
