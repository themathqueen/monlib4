import Monlib.LinearAlgebra.MyMatrix.Basic

#align_import preq.equiv

theorem Equiv.Perm.ToPequiv.toMatrix_mem_unitaryGroup {n : Type _} [DecidableEq n] [Fintype n]
    {𝕜 : Type _} [CommRing 𝕜] [StarRing 𝕜] (σ : Equiv.Perm n) :
    (Equiv.toPEquiv σ).toMatrix ∈ Matrix.unitaryGroup n 𝕜 :=
  by
  simp_rw [Matrix.mem_unitaryGroup_iff, ← Matrix.ext_iff, Matrix.mul_apply,
    PEquiv.toMatrix_apply, boole_mul, Equiv.toPEquiv_apply, Matrix.one_apply, Option.mem_def,
    Matrix.star_apply, PEquiv.toMatrix_apply, star_ite, star_one, star_zero,
    Option.some.injEq, Option.mem_def, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  intro i j
  simp_rw [Equiv.toPEquiv_apply, Option.some.injEq,
    Function.Injective.eq_iff (Equiv.injective _), eq_comm]
