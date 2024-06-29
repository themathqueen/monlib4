import Mathlib.Data.Matrix.Basic

abbrev PiMat (R k : Type*) (s : k → Type*) := Π i, Matrix (s i) (s i) R

@[ext]
theorem PiMat.ext {R k : Type*} {s : k → Type*} {x y : PiMat R k s} (h : ∀ i, x i = y i) : x = y :=
  funext h
