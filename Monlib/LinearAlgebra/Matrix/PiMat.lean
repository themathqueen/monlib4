import Mathlib.Data.Matrix.Basic

abbrev Mat (R n : Type*) := Matrix n n R

abbrev PiMat (R k : Type*) (s : k → Type*) :=
Π i, (fun j => Mat R (s j)) i

@[ext]
theorem PiMat.ext {R k : Type*} {s : k → Type*} {x y : PiMat R k s} (h : ∀ i, x i = y i) : x = y :=
  funext h
