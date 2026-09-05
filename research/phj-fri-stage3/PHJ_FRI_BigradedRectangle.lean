import Mathlib
import PHJ_FRI_BigradedKoszulLength

/-!
# Explicit bidegree rectangles

A bihomogeneous polynomial of bidegree `(u,v)` on `P¹ × P¹` has
`(u+1)(v+1)` coefficients.  We model that coefficient space by a rectangular
array and instantiate the abstract Koszul length theorem, eliminating the
three dimension equalities from the user-facing interface.
-/

namespace PHJFRI.Stage3.BigradedRectangle

open Function
open PHJFRI.Stage3.BigradedKoszulLength

noncomputable section

variable {K Q : Type*} [Field K]
variable [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- Coefficient rectangle for bidegree `(u,v)`. -/
abbrev Rect (K : Type*) [Field K] (u v : ℕ) :=
  Fin (u + 1) → Fin (v + 1) → K

@[simp] theorem rect_finrank (u v : ℕ) :
    Module.finrank K (Rect K u v) = (u + 1) * (v + 1) := by
  simp [Rect]

/-- The middle term of the large-bidegree two-generator Koszul complex. -/
abbrev Middle (K : Type*) [Field K]
    (r s a b c d : ℕ) :=
  Rect K (r + c) (s + d) × Rect K (r + a) (s + b)

@[simp] theorem middle_finrank (r s a b c d : ℕ) :
    Module.finrank K (Middle K r s a b c d) =
      (r + c + 1) * (s + d + 1) +
        (r + a + 1) * (s + b + 1) := by
  simp [Middle, Rect]

/-- Explicit-rectangle form of the characteristic-free mixed-length theorem. -/
theorem target_finrank_le_mixed_bezout_rect
    (r s a b c d : ℕ)
    (d₂ : Rect K r s →ₗ[K] Middle K r s a b c d)
    (d₁ : Middle K r s a b c d →ₗ[K]
      Rect K (r + a + c) (s + b + d))
    (E : Rect K (r + a + c) (s + b + d) →ₗ[K] Q)
    (hd₂inj : Function.Injective d₂)
    (hexact : LinearMap.ker d₁ = LinearMap.range d₂)
    (hcontain : LinearMap.range d₁ ≤ LinearMap.ker E)
    (hEsurj : Function.Surjective E) :
    Module.finrank K Q ≤ a * d + b * c := by
  apply target_finrank_le_mixed_bezout
    (K := K) (H := Rect K r s)
    (M := Middle K r s a b c d)
    (C := Rect K (r + a + c) (s + b + d))
    r s a b c d d₂ d₁ E hd₂inj hexact hcontain hEsurj
  · simp [Rect]
  · simp [Middle, Rect]
  · simp [Rect]

#print axioms rect_finrank
#print axioms middle_finrank
#print axioms target_finrank_le_mixed_bezout_rect

end

end PHJFRI.Stage3.BigradedRectangle
