import Mathlib
import PHJ_FRI_BigradedRectangle

/-!
# Generic-fiber residue fields from explicit bidegree rectangles

This is the tightest abstract interface before constructing actual polynomial
multiplication and evaluation maps.  The finite target is the product of all
selected generic-fiber residue fields, so its `K`-dimension is the sum of the
full residue degrees, including inseparable degree.
-/

namespace PHJFRI.Stage3.GenericFiberRectangle

open Function
open PHJFRI.Stage3.BigradedRectangle

noncomputable section

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι]
variable (L : ι → Type*)
variable [∀ i, AddCommGroup (L i)]
variable [∀ i, Module K (L i)]
variable [∀ i, FiniteDimensional K (L i)]

/-- Explicit-rectangle generic-fiber mixed-degree theorem. -/
theorem sum_residue_finrank_le_mixed_rect
    (r s a b c d : ℕ)
    (d₂ : Rect K r s →ₗ[K] Middle K r s a b c d)
    (d₁ : Middle K r s a b c d →ₗ[K]
      Rect K (r + a + c) (s + b + d))
    (E : Rect K (r + a + c) (s + b + d) →ₗ[K]
      ((i : ι) → L i))
    (hd₂inj : Function.Injective d₂)
    (hexact : LinearMap.ker d₁ = LinearMap.range d₂)
    (hcontain : LinearMap.range d₁ ≤ LinearMap.ker E)
    (hEsurj : Function.Surjective E) :
    (∑ i, Module.finrank K (L i)) ≤ a * d + b * c := by
  have h := target_finrank_le_mixed_bezout_rect
    (K := K) (Q := ((i : ι) → L i))
    r s a b c d d₂ d₁ E hd₂inj hexact hcontain hEsurj
  simpa using h

#print axioms sum_residue_finrank_le_mixed_rect

end

end PHJFRI.Stage3.GenericFiberRectangle
