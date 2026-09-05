import Mathlib
import PHJ_FRI_BigradedKoszulLength

/-!
# Generic-fiber mixed-degree bridge

After choosing one coordinate as a transcendental base, every horizontal
irreducible curve component becomes a closed point of a two-variable generic
fiber.  Its residue field may be inseparable.  Mapping a sufficiently large
bihomogeneous piece onto the product of all residue fields and applying the
Koszul Euler characteristic bounds the sum of the *full* residue degrees.

This file formalizes the final linear-algebra bridge.  It deliberately treats
the construction of the Koszul maps and the large-bidegree evaluation map as
explicit inputs, so no geometric assertion is hidden in the statement.
-/

namespace PHJFRI.Stage3.GenericFiberMixedDegree

open Function
open PHJFRI.Stage3.BigradedKoszulLength

noncomputable section

variable {K H M C : Type*} [Field K]
variable [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable [AddCommGroup C] [Module K C] [FiniteDimensional K C]

variable {ι : Type*} [Fintype ι]
variable (L : ι → Type*)
variable [∀ i, AddCommGroup (L i)]
variable [∀ i, Module K (L i)]
variable [∀ i, FiniteDimensional K (L i)]

/-- A bihomogeneous Koszul presentation that evaluates surjectively to the
    product of generic-fiber residue fields bounds the sum of their complete
    extension degrees by the mixed Bezout number.  Purely inseparable degrees
    are included because `Module.finrank`, not embedding count, is used. -/
theorem sum_residue_finrank_le_mixed_bezout
    (r s a b c d : ℕ)
    (d₂ : H →ₗ[K] M) (d₁ : M →ₗ[K] C)
    (E : C →ₗ[K] ((i : ι) → L i))
    (hd₂inj : Function.Injective d₂)
    (hexact : LinearMap.ker d₁ = LinearMap.range d₂)
    (hcontain : LinearMap.range d₁ ≤ LinearMap.ker E)
    (hEsurj : Function.Surjective E)
    (hH : Module.finrank K H = (r + 1) * (s + 1))
    (hM : Module.finrank K M =
      (r + c + 1) * (s + d + 1) +
        (r + a + 1) * (s + b + 1))
    (hC : Module.finrank K C =
      (r + a + c + 1) * (s + b + d + 1)) :
    (∑ i, Module.finrank K (L i)) ≤ a * d + b * c := by
  have h := target_finrank_le_mixed_bezout
    (K := K) (Q := ((i : ι) → L i))
    r s a b c d d₂ d₁ E hd₂inj hexact hcontain hEsurj hH hM hC
  simpa using h

/-- Coordinate-free restatement with a named mixed-degree budget. -/
theorem sum_residue_finrank_le_budget
    (r s a b c d budget : ℕ)
    (d₂ : H →ₗ[K] M) (d₁ : M →ₗ[K] C)
    (E : C →ₗ[K] ((i : ι) → L i))
    (hd₂inj : Function.Injective d₂)
    (hexact : LinearMap.ker d₁ = LinearMap.range d₂)
    (hcontain : LinearMap.range d₁ ≤ LinearMap.ker E)
    (hEsurj : Function.Surjective E)
    (hH : Module.finrank K H = (r + 1) * (s + 1))
    (hM : Module.finrank K M =
      (r + c + 1) * (s + d + 1) +
        (r + a + 1) * (s + b + 1))
    (hC : Module.finrank K C =
      (r + a + c + 1) * (s + b + d + 1))
    (hmixed : a * d + b * c ≤ budget) :
    (∑ i, Module.finrank K (L i)) ≤ budget := by
  exact (sum_residue_finrank_le_mixed_bezout
    (K := K) L r s a b c d d₂ d₁ E hd₂inj hexact hcontain hEsurj hH hM hC).trans hmixed

#print axioms sum_residue_finrank_le_mixed_bezout
#print axioms sum_residue_finrank_le_budget

end

end PHJFRI.Stage3.GenericFiberMixedDegree
