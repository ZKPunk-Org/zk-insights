import Mathlib

/-!
# Bigraded Koszul length scaffold

This file isolates the characteristic-free linear-algebra core of the proposed
replacement for the separable-embedding proof of planar degree aggregation.

For coprime bihomogeneous equations of bidegrees `(a,b)` and `(c,d)`, the
Koszul complex in any sufficiently large bidegree has Euler characteristic
`a*d + b*c`.  Once its exactness and a surjective evaluation to a finite target
algebra are supplied, the full target length -- including inseparable and
nilpotent multiplicity -- is bounded by that mixed Bezout number.

The polynomial exactness and eventual-surjectivity inputs are deliberately
explicit: this file proves the complete dimension implication without
asserting the still-to-be-instantiated geometric statements.
-/

namespace PHJFRI.Stage3.BigradedKoszulLength

open Function

noncomputable section

variable {K H M C Q : Type*}
variable [Field K]
variable [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable [AddCommGroup C] [Module K C] [FiniteDimensional K C]
variable [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- An exact two-step Koszul presentation followed by a surjection to `Q`
    bounds `dim Q + dim M` by `dim C + dim H`.  No reducedness or separability
    hypothesis appears. -/
theorem target_finrank_add_middle_le
    (d₂ : H →ₗ[K] M) (d₁ : M →ₗ[K] C) (E : C →ₗ[K] Q)
    (hd₂inj : Function.Injective d₂)
    (hexact : LinearMap.ker d₁ = LinearMap.range d₂)
    (hcontain : LinearMap.range d₁ ≤ LinearMap.ker E)
    (hEsurj : Function.Surjective E) :
    Module.finrank K Q + Module.finrank K M ≤
      Module.finrank K C + Module.finrank K H := by
  have hd₂ker : LinearMap.ker d₂ = ⊥ := LinearMap.ker_eq_bot.mpr hd₂inj
  have hd₂rank := LinearMap.finrank_range_add_finrank_ker d₂
  have hd₁rank := LinearMap.finrank_range_add_finrank_ker d₁
  have hErank := LinearMap.finrank_range_add_finrank_ker E
  have hd₂range : Module.finrank K (LinearMap.range d₂) = Module.finrank K H := by
    rw [hd₂ker, finrank_bot, add_zero] at hd₂rank
    omega
  have hErange : Module.finrank K (LinearMap.range E) = Module.finrank K Q := by
    rw [LinearMap.range_eq_top.mpr hEsurj, finrank_top]
  have hmono : Module.finrank K (LinearMap.range d₁) ≤
      Module.finrank K (LinearMap.ker E) :=
    Submodule.finrank_mono hcontain
  rw [hexact, hd₂range] at hd₁rank
  rw [hErange] at hErank
  omega

/-- Exact Euler-characteristic identity for the large `(u,v)` component of a
    bihomogeneous Koszul complex.  We parameterize
    `u = r+a+c`, `v = s+b+d` to avoid truncated subtraction. -/
theorem bihomogeneous_euler_identity
    (r s a b c d : ℕ) :
    (r + a + c + 1) * (s + b + d + 1) + (r + 1) * (s + 1) =
      ((r + c + 1) * (s + d + 1) +
        (r + a + 1) * (s + b + 1)) +
      (a * d + b * c) := by
  ring

/-- Mixed-Bezout consequence of an exact large-bidegree Koszul presentation.

`H`, `M`, and `C` are respectively the source, middle, and target graded
pieces.  `Q` may be a product of residue fields, a purely inseparable field,
or a nonreduced Artin algebra. -/
theorem target_finrank_le_mixed_bezout
    (r s a b c d : ℕ)
    (d₂ : H →ₗ[K] M) (d₁ : M →ₗ[K] C) (E : C →ₗ[K] Q)
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
    Module.finrank K Q ≤ a * d + b * c := by
  have hlinear := target_finrank_add_middle_le d₂ d₁ E
    hd₂inj hexact hcontain hEsurj
  have heuler := bihomogeneous_euler_identity r s a b c d
  rw [hH, hM, hC] at hlinear
  omega

#print axioms target_finrank_add_middle_le
#print axioms bihomogeneous_euler_identity
#print axioms target_finrank_le_mixed_bezout

end

end PHJFRI.Stage3.BigradedKoszulLength
