import Mathlib

/-!
# Trigraded Koszul length

For three hypersurfaces on `(P¹)^3`, a proper complete intersection is
resolved by the three-generator Koszul complex.  In a sufficiently large
tridegree its Euler characteristic is the six-term mixed permanent

`g₁*t₂*c₃ + g₁*t₃*c₂ + g₂*t₁*c₃ + g₂*t₃*c₁ + g₃*t₁*c₂ + g₃*t₂*c₁`.

This is exactly the contact-ledger expression
`c₁ Δ₁ + c₂ Δ₂ + c₃ Δ₃`.  The argument uses vector-space length, so it
counts inseparable and nilpotent intersection multiplicity.
-/

namespace PHJFRI.Stage3.TrigradedKoszulLength

open Function

noncomputable section

variable {K H3 H2 H1 H0 Q : Type*} [Field K]
variable [AddCommGroup H3] [Module K H3] [FiniteDimensional K H3]
variable [AddCommGroup H2] [Module K H2] [FiniteDimensional K H2]
variable [AddCommGroup H1] [Module K H1] [FiniteDimensional K H1]
variable [AddCommGroup H0] [Module K H0] [FiniteDimensional K H0]
variable [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- Six-term mixed intersection number for three multidegrees on `(P¹)^3`. -/
def mixed3
    (g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ) : ℕ :=
  g1 * t2 * c3 + g1 * t3 * c2 +
  g2 * t1 * c3 + g2 * t3 * c1 +
  g3 * t1 * c2 + g3 * t2 * c1

/-- Dimension inequality extracted from an exact three-generator Koszul
    complex followed by a surjection to a finite target. -/
theorem target_finrank_le_three_generator_euler
    (d3 : H3 →ₗ[K] H2) (d2 : H2 →ₗ[K] H1)
    (d1 : H1 →ₗ[K] H0) (E : H0 →ₗ[K] Q)
    (hd3inj : Function.Injective d3)
    (hexact2 : LinearMap.ker d2 = LinearMap.range d3)
    (hexact1 : LinearMap.ker d1 = LinearMap.range d2)
    (hcontain : LinearMap.range d1 ≤ LinearMap.ker E)
    (hEsurj : Function.Surjective E) :
    Module.finrank K Q + Module.finrank K H1 + Module.finrank K H3 ≤
      Module.finrank K H0 + Module.finrank K H2 := by
  have hd3ker : LinearMap.ker d3 = ⊥ := LinearMap.ker_eq_bot.mpr hd3inj
  have hd3rank := LinearMap.finrank_range_add_finrank_ker d3
  have hd2rank := LinearMap.finrank_range_add_finrank_ker d2
  have hd1rank := LinearMap.finrank_range_add_finrank_ker d1
  have hErank := LinearMap.finrank_range_add_finrank_ker E
  have hd3range : Module.finrank K (LinearMap.range d3) =
      Module.finrank K H3 := by
    rw [hd3ker, finrank_bot, add_zero] at hd3rank
    omega
  have hErange : Module.finrank K (LinearMap.range E) =
      Module.finrank K Q := by
    rw [LinearMap.range_eq_top.mpr hEsurj, finrank_top]
  have hmono : Module.finrank K (LinearMap.range d1) ≤
      Module.finrank K (LinearMap.ker E) :=
    Submodule.finrank_mono hcontain
  rw [hexact2, hd3range] at hd2rank
  rw [hexact1] at hd1rank
  rw [hErange] at hErank
  omega

/-- Trigraded Hilbert-function identity.  The base tridegree is `(r1,r2,r3)`
    and the three equation multidegrees are `g`, `t`, and `c`. -/
theorem trihomogeneous_euler_identity
    (r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ) :
    ((r1 + g1 + t1 + c1 + 1) *
       (r2 + g2 + t2 + c2 + 1) *
       (r3 + g3 + t3 + c3 + 1)) +
    (((r1 + c1 + 1) * (r2 + c2 + 1) * (r3 + c3 + 1)) +
     ((r1 + t1 + 1) * (r2 + t2 + 1) * (r3 + t3 + 1)) +
     ((r1 + g1 + 1) * (r2 + g2 + 1) * (r3 + g3 + 1))) =
    (((r1 + t1 + c1 + 1) * (r2 + t2 + c2 + 1) *
       (r3 + t3 + c3 + 1)) +
     ((r1 + g1 + c1 + 1) * (r2 + g2 + c2 + 1) *
       (r3 + g3 + c3 + 1)) +
     ((r1 + g1 + t1 + 1) * (r2 + g2 + t2 + 1) *
       (r3 + g3 + t3 + 1))) +
    ((r1 + 1) * (r2 + 1) * (r3 + 1)) +
    mixed3 g1 g2 g3 t1 t2 t3 c1 c2 c3 := by
  simp only [mixed3]
  ring

/-- Characteristic-free mixed-length consequence of the trigraded Koszul
    complex.  The four dimension hypotheses are the large-tridegree Hilbert
    functions of the four Koszul terms. -/
theorem target_finrank_le_mixed3
    (r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ)
    (d3 : H3 →ₗ[K] H2) (d2 : H2 →ₗ[K] H1)
    (d1 : H1 →ₗ[K] H0) (E : H0 →ₗ[K] Q)
    (hd3inj : Function.Injective d3)
    (hexact2 : LinearMap.ker d2 = LinearMap.range d3)
    (hexact1 : LinearMap.ker d1 = LinearMap.range d2)
    (hcontain : LinearMap.range d1 ≤ LinearMap.ker E)
    (hEsurj : Function.Surjective E)
    (hH3 : Module.finrank K H3 =
      (r1 + 1) * (r2 + 1) * (r3 + 1))
    (hH2 : Module.finrank K H2 =
      (r1 + c1 + 1) * (r2 + c2 + 1) * (r3 + c3 + 1) +
      (r1 + t1 + 1) * (r2 + t2 + 1) * (r3 + t3 + 1) +
      (r1 + g1 + 1) * (r2 + g2 + 1) * (r3 + g3 + 1))
    (hH1 : Module.finrank K H1 =
      (r1 + t1 + c1 + 1) * (r2 + t2 + c2 + 1) *
        (r3 + t3 + c3 + 1) +
      (r1 + g1 + c1 + 1) * (r2 + g2 + c2 + 1) *
        (r3 + g3 + c3 + 1) +
      (r1 + g1 + t1 + 1) * (r2 + g2 + t2 + 1) *
        (r3 + g3 + t3 + 1))
    (hH0 : Module.finrank K H0 =
      (r1 + g1 + t1 + c1 + 1) *
      (r2 + g2 + t2 + c2 + 1) *
      (r3 + g3 + t3 + c3 + 1)) :
    Module.finrank K Q ≤ mixed3 g1 g2 g3 t1 t2 t3 c1 c2 c3 := by
  have hlinear := target_finrank_le_three_generator_euler
    d3 d2 d1 E hd3inj hexact2 hexact1 hcontain hEsurj
  have heuler := trihomogeneous_euler_identity
    r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3
  rw [hH3, hH2, hH1, hH0] at hlinear
  omega

/-- The six-term permanent equals the contact-ledger dot product
    `c1*Δ1+c2*Δ2+c3*Δ3`. -/
theorem mixed3_eq_coordinate_ledger
    (g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ) :
    mixed3 g1 g2 g3 t1 t2 t3 c1 c2 c3 =
      c1 * (g2 * t3 + g3 * t2) +
      c2 * (g1 * t3 + g3 * t1) +
      c3 * (g1 * t2 + g2 * t1) := by
  simp only [mixed3]
  ring

#print axioms mixed3
#print axioms target_finrank_le_three_generator_euler
#print axioms trihomogeneous_euler_identity
#print axioms target_finrank_le_mixed3
#print axioms mixed3_eq_coordinate_ledger

end

end PHJFRI.Stage3.TrigradedKoszulLength
