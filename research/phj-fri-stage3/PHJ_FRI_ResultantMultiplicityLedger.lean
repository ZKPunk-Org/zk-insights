import Mathlib

/-!
# Resultant-multiplicity and component-incidence ledger

This file isolates the arithmetic interface required from the missing
geometric backend.  Component pole masses may already include inseparable
image multiplicities or nonreduced quotient lengths.  Once their aggregate
masses are bounded, the proper-cut incidence ledger composes without any
coordinate-wise separability assumption.
-/

namespace PHJFRI.Stage3.ResultantMultiplicityLedger

open scoped BigOperators

/-- Componentwise box-zero/incidence estimates aggregate against total pole
    budgets.  This is the exact arithmetic shape used by the contact proof. -/
theorem aggregate_component_incidence
    {I : Type*} [Fintype I]
    (q dY dR dZ : I → ℕ)
    (gap n e cY cR cZ deltaY deltaR deltaZ : ℕ)
    (hcomponent : ∀ i,
      q i * gap ≤
        n * (cY * dY i + cR * dR i + cZ * dZ i) +
          (e + 1) * gap * dZ i)
    (hY : (∑ i, dY i) ≤ deltaY)
    (hR : (∑ i, dR i) ≤ deltaR)
    (hZ : (∑ i, dZ i) ≤ deltaZ) :
    (∑ i, q i) * gap ≤
      n * (cY * deltaY + cR * deltaR + cZ * deltaZ) +
        (e + 1) * gap * deltaZ := by
  let SY := ∑ i, dY i
  let SR := ∑ i, dR i
  let SZ := ∑ i, dZ i
  have hsum :
      (∑ i, q i * gap) ≤
        ∑ i, (n * (cY * dY i + cR * dR i + cZ * dZ i) +
          (e + 1) * gap * dZ i) :=
    Finset.sum_le_sum fun i _ => hcomponent i
  have hbox : cY * SY + cR * SR + cZ * SZ ≤
      cY * deltaY + cR * deltaR + cZ * deltaZ := by
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left cY hY) (Nat.mul_le_mul_left cR hR))
      (Nat.mul_le_mul_left cZ hZ)
  have hseed : (e + 1) * gap * SZ ≤ (e + 1) * gap * deltaZ :=
    Nat.mul_le_mul_left ((e + 1) * gap) hZ
  calc
    (∑ i, q i) * gap = ∑ i, q i * gap := by
      rw [Finset.sum_mul]
    _ ≤ ∑ i, (n * (cY * dY i + cR * dR i + cZ * dZ i) +
          (e + 1) * gap * dZ i) := hsum
    _ = n * (cY * SY + cR * SR + cZ * SZ) +
          (e + 1) * gap * SZ := by
      simp only [SY, SR, SZ, Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    _ ≤ n * (cY * deltaY + cR * deltaR + cZ * deltaZ) +
          (e + 1) * gap * deltaZ :=
      Nat.add_le_add (Nat.mul_le_mul_left n hbox) hseed

/-- A finite family of image factors, each carrying an inseparable or
    scheme-theoretic multiplicity, consumes a resultant degree budget.  This
    wrapper simply exposes the corresponding weighted pole mass. -/
theorem weighted_image_degree_le
    {I : Type*} [Fintype I]
    (multiplicity imageDegree : I → ℕ) (resultantDegree : ℕ)
    (hresultant : (∑ i, multiplicity i * imageDegree i) ≤ resultantDegree) :
    (∑ i, multiplicity i * imageDegree i) ≤ resultantDegree :=
  hresultant

/-- If every vertical component consumes at least one unit of weighted
    non-seed coordinate mass, its cardinality is charged to that mass. -/
theorem vertical_count_le_weighted_mass
    {I : Type*} [Fintype I]
    (multiplicity dY dR : I → ℕ)
    (hpositive : ∀ i, 1 ≤ multiplicity i * (dY i + dR i)) :
    Fintype.card I ≤
      (∑ i, multiplicity i * dY i) +
        ∑ i, multiplicity i * dR i := by
  calc
    Fintype.card I = ∑ _i : I, 1 := by simp
    _ ≤ ∑ i, multiplicity i * (dY i + dR i) :=
      Finset.sum_le_sum fun i _ => hpositive i
    _ = (∑ i, multiplicity i * dY i) +
        ∑ i, multiplicity i * dR i := by
      simp only [Nat.mul_add, Finset.sum_add_distrib]

/-- Horizontal proper-cut incidences plus vertical one-seed components. -/
theorem horizontal_vertical_aggregate
    (qHorizontal qVertical gap n e proper deltaY deltaR deltaZ : ℕ)
    (hHorizontal :
      qHorizontal * gap ≤ n * proper + (e + 1) * gap * deltaZ)
    (hVertical : qVertical ≤ deltaY + deltaR) :
    (qHorizontal + qVertical) * gap ≤
      n * proper + (e + 1) * gap * deltaZ +
        gap * (deltaY + deltaR) := by
  have hv : qVertical * gap ≤ (deltaY + deltaR) * gap :=
    Nat.mul_le_mul_right gap hVertical
  calc
    (qHorizontal + qVertical) * gap =
        qHorizontal * gap + qVertical * gap := by ring
    _ ≤ (n * proper + (e + 1) * gap * deltaZ) +
        (deltaY + deltaR) * gap := Nat.add_le_add hHorizontal hv
    _ = n * proper + (e + 1) * gap * deltaZ +
        gap * (deltaY + deltaR) := by ring

#print axioms aggregate_component_incidence
#print axioms weighted_image_degree_le
#print axioms vertical_count_le_weighted_mass
#print axioms horizontal_vertical_aggregate

end PHJFRI.Stage3.ResultantMultiplicityLedger
