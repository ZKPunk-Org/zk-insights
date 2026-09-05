import Mathlib

/-!
# Aggregate prime-component seed incidence

This file closes the finite-sum bookkeeping after the geometric backend has
supplied aggregate coordinate pole budgets.  It is deliberately independent
of the construction of those budgets.
-/

namespace PHJFRI.Stage3.AggregatePrimeSeedIncidence

open scoped BigOperators

/-- Summing the per-prime contact-incidence inequalities preserves the sharp
    mixed box cost. -/
theorem aggregate_horizontal_seed_bound
    {I : Type*} [Fintype I]
    (q dY dR dZ : I → ℕ)
    (gap n e capY capR capZ deltaY deltaR deltaZ : ℕ)
    (hlocal : ∀ i,
      q i * gap ≤
        n * (capY * dY i + capR * dR i + capZ * dZ i) +
          (e + 1) * gap * dZ i)
    (hY : (∑ i, dY i) ≤ deltaY)
    (hR : (∑ i, dR i) ≤ deltaR)
    (hZ : (∑ i, dZ i) ≤ deltaZ) :
    (∑ i, q i) * gap ≤
      n * (capY * deltaY + capR * deltaR + capZ * deltaZ) +
        (e + 1) * gap * deltaZ := by
  have hsum :
      (∑ i, q i * gap) ≤
        ∑ i,
          (n * (capY * dY i + capR * dR i + capZ * dZ i) +
            (e + 1) * gap * dZ i) :=
    Finset.sum_le_sum fun i _ => hlocal i
  have hcost :
      (∑ i, capY * dY i + capR * dR i + capZ * dZ i) ≤
        capY * deltaY + capR * deltaR + capZ * deltaZ := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [← Finset.mul_sum]
    exact Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left capY hY)
      (Nat.mul_le_mul_left capR hR))
      (Nat.mul_le_mul_left capZ hZ)
  calc
    (∑ i, q i) * gap = ∑ i, q i * gap := by rw [Finset.sum_mul]
    _ ≤ ∑ i,
        (n * (capY * dY i + capR * dR i + capZ * dZ i) +
          (e + 1) * gap * dZ i) := hsum
    _ = n * (∑ i, capY * dY i + capR * dR i + capZ * dZ i) +
        (e + 1) * gap * (∑ i, dZ i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ n * (capY * deltaY + capR * deltaR + capZ * deltaZ) +
        (e + 1) * gap * deltaZ :=
      Nat.add_le_add (Nat.mul_le_mul_left n hcost)
        (Nat.mul_le_mul_left ((e + 1) * gap) hZ)

/-- Adding vertical components costs only their number times one seed, and the
    number of such components is charged to aggregate `Y+R` mass. -/
theorem aggregate_all_components_bound
    (qHorizontal qVertical gap n e proper deltaY deltaR deltaZ : ℕ)
    (hHorizontal :
      qHorizontal * gap ≤
        n * proper + (e + 1) * gap * deltaZ)
    (hVertical : qVertical ≤ deltaY + deltaR) :
    (qHorizontal + qVertical) * gap ≤
      n * proper + (e + 1) * gap * deltaZ +
        gap * (deltaY + deltaR) := by
  have hv := Nat.mul_le_mul_right gap hVertical
  calc
    (qHorizontal + qVertical) * gap =
        qHorizontal * gap + qVertical * gap := by ring
    _ ≤ (n * proper + (e + 1) * gap * deltaZ) +
        (deltaY + deltaR) * gap := Nat.add_le_add hHorizontal hv
    _ = n * proper + (e + 1) * gap * deltaZ +
        gap * (deltaY + deltaR) := by ring

#print axioms aggregate_horizontal_seed_bound
#print axioms aggregate_all_components_bound

end PHJFRI.Stage3.AggregatePrimeSeedIncidence
