import Mathlib
import PHJ_FRI_TrigradedKoszulLength

/-!
# Inseparable pole-budget aggregation

For a proper normal curve and a nonconstant coordinate `x`, the degree of the
pole divisor of `x` is the full function-field degree `[K(C):K(x)]`, including
inseparable degree.  The geometric construction of that identity is kept as
an explicit per-component hypothesis here.  This file proves the complete
aggregate ledger used by hidden-jet contact counting.
-/

namespace PHJFRI.Stage3.InseparablePoleAggregation

open BigOperators
open PHJFRI.Stage3.TrigradedKoszulLength

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise pole mass is bounded by the corresponding full extension
    degree, hence any aggregate extension-degree bound transfers to poles. -/
theorem sum_pole_le_of_component_degree
    (pole degree : ι → ℕ)
    (hlocal : ∀ i, pole i ≤ degree i)
    (budget : ℕ)
    (hdegree : (∑ i, degree i) ≤ budget) :
    (∑ i, pole i) ≤ budget := by
  exact (Finset.sum_le_sum fun i _ => hlocal i).trans hdegree

/-- Three coordinate-degree budgets imply the exact box-weighted pole ledger. -/
theorem aggregate_box_pole_cost_le
    (pole1 pole2 pole3 degree1 degree2 degree3 : ι → ℕ)
    (c1 c2 c3 delta1 delta2 delta3 : ℕ)
    (hpole1 : ∀ i, pole1 i ≤ degree1 i)
    (hpole2 : ∀ i, pole2 i ≤ degree2 i)
    (hpole3 : ∀ i, pole3 i ≤ degree3 i)
    (hdegree1 : (∑ i, degree1 i) ≤ delta1)
    (hdegree2 : (∑ i, degree2 i) ≤ delta2)
    (hdegree3 : (∑ i, degree3 i) ≤ delta3) :
    (∑ i, (c1 * pole1 i + c2 * pole2 i + c3 * pole3 i)) ≤
      c1 * delta1 + c2 * delta2 + c3 * delta3 := by
  have h1 : (∑ i, pole1 i) ≤ delta1 :=
    sum_pole_le_of_component_degree pole1 degree1 hpole1 delta1 hdegree1
  have h2 : (∑ i, pole2 i) ≤ delta2 :=
    sum_pole_le_of_component_degree pole2 degree2 hpole2 delta2 hdegree2
  have h3 : (∑ i, pole3 i) ≤ delta3 :=
    sum_pole_le_of_component_degree pole3 degree3 hpole3 delta3 hdegree3
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  omega

/-- Substituting the three generic-fiber mixed-degree bounds recovers exactly
    the six-term contact mixed permanent. -/
theorem aggregate_box_pole_cost_le_mixed3
    (pole1 pole2 pole3 degree1 degree2 degree3 : ι → ℕ)
    (g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ)
    (hpole1 : ∀ i, pole1 i ≤ degree1 i)
    (hpole2 : ∀ i, pole2 i ≤ degree2 i)
    (hpole3 : ∀ i, pole3 i ≤ degree3 i)
    (hdegree1 : (∑ i, degree1 i) ≤ g2 * t3 + g3 * t2)
    (hdegree2 : (∑ i, degree2 i) ≤ g1 * t3 + g3 * t1)
    (hdegree3 : (∑ i, degree3 i) ≤ g1 * t2 + g2 * t1) :
    (∑ i, (c1 * pole1 i + c2 * pole2 i + c3 * pole3 i)) ≤
      mixed3 g1 g2 g3 t1 t2 t3 c1 c2 c3 := by
  rw [mixed3_eq_coordinate_ledger]
  exact aggregate_box_pole_cost_le
    pole1 pole2 pole3 degree1 degree2 degree3
    c1 c2 c3
    (g2 * t3 + g3 * t2)
    (g1 * t3 + g3 * t1)
    (g1 * t2 + g2 * t1)
    hpole1 hpole2 hpole3 hdegree1 hdegree2 hdegree3

#print axioms sum_pole_le_of_component_degree
#print axioms aggregate_box_pole_cost_le
#print axioms aggregate_box_pole_cost_le_mixed3

end

end PHJFRI.Stage3.InseparablePoleAggregation
