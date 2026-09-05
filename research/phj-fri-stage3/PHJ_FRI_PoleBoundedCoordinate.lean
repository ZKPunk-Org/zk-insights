import ProximityPrize.SubmissionLower.CoordinateBoxZeroCount

/-!
# Pole-bounded coordinates

This is the minimal replacement interface for the current all-coordinate
separability backend.  A coordinate carries its actual value, an integer
projection-degree budget, and the one theorem needed by the common-place
product formula: every finite common-place pole sum is bounded by that budget.
No separability field is stored.
-/

namespace PHJFRI.Stage3.PoleBoundedCoordinate

open scoped Classical BigOperators WithZero
open IsDedekindDomain

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

abbrev Place := CoordinatePlaceClassification.NormalizedValuation K L

structure Coordinate where
  value : L
  degree : ℕ
  pole_le_degree : ∀ W : Finset (Place K L),
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v value) ≤ (degree : ℤ)

variable [IsAlgClosed K]
variable {σ : Type*} [Fintype σ]

/-- The local box inequality plus supplied actual coordinate pole theorems
    yields the same sharp weighted box budget as the old separable-coordinate
    package. -/
theorem finite_sum_polynomial_pole_le_box
    (W : Finset (Place K L)) (c : σ → Coordinate K L)
    (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i) :
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v
      (MvPolynomial.eval₂Hom (algebraMap K L) (fun i => (c i).value) F)) ≤
      ∑ i, (cap i : ℤ) * ((c i).degree : ℤ) := by
  have hlocal := ContactLocalPoleBound.weighted_poleOrder_eval_le_box
    W (fun _ => 1) (fun v => v.val) (algebraMap K L)
    (fun v _ a => CoordinateBoxZeroCount.constant_value_le_one K L v a)
    (fun i => (c i).value) cap F hcap
  simp only [Nat.cast_one, one_mul] at hlocal
  calc
    _ ≤ ∑ i, (cap i : ℤ) *
        ∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (c i).value := hlocal
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left ((c i).pole_le_degree W)
        (Int.natCast_nonneg _)

section FixedSeparator

variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

/-- Characteristic-free analytic zero count, conditional only on actual pole
    budgets.  One fixed separable seed coordinate supplies the common product
    formula; the tested coordinates themselves need not be separable. -/
theorem finite_zero_places_le_box
    (c : σ → Coordinate K L) (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (hF : MvPolynomial.eval₂Hom (algebraMap K L) (fun i => (c i).value) F ≠ 0)
    (U : Finset (Place K L))
    (hU : ∀ v ∈ U, 1 ≤ CommonPlaceBalance.order K L v
      (MvPolynomial.eval₂Hom (algebraMap K L) (fun i => (c i).value) F)) :
    (U.card : ℤ) ≤ ∑ i, (cap i : ℤ) * ((c i).degree : ℤ) := by
  exact (CommonPlaceBalance.finite_zero_places_le_poleMass K L _ hF U hU).trans
    (finite_sum_polynomial_pole_le_box K L _ c cap F hcap)

end FixedSeparator

#print axioms finite_sum_polynomial_pole_le_box
#print axioms finite_zero_places_le_box

end

end PHJFRI.Stage3.PoleBoundedCoordinate
