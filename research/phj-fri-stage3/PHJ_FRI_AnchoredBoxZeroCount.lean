import ProximityPrize.SubmissionLower.CoordinateBoxZeroCount

/-!
# One-anchor zero counts from supplied pole budgets

The original Proximity Prize backend packages every nonconstant coordinate as
its own finite separable rational-function extension.  For PHJ-FRI we only
need one fixed finite separable seed extension to obtain the product formula.
The other coordinates may be arbitrary elements of the same function field;
their pole masses are supplied by a separate geometric theorem.

This file proves that analytic separation cleanly: no `Y`- or `R`-projection
separability is used below.
-/

namespace PHJFRI.Stage3.AnchoredBoxZeroCount

open scoped Classical BigOperators WithZero
open IsDedekindDomain

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [IsAlgClosed K]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

abbrev Place := CoordinatePlaceClassification.NormalizedValuation K L

variable {σ : Type*} [Fintype σ]

/-- A box polynomial has at most the supplied weighted coordinate pole mass
    many distinct affine zero places.  The product formula uses only the one
    fixed `RatFunc K` algebra already present in the ambient instances. -/
theorem finite_zero_places_le_supplied_box
    (x : σ → L) (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (hF : MvPolynomial.eval₂Hom (algebraMap K L) x F ≠ 0)
    (U : Finset (Place K L))
    (hU : ∀ v ∈ U, 1 ≤ CommonPlaceBalance.order K L v
      (MvPolynomial.eval₂Hom (algebraMap K L) x F))
    (budget : σ → ℤ)
    (hpole : ∀ i,
      (∑ v ∈ CommonPlaceBalance.placesFor K L
          (MvPolynomial.eval₂Hom (algebraMap K L) x F) hF,
        CoordinatePoleMass.poleOrder K L v (x i)) ≤ budget i) :
    (U.card : ℤ) ≤ ∑ i, (cap i : ℤ) * budget i := by
  let value := MvPolynomial.eval₂Hom (algebraMap K L) x F
  let W := CommonPlaceBalance.placesFor K L value hF
  have hzero : (U.card : ℤ) ≤
      ∑ v ∈ W, CoordinatePoleMass.poleOrder K L v value :=
    CommonPlaceBalance.finite_zero_places_le_poleMass K L value hF U hU
  have hlocal0 := ContactLocalPoleBound.weighted_poleOrder_eval_le_box
    (K := K) (L := L) W (fun _ => 1) (fun v => v.val)
      (algebraMap K L)
      (fun v _ a => CoordinateBoxZeroCount.constant_value_le_one K L v a)
      x cap F hcap
  have hlocal :
      (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v value) ≤
        ∑ i, (cap i : ℤ) *
          (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (x i)) := by
    simpa only [Nat.cast_one, one_mul, value, W,
      CoordinatePoleMass.poleOrder] using hlocal0
  have hbudget :
      (∑ i, (cap i : ℤ) *
        (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (x i))) ≤
        ∑ i, (cap i : ℤ) * budget i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (by simpa only [W] using hpole i)
      (Int.natCast_nonneg _)
  exact hzero.trans (hlocal.trans hbudget)

#print axioms finite_zero_places_le_supplied_box

end

end PHJFRI.Stage3.AnchoredBoxZeroCount
