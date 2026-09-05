import ProximityPrize.SubmissionLower.ActualCurveZeroCount
import ProximityPrize.SubmissionLower.ActualCurveScalarTowers
import PHJ_FRI_PoleBoundedModelZeroCount

/-!
# Actual prime-component zero count from one anchor

This theorem mirrors `ActualCurveZeroCount.finite_zero_points_le_box_of_separator`
but replaces three separately finite/separable coordinate projections by:

* one fixed finite separable anchor coordinate; and
* supplied pole-mass bounds for all coordinates in the same function field.
-/

namespace PHJFRI.Stage3.ActualCurvePoleZeroCount

open scoped Classical BigOperators
open ProximityPrize.SubmissionLower.ActualCurveCoordinateField
open ProximityPrize.SubmissionLower.ActualCurveRationalProjection
open ProximityPrize.SubmissionLower.ActualCurveScalarTowers

noncomputable section

variable (K : Type*) [Field K]
variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
variable [IsAlgClosed K]

/-- Point count on the literal prime-component coordinate ring.  The only
    separability input is for the selected anchor `i0`. -/
theorem finite_zero_points_le_box_of_anchor
    (i0 : Fin 3)
    (hi0 : Transcendental K (coordinate K P i0))
    (hfinite :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P i0 hi0
      FiniteDimensional (RatFunc K) (CoordinateField K P))
    (hseparable :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P i0 hi0
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (c : Fin 3 →
      PHJFRI.Stage3.PoleBoundedCoordinate.Coordinate K (CoordinateField K P))
    (hc : ∀ i, (c i).value = coordinate K P i)
    (F : MvPolynomial (Fin 3) K) (hF : F ∉ P)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (S : Finset (Fin 3 → K))
    (hSP : ∀ v ∈ S, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hSF : ∀ v ∈ S, MvPolynomial.aeval v F = 0) :
    (S.card : ℤ) ≤ ∑ i, (cap i : ℤ) * ((c i).degree : ℤ) := by
  classical
  letI : Algebra (Polynomial K) (CoordinateRing K P) :=
    quotientPolynomialAlgebra K P i0
  letI : Algebra (Polynomial K) (CoordinateField K P) :=
    polynomialBaseAlgebra K P i0
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    rationalBaseAlgebra K P i0 hi0
  letI := quotientBaseScalarTower K P i0
  letI := polynomialBaseScalarTower K P i0
  letI := quotientFractionScalarTower K P i0
  letI := polynomialRationalScalarTower K P i0 hi0
  letI := rationalBaseScalarTower K P i0 hi0
  letI : FiniteDimensional (RatFunc K) (CoordinateField K P) := hfinite
  letI : Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := hseparable
  have hcModel : ∀ i, (c i).value =
      algebraMap (CoordinateRing K P) (CoordinateField K P)
        (quotientCoordinate K P i) := by
    intro i
    rw [quotientCoordinate_fraction]
    exact hc i
  let liftPoint : {v : Fin 3 → K // v ∈ S} →
      (CoordinateRing K P →ₐ[K] K) :=
    fun v => ProximityPrize.SubmissionLower.ActualCurveZeroCount.pointHom K P
      ⟨v.1, hSP v.1 v.2⟩
  have hinj : Function.Injective liftPoint := by
    intro v w h
    have hvw := ProximityPrize.SubmissionLower.ActualCurveZeroCount.
      pointHom_injective K P h
    apply Subtype.ext
    exact congrArg
      (fun z : ProximityPrize.SubmissionLower.ActualCurveZeroCount.PointOn K P => z.val)
      hvw
  let points := S.attach.image liftPoint
  have hpoints : ∀ phi ∈ points, phi
      (MvPolynomial.eval₂Hom
        (algebraMap K (CoordinateRing K P)) (quotientCoordinate K P) F) = 0 := by
    intro phi hphi
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hphi
    rw [ProximityPrize.SubmissionLower.ActualCurveZeroCount.quotient_eval_eq_mk]
    exact hSF v.1 v.2
  have hnonzero := ProximityPrize.SubmissionLower.ActualCurveZeroCount.
    quotient_eval_ne_zero_of_not_mem K P F hF
  have hcount :=
    PHJFRI.Stage3.PoleBoundedModelZeroCount.finite_model_zero_points_le_box
      K (CoordinateField K P) (CoordinateRing K P)
      (quotientCoordinate K P) c hcModel cap F hcap hnonzero points hpoints
  have hcard : points.card = S.card := by
    change (S.attach.image liftPoint).card = S.card
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rwa [hcard] at hcount

#print axioms finite_zero_points_le_box_of_anchor

end

end PHJFRI.Stage3.ActualCurvePoleZeroCount
