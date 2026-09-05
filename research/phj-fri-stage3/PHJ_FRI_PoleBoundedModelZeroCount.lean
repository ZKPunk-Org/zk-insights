import ProximityPrize.SubmissionLower.CoordinateBoxZeroCount
import PHJ_FRI_PoleBoundedCoordinate

/-!
# Affine-model zero count with pole-bounded coordinates

This is the model-level replacement for the all-coordinate separable package.
The affine point-to-place map is reused verbatim.  Only one fixed separable
`RatFunc K` extension supplies the product formula; each tested coordinate is
represented by its value and a proved pole-mass budget.
-/

namespace PHJFRI.Stage3.PoleBoundedModelZeroCount

open scoped Classical BigOperators WithZero
open IsDedekindDomain

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [IsAlgClosed K]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

variable {σ : Type*} [Fintype σ]
variable (A : Type*) [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra A L] [IsFractionRing A L]
variable [Algebra (Polynomial K) A]
variable [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
variable [IsScalarTower (Polynomial K) A L]

/-- Actual affine-model K-points satisfy the sharp box count under supplied
    pole budgets.  No coordinate other than the fixed ambient separator is
    required to induce a separable rational projection. -/
theorem finite_model_zero_points_le_box
    (x : σ → A)
    (c : σ → PHJFRI.Stage3.PoleBoundedCoordinate.Coordinate K L)
    (hc : ∀ i, (c i).value = algebraMap A L (x i))
    (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (hF : MvPolynomial.eval₂Hom (algebraMap K A) x F ≠ 0)
    (S : Finset (A →ₐ[K] K))
    (hS : ∀ phi ∈ S, phi (MvPolynomial.eval₂Hom (algebraMap K A) x F) = 0) :
    (S.card : ℤ) ≤ ∑ i, (cap i : ℤ) * ((c i).degree : ℤ) := by
  classical
  have heval : MvPolynomial.eval₂Hom (algebraMap K L)
      (fun i => (c i).value) F =
        algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F) := by
    simp_rw [hc]
    exact (ProximityPrize.SubmissionLower.CoordinateBoxZeroCount.
      map_model_eval K L A x F).symm
  have hnonzero : MvPolynomial.eval₂Hom (algebraMap K L)
      (fun i => (c i).value) F ≠ 0 := by
    rw [heval]
    intro hz
    apply hF
    apply IsFractionRing.injective A L
    simpa only [map_zero] using hz
  let U := S.image
    (ProximityPrize.SubmissionLower.CoordinateBoxZeroCount.modelPlace K L A)
  have hU : ∀ v ∈ U, 1 ≤ ProximityPrize.SubmissionLower.CommonPlaceBalance.order K L v
      (MvPolynomial.eval₂Hom (algebraMap K L) (fun i => (c i).value) F) := by
    intro v hv
    obtain ⟨phi, hphi, rfl⟩ := Finset.mem_image.mp hv
    rw [heval]
    exact ProximityPrize.SubmissionLower.ActualAffineModelPlaces.
      actual_model_zero_order_ge_one K A L phi _ hF (hS phi hphi)
  have hcount := PHJFRI.Stage3.PoleBoundedCoordinate.finite_zero_places_le_box
    K L c cap F hcap hnonzero U hU
  have hcard : U.card = S.card :=
    Finset.card_image_of_injective _
      (ProximityPrize.SubmissionLower.CoordinateBoxZeroCount.
        modelPlace_injective K L A)
  rwa [hcard] at hcount

#print axioms finite_model_zero_points_le_box

end

end PHJFRI.Stage3.PoleBoundedModelZeroCount
