import ProximityPrize.SubmissionLower.MatrixRootMultiplicity
import ProximityPrize.SubmissionLower.PlaneResultantPointCount
import PHJ_FRI_SylvesterQuotientLength

/-!
# Resultants bound arbitrary finite fiber lengths

The public backend sums Sylvester coranks to bound the number of distinct
common roots in scalar fibers.  The same argument works for any finite
K-vector-space quotient of each fiber, including nonreduced Artin algebras.
This is the scheme-length statement needed to retain purely inseparable and
nilpotent multiplicities.
-/

namespace PHJFRI.Stage3.ResultantFiberLength

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

/-- The sum of arbitrary finite target lengths over scalar fibers is bounded
    by the degree of the nonzero fixed-cap resultant. -/
theorem sum_fiber_finranks_le_resultant_natDegree
    (P Q : Polynomial (Polynomial K)) (m n : ℕ)
    (points : Finset K)
    (B : K → Type*)
    [∀ alpha, AddCommGroup (B alpha)]
    [∀ alpha, Module K (B alpha)]
    [∀ alpha, FiniteDimensional K (B alpha)]
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n)
    (hresultant : Polynomial.resultant P Q m n ≠ 0)
    (E : ∀ alpha,
      Polynomial.degreeLT K (m + n) →ₗ[K] B alpha)
    (hsurj : ∀ alpha ∈ points, Function.Surjective (E alpha))
    (hcontain : ∀ alpha ∈ points,
      LinearMap.range (Polynomial.sylvesterMap
        (P.map (Polynomial.evalRingHom alpha))
        (Q.map (Polynomial.evalRingHom alpha))
        (Polynomial.natDegree_map_le.trans hP)
        (Polynomial.natDegree_map_le.trans hQ)) ≤
      LinearMap.ker (E alpha)) :
    (∑ alpha ∈ points, Module.finrank K (B alpha)) ≤
      (Polynomial.resultant P Q m n).natDegree := by
  calc
    (∑ alpha ∈ points, Module.finrank K (B alpha)) ≤
        ∑ alpha ∈ points,
          (m + n - (Polynomial.sylvester
            (P.map (Polynomial.evalRingHom alpha))
            (Q.map (Polynomial.evalRingHom alpha)) m n).rank) := by
      apply Finset.sum_le_sum
      intro alpha halpha
      exact PHJFRI.Stage3.SylvesterQuotientLength.finrank_target_le_sylvester_corank
        (P.map (Polynomial.evalRingHom alpha))
        (Q.map (Polynomial.evalRingHom alpha)) m n
        (Polynomial.natDegree_map_le.trans hP)
        (Polynomial.natDegree_map_le.trans hQ)
        (E alpha) (hsurj alpha halpha) (hcontain alpha halpha)
    _ ≤ (Polynomial.resultant P Q m n).natDegree :=
      ProximityPrize.SubmissionLower.MatrixRootMultiplicity.
        sum_sylvester_coranks_le_resultant_natDegree
          P Q m n points hresultant

/-- Concrete mixed-bidegree corollary. -/
theorem sum_fiber_finranks_le_bidegree
    (P Q : Polynomial (Polynomial K)) (m n : ℕ)
    (points : Finset K)
    (B : K → Type*)
    [∀ alpha, AddCommGroup (B alpha)]
    [∀ alpha, Module K (B alpha)]
    [∀ alpha, FiniteDimensional K (B alpha)]
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n)
    (hresultant : Polynomial.resultant P Q m n ≠ 0)
    (E : ∀ alpha,
      Polynomial.degreeLT K (m + n) →ₗ[K] B alpha)
    (hsurj : ∀ alpha ∈ points, Function.Surjective (E alpha))
    (hcontain : ∀ alpha ∈ points,
      LinearMap.range (Polynomial.sylvesterMap
        (P.map (Polynomial.evalRingHom alpha))
        (Q.map (Polynomial.evalRingHom alpha))
        (Polynomial.natDegree_map_le.trans hP)
        (Polynomial.natDegree_map_le.trans hQ)) ≤
      LinearMap.ker (E alpha)) :
    (∑ alpha ∈ points, Module.finrank K (B alpha)) ≤
      n * Polynomial.Bivariate.degreeX P +
        m * Polynomial.Bivariate.degreeX Q := by
  exact (sum_fiber_finranks_le_resultant_natDegree
    P Q m n points B hP hQ hresultant E hsurj hcontain).trans
      (Polynomial.bivariate_resultant_natDegree_le (F := K) P Q m n)

#print axioms sum_fiber_finranks_le_resultant_natDegree
#print axioms sum_fiber_finranks_le_bidegree

end

end PHJFRI.Stage3.ResultantFiberLength
