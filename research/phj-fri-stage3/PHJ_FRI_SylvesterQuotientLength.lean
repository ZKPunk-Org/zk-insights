import ProximityPrize.SubmissionLower.PlaneResultantPointCount

/-!
# Sylvester corank controls arbitrary quotient length

The existing resultant backend injects distinct point-evaluation functionals
into the Sylvester cokernel.  Purely inseparable branches instead produce a
nonreduced finite algebra.  The same linear algebra controls its full vector-
space length, provided the bounded polynomial space surjects onto that algebra
and the Sylvester image vanishes there.
-/

namespace PHJFRI.Stage3.SylvesterQuotientLength

noncomputable section

variable {K B : Type*} [Field K] [AddCommGroup B] [Module K B]
variable [FiniteDimensional K B]

/-- Universal target version of the common-root corank argument.  `B` may be a
    product of residue fields or a nonreduced Artin algebra; no separability or
    reducedness assumption occurs. -/
theorem finrank_target_le_sylvester_corank
    (p q : Polynomial K) (m n : ℕ)
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (E : Polynomial.degreeLT K (m + n) →ₗ[K] B)
    (hsurj : Function.Surjective E)
    (hcontain : LinearMap.range (Polynomial.sylvesterMap p q hp hq) ≤
      LinearMap.ker E) :
    Module.finrank K B ≤ m + n - (Polynomial.sylvester p q m n).rank := by
  have htarget : Module.finrank K (LinearMap.range E) = Module.finrank K B := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
  have hnull := LinearMap.finrank_range_add_finrank_ker E
  rw [htarget,
    ProximityPrize.SubmissionLower.PlaneResultantPointCount.finrank_degreeLT] at hnull
  have hmono := Submodule.finrank_mono hcontain
  have hmatrix :=
    ProximityPrize.SubmissionLower.PlaneResultantPointCount.sylvester_rank_eq_finrank_range
      p q m n hp hq
  change (Polynomial.sylvester p q m n).rank =
    Module.finrank K (LinearMap.range (Polynomial.sylvesterMap p q hp hq)) at hmatrix
  omega

#print axioms finrank_target_le_sylvester_corank

end

end PHJFRI.Stage3.SylvesterQuotientLength
