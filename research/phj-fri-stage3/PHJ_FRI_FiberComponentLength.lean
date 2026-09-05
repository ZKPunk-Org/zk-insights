import PHJ_FRI_FiniteAlgebraProjection
import PHJ_FRI_SylvesterQuotientLength

/-!
# One closed fiber: component quotient lengths versus Sylvester corank

This file composes the finite-algebra CRT bound with the universal Sylvester
cokernel bound.  It isolates the exact algebraic statement needed inside a
single irreducible resultant factor.

The remaining geometric task is only to construct the finite fiber algebra
and the pairwise-coprime component ideals from the actual contact primes.
-/

namespace PHJFRI.Stage3.FiberComponentLength

open scoped BigOperators

noncomputable section

variable {K B ι : Type*} [Field K] [CommRing B] [Algebra K B]
variable [FiniteDimensional K B]
variable [Fintype ι]

/-- Pairwise-coprime component quotients of a finite fiber algebra consume at
    most one Sylvester corank.  Nilpotents and purely inseparable residue
    fields are retained in the quotient dimensions. -/
theorem sum_component_quotient_finrank_le_sylvester_corank
    (p q : Polynomial K) (m n : ℕ)
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (evaluation : Polynomial.degreeLT K (m + n) →ₗ[K] B)
    (hsurj : Function.Surjective evaluation)
    (hcontain : LinearMap.range (Polynomial.sylvesterMap p q hp hq) ≤
      LinearMap.ker evaluation)
    (I : ι → Ideal B) (hI : Pairwise (IsCoprime on I))
    [∀ i, FiniteDimensional K (B ⧸ I i)] :
    (∑ i, Module.finrank K (B ⧸ I i)) ≤
      m + n - (Polynomial.sylvester p q m n).rank := by
  calc
    (∑ i, Module.finrank K (B ⧸ I i)) ≤ Module.finrank K B :=
      FiniteAlgebraProjection.sum_finrank_quotient_le K B I hI
    _ ≤ m + n - (Polynomial.sylvester p q m n).rank :=
      SylvesterQuotientLength.finrank_target_le_sylvester_corank
        p q m n hp hq evaluation hsurj hcontain

/-- Variant exposing an arbitrary family of lower bounds on the quotient
    dimensions. -/
theorem sum_relative_length_le_sylvester_corank
    (p q : Polynomial K) (m n : ℕ)
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (evaluation : Polynomial.degreeLT K (m + n) →ₗ[K] B)
    (hsurj : Function.Surjective evaluation)
    (hcontain : LinearMap.range (Polynomial.sylvesterMap p q hp hq) ≤
      LinearMap.ker evaluation)
    (I : ι → Ideal B) (hI : Pairwise (IsCoprime on I))
    [∀ i, FiniteDimensional K (B ⧸ I i)]
    (relativeLength : ι → ℕ)
    (hlength : ∀ i, relativeLength i ≤ Module.finrank K (B ⧸ I i)) :
    (∑ i, relativeLength i) ≤
      m + n - (Polynomial.sylvester p q m n).rank := by
  calc
    (∑ i, relativeLength i) ≤
        ∑ i, Module.finrank K (B ⧸ I i) := by
      apply Finset.sum_le_sum
      intro i _
      exact hlength i
    _ ≤ m + n - (Polynomial.sylvester p q m n).rank :=
      sum_component_quotient_finrank_le_sylvester_corank
        p q m n hp hq evaluation hsurj hcontain I hI

#print axioms sum_component_quotient_finrank_le_sylvester_corank
#print axioms sum_relative_length_le_sylvester_corank

end

end PHJFRI.Stage3.FiberComponentLength
