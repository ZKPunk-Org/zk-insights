import Mathlib

/-!
# Prime-factor multiplicity ledger

Once every irreducible resultant factor receives a corank multiplicity, the
pairwise-coprime powers consume determinant degree. This file formalizes that
pure UFD step. It does not assert that contact-curve components have already
been injected into the corresponding quotient algebras.
-/

namespace PHJFRI.Stage3.PrimeFactorDegreeLedger

open scoped BigOperators

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Pairwise-coprime monic polynomial factors, each occurring to a supplied
    multiplicity in `D`, consume the weighted sum of their degrees. -/
theorem sum_multiplicity_mul_natDegree_le
    (f : ι → Polynomial K) (multiplicity : ι → ℕ) (D : Polynomial K)
    (hmonic : ∀ i, (f i).Monic)
    (hcoprime : Pairwise (IsCoprime on f))
    (hdiv : ∀ i, f i ^ multiplicity i ∣ D)
    (hD : D ≠ 0) :
    (∑ i, multiplicity i * (f i).natDegree) ≤ D.natDegree := by
  classical
  have hpowers : Pairwise (IsCoprime on fun i => f i ^ multiplicity i) := by
    intro i j hij
    exact (hcoprime hij).pow_left.pow_right
  have hproduct : (∏ i, f i ^ multiplicity i) ∣ D :=
    Fintype.prod_dvd_of_coprime hpowers hdiv
  have hdegree :
      (∏ i, f i ^ multiplicity i).natDegree ≤ D.natDegree :=
    Polynomial.natDegree_le_of_dvd hproduct hD
  have hproductDegree :
      (∏ i, f i ^ multiplicity i).natDegree =
        ∑ i, multiplicity i * (f i).natDegree := by
    calc
      (∏ i, f i ^ multiplicity i).natDegree =
          ∑ i, (f i ^ multiplicity i).natDegree := by
        simpa using Polynomial.natDegree_prod_of_monic
          (s := Finset.univ) (f := fun i => f i ^ multiplicity i)
          (fun i _ => (hmonic i).pow _)
      _ = ∑ i, multiplicity i * (f i).natDegree := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hmonic i).natDegree_pow _
  rwa [hproductDegree] at hdegree

/-- Degree-cap corollary used after a resultant degree estimate. -/
theorem sum_multiplicity_mul_natDegree_le_of_resultant_cap
    (f : ι → Polynomial K) (multiplicity : ι → ℕ) (D : Polynomial K)
    (cap : ℕ)
    (hmonic : ∀ i, (f i).Monic)
    (hcoprime : Pairwise (IsCoprime on f))
    (hdiv : ∀ i, f i ^ multiplicity i ∣ D)
    (hD : D ≠ 0) (hcap : D.natDegree ≤ cap) :
    (∑ i, multiplicity i * (f i).natDegree) ≤ cap :=
  (sum_multiplicity_mul_natDegree_le f multiplicity D hmonic hcoprime hdiv hD).trans hcap

#print axioms sum_multiplicity_mul_natDegree_le
#print axioms sum_multiplicity_mul_natDegree_le_of_resultant_cap

end

end PHJFRI.Stage3.PrimeFactorDegreeLedger
