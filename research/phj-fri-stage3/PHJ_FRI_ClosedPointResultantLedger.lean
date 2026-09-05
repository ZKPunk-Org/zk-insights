import PHJ_FRI_IrreducibleFactorMultiplicity
import PHJ_FRI_PrimeFactorDegreeLedger

/-!
# Closed-point resultant degree ledger

This file composes the two characteristic-free algebraic mechanisms:

* rank loss modulo each prime resultant factor forces the corresponding
  factor power into the determinant;
* pairwise-coprime factor powers consume determinant degree.

The remaining geometric input is stated explicitly as `relativeTotal`: the
sum of relative residue/quotient lengths of actual components lying over one
closed point is at most the specialized Sylvester corank.  No separability or
splitting-field embedding count appears.
-/

namespace PHJFRI.Stage3.ClosedPointResultantLedger

open scoped BigOperators

noncomputable section

variable {K I κ : Type*} [Field K]
variable [Fintype I] [Fintype κ] [DecidableEq κ]
variable (E : I → Type*) [∀ i, Field (E i)]

/-- Closed-point degrees, weighted by relative scheme lengths over their
    irreducible base factors, are bounded by the determinant degree. -/
theorem sum_closedPointDegree_le_det
    (q : ∀ i, Polynomial K →+* E i)
    (hq : ∀ i, Function.Surjective (q i))
    (factor : I → Polynomial K)
    (hprime : ∀ i, Prime (factor i))
    (hmonic : ∀ i, (factor i).Monic)
    (hker : ∀ i, RingHom.ker (q i) = Ideal.span {factor i})
    (hcoprime : Pairwise (IsCoprime on factor))
    (M : Matrix κ κ (Polynomial K))
    (relativeTotal : I → ℕ)
    (hrelative : ∀ i,
      relativeTotal i ≤ Fintype.card κ - ((q i).mapMatrix M).rank)
    (hdet : M.det ≠ 0) :
    (∑ i, relativeTotal i * (factor i).natDegree) ≤ M.det.natDegree := by
  classical
  let corank : I → ℕ :=
    fun i => Fintype.card κ - ((q i).mapMatrix M).rank
  have hpow : ∀ i, factor i ^ corank i ∣ M.det := by
    intro i
    exact IrreducibleFactorMultiplicity.pow_corank_dvd_det_of_prime_quotient
      (q i) (hq i) (factor i) (hprime i) (hker i) M
  have hfactor :=
    PrimeFactorDegreeLedger.sum_multiplicity_mul_natDegree_le
      factor corank M.det hmonic hcoprime hpow hdet
  calc
    (∑ i, relativeTotal i * (factor i).natDegree) ≤
        ∑ i, corank i * (factor i).natDegree := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_right (factor i).natDegree (hrelative i)
    _ ≤ M.det.natDegree := hfactor

/-- Resultant-cap version used by the contact mixed-degree ledger. -/
theorem sum_closedPointDegree_le_cap
    (q : ∀ i, Polynomial K →+* E i)
    (hq : ∀ i, Function.Surjective (q i))
    (factor : I → Polynomial K)
    (hprime : ∀ i, Prime (factor i))
    (hmonic : ∀ i, (factor i).Monic)
    (hker : ∀ i, RingHom.ker (q i) = Ideal.span {factor i})
    (hcoprime : Pairwise (IsCoprime on factor))
    (M : Matrix κ κ (Polynomial K))
    (relativeTotal : I → ℕ)
    (hrelative : ∀ i,
      relativeTotal i ≤ Fintype.card κ - ((q i).mapMatrix M).rank)
    (hdet : M.det ≠ 0) (cap : ℕ) (hcap : M.det.natDegree ≤ cap) :
    (∑ i, relativeTotal i * (factor i).natDegree) ≤ cap :=
  (sum_closedPointDegree_le_det E q hq factor hprime hmonic hker hcoprime
    M relativeTotal hrelative hdet).trans hcap

#print axioms sum_closedPointDegree_le_det
#print axioms sum_closedPointDegree_le_cap

end

end PHJFRI.Stage3.ClosedPointResultantLedger
