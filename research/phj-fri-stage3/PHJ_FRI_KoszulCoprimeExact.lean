import Mathlib
import PHJ_FRI_KoszulLinearExact

/-!
# Coprime specialization of Koszul exactness

In a GCD domain, `IsCoprime P Q` supplies precisely the Euclid divisibility
implication used by the two-generator Koszul syzygy theorem.  This removes the
last abstract exactness premise at the ambient polynomial-ring level.
-/

namespace PHJFRI.Stage3.KoszulCoprimeExact

open Function
open PHJFRI.Stage3.KoszulLinearExact

noncomputable section

variable {K R : Type*} [Field K]
variable [CommRing R] [NoZeroDivisors R] [GCDMonoid R] [Algebra K R]

/-- Ambient two-generator Koszul exactness for coprime elements. -/
theorem koszul_ker_eq_range_of_isCoprime
    (P Q : R) (hP : P ≠ 0) (hcop : IsCoprime P Q) :
    LinearMap.ker (koszulD1 (K := K) P Q) =
      LinearMap.range (koszulD2 (K := K) P Q) := by
  apply koszul_ker_eq_range (K := K) P Q hP
  intro x hx
  exact hcop.dvd_of_dvd_mul_left hx

/-- Symmetric orientation of the same exactness theorem. -/
theorem koszul_ker_eq_range_of_isCoprime_right
    (P Q : R) (hQ : Q ≠ 0) (hcop : IsCoprime P Q) :
    LinearMap.ker (koszulD1 (K := K) P Q) =
      LinearMap.range (koszulD2 (K := K) P Q) := by
  apply koszul_ker_eq_range (K := K) P Q
  · intro hP
    have hQunit : IsUnit Q := by
      simpa [hP] using hcop
    exact hQ (hQunit.ne_zero)
  · intro x hx
    exact hcop.dvd_of_dvd_mul_left hx

#print axioms koszul_ker_eq_range_of_isCoprime
#print axioms koszul_ker_eq_range_of_isCoprime_right

end

end PHJFRI.Stage3.KoszulCoprimeExact
