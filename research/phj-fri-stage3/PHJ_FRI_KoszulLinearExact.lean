import Mathlib
import PHJ_FRI_KoszulSyzygy

/-!
# Exact two-generator Koszul linear complex

This file upgrades the elementwise syzygy theorem to an equality of kernels
and ranges for explicit `K`-linear Koszul maps.  It is the exactness input
required by the bigraded length theorem before restriction to homogeneous
components.
-/

namespace PHJFRI.Stage3.KoszulLinearExact

open Function
open PHJFRI.Stage3.KoszulSyzygy

noncomputable section

variable {K R : Type*} [Field K]
variable [CommRing R] [NoZeroDivisors R] [Algebra K R]

/-- First nontrivial map in the two-generator Koszul complex. -/
def koszulD2 (P Q : R) : R →ₗ[K] R × R where
  toFun h := (Q * h, -(P * h))
  map_add' x y := by
    ext <;> simp [mul_add]
  map_smul' c x := by
    ext <;> simp [Algebra.smul_def]
    <;> ring

/-- Last nontrivial map in the two-generator Koszul complex. -/
def koszulD1 (P Q : R) : R × R →ₗ[K] R where
  toFun x := P * x.1 + Q * x.2
  map_add' x y := by
    simp [mul_add, add_mul]
    ring
  map_smul' c x := by
    simp [Algebra.smul_def]
    ring

@[simp] theorem koszulD1_apply (P Q A B : R) :
    koszulD1 (K := K) P Q (A, B) = P * A + Q * B := rfl

@[simp] theorem koszulD2_apply (P Q h : R) :
    koszulD2 (K := K) P Q h = (Q * h, -(P * h)) := rfl

/-- The two displayed maps form a complex. -/
theorem koszul_complex_zero (P Q : R) :
    (koszulD1 (K := K) P Q).comp (koszulD2 (K := K) P Q) = 0 := by
  ext h
  simp [koszulD1, koszulD2]
  ring

/-- If `P` is nonzero, the first Koszul map is injective. -/
theorem koszulD2_injective (P Q : R) (hP : P ≠ 0) :
    Function.Injective (koszulD2 (K := K) P Q) := by
  intro x y hxy
  have hsecond : -(P * x) = -(P * y) := congrArg Prod.snd hxy
  have hmul : P * (x - y) = 0 := by
    calc
      P * (x - y) = P * x - P * y := by ring
      _ = 0 := by linear_combination hsecond
  rcases mul_eq_zero.mp hmul with hPzero | hxyzero
  · exact (hP hPzero).elim
  · exact sub_eq_zero.mp hxyzero

/-- Exactness at the middle term under the Euclid divisibility implication. -/
theorem koszul_ker_eq_range
    (P Q : R) (hP : P ≠ 0)
    (hEuclid : ∀ x : R, P ∣ Q * x → P ∣ x) :
    LinearMap.ker (koszulD1 (K := K) P Q) =
      LinearMap.range (koszulD2 (K := K) P Q) := by
  ext x
  constructor
  · intro hx
    rcases x with ⟨A, B⟩
    change P * A + Q * B = 0 at hx
    obtain ⟨h, hA, hB⟩ :=
      relation_generated_by_koszul P Q A B hP hEuclid hx
    refine ⟨h, ?_⟩
    ext
    · exact hA.symm
    · exact hB.symm
  · intro hx
    rcases hx with ⟨h, rfl⟩
    change P * (Q * h) + Q * (-(P * h)) = 0
    ring

#print axioms koszulD2
#print axioms koszulD1
#print axioms koszul_complex_zero
#print axioms koszulD2_injective
#print axioms koszul_ker_eq_range

end

end PHJFRI.Stage3.KoszulLinearExact
