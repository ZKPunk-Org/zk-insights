import Mathlib
import PHJ_FRI_TrigradedKoszulLength

/-!
# Explicit tridegree coefficient boxes

This file instantiates the abstract three-generator Koszul length theorem on
finite coefficient arrays for trihomogeneous forms on `(P¹)^3`.  It removes
all Hilbert-function equalities from the final interface.
-/

namespace PHJFRI.Stage3.TrigradedRectangle

open Function
open PHJFRI.Stage3.TrigradedKoszulLength

noncomputable section

variable {K Q : Type*} [Field K]
variable [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

abbrev Rect3 (K : Type*) [Field K] (u v w : ℕ) :=
  Fin (u + 1) → Fin (v + 1) → Fin (w + 1) → K

@[simp] theorem rect3_finrank (u v w : ℕ) :
    Module.finrank K (Rect3 K u v w) = (u + 1) * (v + 1) * (w + 1) := by
  simp [Rect3]

abbrev K2 (K : Type*) [Field K]
    (r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ) :=
  Rect3 K (r1 + c1) (r2 + c2) (r3 + c3) ×
  (Rect3 K (r1 + t1) (r2 + t2) (r3 + t3) ×
   Rect3 K (r1 + g1) (r2 + g2) (r3 + g3))

abbrev K1 (K : Type*) [Field K]
    (r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ) :=
  Rect3 K (r1 + t1 + c1) (r2 + t2 + c2) (r3 + t3 + c3) ×
  (Rect3 K (r1 + g1 + c1) (r2 + g2 + c2) (r3 + g3 + c3) ×
   Rect3 K (r1 + g1 + t1) (r2 + g2 + t2) (r3 + g3 + t3))

@[simp] theorem k2_finrank
    (r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ) :
    Module.finrank K (K2 K r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3) =
      (r1 + c1 + 1) * (r2 + c2 + 1) * (r3 + c3 + 1) +
      (r1 + t1 + 1) * (r2 + t2 + 1) * (r3 + t3 + 1) +
      (r1 + g1 + 1) * (r2 + g2 + 1) * (r3 + g3 + 1) := by
  simp [K2, Rect3]

@[simp] theorem k1_finrank
    (r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ) :
    Module.finrank K (K1 K r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3) =
      (r1 + t1 + c1 + 1) * (r2 + t2 + c2 + 1) *
        (r3 + t3 + c3 + 1) +
      (r1 + g1 + c1 + 1) * (r2 + g2 + c2 + 1) *
        (r3 + g3 + c3 + 1) +
      (r1 + g1 + t1 + 1) * (r2 + g2 + t2 + 1) *
        (r3 + g3 + t3 + 1) := by
  simp [K1, Rect3]

/-- Explicit-box form of the three-generator mixed-length theorem. -/
theorem target_finrank_le_mixed3_rect
    (r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 : ℕ)
    (d3 : Rect3 K r1 r2 r3 →ₗ[K]
      K2 K r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3)
    (d2 : K2 K r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 →ₗ[K]
      K1 K r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3)
    (d1 : K1 K r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3 →ₗ[K]
      Rect3 K (r1 + g1 + t1 + c1)
        (r2 + g2 + t2 + c2) (r3 + g3 + t3 + c3))
    (E : Rect3 K (r1 + g1 + t1 + c1)
      (r2 + g2 + t2 + c2) (r3 + g3 + t3 + c3) →ₗ[K] Q)
    (hd3inj : Function.Injective d3)
    (hexact2 : LinearMap.ker d2 = LinearMap.range d3)
    (hexact1 : LinearMap.ker d1 = LinearMap.range d2)
    (hcontain : LinearMap.range d1 ≤ LinearMap.ker E)
    (hEsurj : Function.Surjective E) :
    Module.finrank K Q ≤ mixed3 g1 g2 g3 t1 t2 t3 c1 c2 c3 := by
  apply target_finrank_le_mixed3
    (K := K)
    (H3 := Rect3 K r1 r2 r3)
    (H2 := K2 K r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3)
    (H1 := K1 K r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3)
    (H0 := Rect3 K (r1 + g1 + t1 + c1)
      (r2 + g2 + t2 + c2) (r3 + g3 + t3 + c3))
    r1 r2 r3 g1 g2 g3 t1 t2 t3 c1 c2 c3
    d3 d2 d1 E hd3inj hexact2 hexact1 hcontain hEsurj
  · simp [Rect3]
  · simp [K2, Rect3]
  · simp [K1, Rect3]
  · simp [Rect3]

#print axioms rect3_finrank
#print axioms k2_finrank
#print axioms k1_finrank
#print axioms target_finrank_le_mixed3_rect

end

end PHJFRI.Stage3.TrigradedRectangle
