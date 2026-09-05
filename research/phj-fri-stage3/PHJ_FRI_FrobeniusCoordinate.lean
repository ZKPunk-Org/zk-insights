import ProximityPrize.SubmissionLower.CoordinateBoxZeroCount

/-!
# Frobenius-normalized coordinates

In positive characteristic an inseparable coordinate should not be discarded.
If it is a `q`-th power of a separable coordinate, all pole orders scale by
`q`, exactly matching the total projection degree.  This file proves the
analytic part.  Existence of the maximal Frobenius root on a function field is
kept as a separate geometric theorem.
-/

namespace PHJFRI.Stage3.FrobeniusCoordinate

open scoped Classical BigOperators WithZero

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

abbrev Place := CoordinatePlaceClassification.NormalizedValuation K L

/-- Pole order scales exactly under an arbitrary natural power. -/
theorem poleOrder_pow (v : Place K L) (x : L) (q : ℕ) :
    CoordinatePoleMass.poleOrder K L v (x ^ q) =
      (q : ℤ) * CoordinatePoleMass.poleOrder K L v x := by
  unfold CoordinatePoleMass.poleOrder ContactLocalPoleBound.poleOrder
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  by_cases hx : 0 ≤ (v.val x).log
  · rw [max_eq_right hx]
    rw [max_eq_right (mul_nonneg (Int.natCast_nonneg q) hx)]
  · have hx' : (v.val x).log ≤ 0 := le_of_not_ge hx
    rw [max_eq_left hx', mul_zero]
    rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg q) hx')]

/-- Data for an actual coordinate expressed as a power of a coordinate whose
    rational projection is finite and separable. -/
structure Data where
  root : CoordinateBoxZeroCount.SeparableCoordinate K L
  exponent : ℕ

namespace Data

variable [IsAlgClosed K]

def rootValue (c : Data K L) : L :=
  CoordinateBoxZeroCount.SeparableCoordinate.value K L c.root

def value (c : Data K L) : L := c.rootValue K L ^ c.exponent

def degree (c : Data K L) : ℕ :=
  c.exponent * CoordinateBoxZeroCount.SeparableCoordinate.degree K L c.root

/-- A Frobenius-root presentation gives the exact projection-degree pole
    budget on every finite family of common normalized places. -/
theorem finite_sum_pole_le_degree (c : Data K L) (W : Finset (Place K L)) :
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (c.value K L)) ≤
      (c.degree K L : ℤ) := by
  have hroot :=
    CoordinateBoxZeroCount.SeparableCoordinate.finite_sum_pole_le_degree
      K L c.root W
  calc
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (c.value K L)) =
        (c.exponent : ℤ) *
          (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (c.rootValue K L)) := by
      simp only [value, poleOrder_pow, Finset.mul_sum]
    _ ≤ (c.exponent : ℤ) *
        (CoordinateBoxZeroCount.SeparableCoordinate.degree K L c.root : ℤ) :=
      mul_le_mul_of_nonneg_left hroot (Int.natCast_nonneg _)
    _ = (c.degree K L : ℤ) := by
      simp only [degree, Nat.cast_mul]

end Data

#print axioms poleOrder_pow
#print axioms Data.finite_sum_pole_le_degree

end

end PHJFRI.Stage3.FrobeniusCoordinate
