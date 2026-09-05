import Mathlib

/-!
# Seed-anchored separation and horizontal/vertical aggregation

This file formalizes two reusable pieces of the proposed PHJ-FRI backend:

1. a finite field extension of degree strictly below the positive
   characteristic is automatically separable;
2. horizontal and vertical component budgets combine with only an additive
   vertical-coordinate charge.

The geometric mixed-pole budget is deliberately an input here. No theorem in
this file assumes the still-open MPCB intersection statement.
-/

namespace PHJFRI.Stage3.SeedAnchored

open scoped BigOperators

/-- A finite extension in positive characteristic is separable when its total
    degree is smaller than the characteristic. This is the exact bridge
    needed after bounding the seed-projection degree by a mixed degree below
    `p`; it does not ask the other coordinate projections to be separable. -/
theorem isSeparable_of_finrank_lt_expChar
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (p : ℕ) [ExpChar F p] (hp : 1 < p)
    (hdegree : Module.finrank F E < p) :
    Algebra.IsSeparable F E := by
  rw [isSeparable_iff_finInsepDegree_eq_one]
  obtain ⟨r, hr⟩ := Field.finInsepDegree_eq_pow F E p
  rw [hr]
  by_cases hzero : r = 0
  · simp [hzero]
  · exfalso
    obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hone : 1 ≤ p ^ r' := one_le_pow₀ hp.le
    have hp_le_pow : p ≤ p ^ (r' + 1) := by
      rw [pow_succ]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right p hone
    have hinsep_dvd : Field.finInsepDegree F E ∣ Module.finrank F E := by
      refine ⟨Field.finSepDegree F E, ?_⟩
      rw [Nat.mul_comm, Field.finSepDegree_mul_finInsepDegree]
    have hinsep_le : Field.finInsepDegree F E ≤ Module.finrank F E :=
      Nat.le_of_dvd Module.finrank_pos hinsep_dvd
    rw [hr] at hinsep_le
    exact (not_lt_of_ge (hp_le_pow.trans hinsep_le)) hdegree

/-- If every vertical curve has at least one nonconstant affine coordinate,
    then its number is bounded by the aggregate `Y` plus `R` pole mass. -/
theorem vertical_component_count_le_coordinate_mass
    {I : Type*} [Fintype I] (dY dR : I → ℕ)
    (hnonconstant : ∀ i, 1 ≤ dY i + dR i) :
    Fintype.card I ≤ (∑ i, dY i) + ∑ i, dR i := by
  calc
    Fintype.card I = ∑ _i : I, 1 := by simp
    _ ≤ ∑ i : I, (dY i + dR i) :=
      Finset.sum_le_sum fun i _ => hnonconstant i
    _ = (∑ i, dY i) + ∑ i, dR i := by
      rw [Finset.sum_add_distrib]

/-- Abstract horizontal/vertical seed aggregation. Horizontal components use
    the seed coordinate as their single separating parameter; each vertical
    component carries at most one selected seed and is charged to `deltaY +
    deltaR`. -/
theorem horizontal_vertical_seed_bound
    (qHorizontal qVertical gap n e proper deltaY deltaR deltaZ : ℕ)
    (hHorizontal :
      qHorizontal * gap ≤
        n * proper + (e + 1) * gap * deltaZ)
    (hVertical : qVertical ≤ deltaY + deltaR) :
    (qHorizontal + qVertical) * gap ≤
      n * proper + (e + 1) * gap * deltaZ +
        gap * (deltaY + deltaR) := by
  have hv : qVertical * gap ≤ (deltaY + deltaR) * gap :=
    Nat.mul_le_mul_right gap hVertical
  calc
    (qHorizontal + qVertical) * gap =
        qHorizontal * gap + qVertical * gap := by ring
    _ ≤ (n * proper + (e + 1) * gap * deltaZ) +
        (deltaY + deltaR) * gap := Nat.add_le_add hHorizontal hv
    _ = n * proper + (e + 1) * gap * deltaZ +
        gap * (deltaY + deltaR) := by ring

#print axioms isSeparable_of_finrank_lt_expChar
#print axioms vertical_component_count_le_coordinate_mass
#print axioms horizontal_vertical_seed_bound

end PHJFRI.Stage3.SeedAnchored
