import Mathlib

/-!
# Closed-point degree times relative component length

For a closed point field `E/F`, the base-field length of every finite
`E`-vector space is `[E:F]` times its relative `E`-length.  This is the tower
identity needed to turn one Sylvester corank over `E` into the degree-weighted
closed-point contribution over `F`.
-/

namespace PHJFRI.Stage3.ClosedPointTowerLength

open scoped BigOperators

noncomputable section

variable (F E : Type*) [Field F] [Field E] [Algebra F E]
variable [FiniteDimensional F E]
variable {ι : Type*} [Fintype ι]
variable (L : ι → Type*)
variable [∀ i, AddCommGroup (L i)]
variable [∀ i, Module E (L i)] [∀ i, Module F (L i)]
variable [∀ i, IsScalarTower F E (L i)]
variable [∀ i, FiniteDimensional E (L i)]

/-- Tower law summed over a finite family of finite relative component
    spaces. -/
theorem sum_finrank_base_eq_closedPointDegree_mul_relative :
    (∑ i, Module.finrank F (L i)) =
      Module.finrank F E * ∑ i, Module.finrank E (L i) := by
  calc
    (∑ i, Module.finrank F (L i)) =
        ∑ i, Module.finrank F E * Module.finrank E (L i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Module.finrank_mul_finrank F E (L i)).symm
    _ = Module.finrank F E * ∑ i, Module.finrank E (L i) := by
      rw [Finset.mul_sum]

/-- A relative-length bound becomes a degree-weighted absolute-length
    bound, without separability. -/
theorem sum_finrank_base_le_closedPointDegree_mul_cap
    (cap : ℕ)
    (hcap : (∑ i, Module.finrank E (L i)) ≤ cap) :
    (∑ i, Module.finrank F (L i)) ≤ Module.finrank F E * cap := by
  rw [sum_finrank_base_eq_closedPointDegree_mul_relative F E L]
  exact Nat.mul_le_mul_left (Module.finrank F E) hcap

/-- Numeric form for an arbitrary supplied closed-point degree. -/
theorem weighted_relative_length_le
    (relative : ι → ℕ) (cap degree : ℕ)
    (hrelative : (∑ i, relative i) ≤ cap)
    (hdegree : Module.finrank F E ≤ degree) :
    Module.finrank F E * (∑ i, relative i) ≤ degree * cap := by
  exact Nat.mul_le_mul hdegree hrelative

#print axioms sum_finrank_base_eq_closedPointDegree_mul_relative
#print axioms sum_finrank_base_le_closedPointDegree_mul_cap
#print axioms weighted_relative_length_le

end

end PHJFRI.Stage3.ClosedPointTowerLength
