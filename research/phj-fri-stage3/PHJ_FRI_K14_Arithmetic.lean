import Mathlib

/-!
# PHJ-FRI K14 arithmetic certificate

A standalone exact-arithmetic certificate for the current-proof-safe K14
profile.  It is compiled inside the pinned Proximity Prize Lean 4.32.2
workspace by the accompanying isolated GitHub Actions workflow.
-/

namespace PHJFRI.Stage3.K14

abbrev n : ℕ := 262144
abbrev w : ℕ := 131071
abbrev pKoala : ℕ := 2130706433

abbrev m : ℕ := 14
abbrev L : ℕ := 194
abbrev s : ℕ := 4
abbrev a : ℕ := 185055
abbrev e : ℕ := 77089
abbrev gap : ℕ := 53984
abbrev gapSq : ℕ := 2914272256
abbrev alignmentBudget : ℕ := 137232143318053042
abbrev wholeNumerator : ℕ := 399931827903217763501092864

/-- Agreement and error partition the length exactly. -/
theorem partition : a + e = n := by
  norm_num [a, e, n]

/-- K14 is strictly beyond the finite-length Johnson agreement threshold. -/
theorem beyond_finite_johnson : a ^ 2 < n * w := by
  norm_num [a, n, w]

/-- Exact amount by which `n*w` exceeds `a^2`. -/
theorem johnson_crossing_margin : n * w - a ^ 2 = 114123199 := by
  norm_num [a, n, w]

/-- The hidden-contact interpolation linear system has positive nullity. -/
theorem interpolation_slack :
    20819496100 - n * 79420 = 19620 := by
  norm_num [n]

/-- Every coordinate projection cap required by the existing proof is below
    the KoalaBear characteristic. -/
theorem all_current_projection_gates :
    381419520 < pKoala ∧
    1932525762 < pKoala ∧
    37355524 < pKoala ∧
    381416614 < pKoala ∧
    1932511037 < pKoala ∧
    37355239 < pKoala ∧
    1358 < pKoala ∧
    374808 < pKoala ∧
    138 < pKoala := by
  norm_num [pKoala]

/-- The quotient defining the integer alignment budget is exact. -/
theorem budget_is_strict :
    (alignmentBudget - 1) * gapSq < wholeNumerator ∧
      wholeNumerator < alignmentBudget * gapSq := by
  norm_num [alignmentBudget, gapSq, wholeNumerator]

/-- The exceptional-seed term fits below the fixed 128-bit challenge-field
    allocation used by the public certificate. -/
theorem challenge_field_gate :
    alignmentBudget ≤ pKoala ^ 6 / 2 ^ 129 := by
  norm_num [alignmentBudget, pKoala]

/-- Direct-threshold lifting needs `e+2` seeds on a common pencil. -/
theorem common_pencil_seed_threshold : e + 2 = 77091 := by
  norm_num [e]

/-- The finite search cutoff induced by the current R-projection gate. -/
theorem max_m_cutoff :
    (pKoala - 2) / (4 * (w + 1)) = 4063 := by
  norm_num [pKoala, w]

#print axioms partition
#print axioms beyond_finite_johnson
#print axioms johnson_crossing_margin
#print axioms interpolation_slack
#print axioms all_current_projection_gates
#print axioms budget_is_strict
#print axioms challenge_field_gate
#print axioms common_pencil_seed_threshold
#print axioms max_m_cutoff

end PHJFRI.Stage3.K14
