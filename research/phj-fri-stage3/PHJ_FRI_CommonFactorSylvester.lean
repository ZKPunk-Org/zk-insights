import PHJ_FRI_SylvesterQuotientLength

/-!
# An arbitrary common factor consumes Sylvester corank

This specializes the universal quotient-length theorem to the finite algebra
`K[X]/(H)`.  It is useful over every closed point field: a product of distinct
irreducible component factors dividing both specialized equations has total
degree at most the specialized Sylvester corank, without splitting or
separability.
-/

namespace PHJFRI.Stage3.CommonFactorSylvester

noncomputable section

variable {K : Type*} [Field K]

/-- Evaluation of bounded polynomials in the monic quotient algebra. -/
def degreeLTEvalAdjoinRoot (H : Polynomial K) (N : ℕ) :
    Polynomial.degreeLT K N →ₗ[K] AdjoinRoot H :=
  (AdjoinRoot.mk H).toLinearMap.comp (Polynomial.degreeLT K N).subtype

/-- If the monic modulus has degree at most the cap, every quotient class has
    a representative in the capped polynomial space. -/
theorem degreeLTEvalAdjoinRoot_surjective
    (H : Polynomial K) (hH : H.Monic) (N : ℕ)
    (hdegree : H.natDegree ≤ N) :
    Function.Surjective (degreeLTEvalAdjoinRoot H N) := by
  intro x
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective x
  let R := P %ₘ H
  have hR : R ∈ Polynomial.degreeLT K N := by
    rw [Polynomial.mem_degreeLT]
    have hlt := Polynomial.degree_modByMonic_lt P hH
    exact hlt.trans_le (by
      rw [Polynomial.degree_eq_natDegree hH.ne_zero]
      exact WithBot.coe_le_coe.mpr hdegree)
  refine ⟨⟨R, hR⟩, ?_⟩
  change AdjoinRoot.mk H R = AdjoinRoot.mk H P
  simpa only [R, AdjoinRoot.modByMonicHom_mk] using
    (AdjoinRoot.mk_leftInverse hH (AdjoinRoot.mk H P))

/-- A monic polynomial dividing both Sylvester inputs has degree at most the
    Sylvester corank.  Repeated roots and inseparable irreducible factors are
    fully retained in `H.natDegree`. -/
theorem common_factor_natDegree_le_sylvester_corank
    (p q H : Polynomial K) (m n : ℕ)
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (hH : H.Monic) (hHp : H ∣ p) (hHq : H ∣ q)
    (hcap : H.natDegree ≤ m + n) :
    H.natDegree ≤ m + n - (Polynomial.sylvester p q m n).rank := by
  letI : Module.Free K (AdjoinRoot H) := hH.free_adjoinRoot
  letI : Module.Finite K (AdjoinRoot H) := hH.finite_adjoinRoot
  let evaluation := degreeLTEvalAdjoinRoot H (m + n)
  have hsurj : Function.Surjective evaluation :=
    degreeLTEvalAdjoinRoot_surjective H hH (m + n) hcap
  have hcontain : LinearMap.range (Polynomial.sylvesterMap p q hp hq) ≤
      LinearMap.ker evaluation := by
    rintro P ⟨input, rfl⟩
    rw [LinearMap.mem_ker]
    change AdjoinRoot.mk H
      (p * (input.2 : Polynomial K) + q * (input.1 : Polynomial K)) = 0
    have hpzero : AdjoinRoot.mk H p = 0 := AdjoinRoot.mk_eq_zero.mpr hHp
    have hqzero : AdjoinRoot.mk H q = 0 := AdjoinRoot.mk_eq_zero.mpr hHq
    simp only [map_add, map_mul, hpzero, hqzero, zero_mul, zero_add]
  have hbound := SylvesterQuotientLength.finrank_target_le_sylvester_corank
    p q m n hp hq evaluation hsurj hcontain
  simpa only [finrank_quotient_span_eq_natDegree] using hbound

#print axioms degreeLTEvalAdjoinRoot_surjective
#print axioms common_factor_natDegree_le_sylvester_corank

end

end PHJFRI.Stage3.CommonFactorSylvester
