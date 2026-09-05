import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import PHJ_FRI_ActualCurvePoleZeroCount

/-!
# Prime-component seed incidence with one anchor and pole budgets

This is the local contact-geometry replacement theorem.  On a horizontal
component the seed coordinate `Z` is the sole finite separable anchor.  The
`Y,R,Z` box cost is supplied by pole-bounded coordinate data in the same
function field.  The identity-node / affine-pencil half of the public proof is
reused unchanged.
-/

namespace PHJFRI.Stage3.ContactPrimeSeedIncidencePole

open scoped Classical BigOperators
open ProximityPrize.SubmissionLower.ActualCurveCoordinateField
open ProximityPrize.SubmissionLower.ActualCurveRationalProjection
open ProximityPrize.SubmissionLower.ContactGenericSurface
open ProximityPrize.SubmissionLower.ContactPolynomialSolutions
open ProximityPrize.SubmissionLower.ContactPolynomialRecovery
open ProximityPrize.SubmissionLower.ContactTaylorNumerators
open ProximityPrize.SubmissionLower.ContactComponentPencils
open ProximityPrize.SubmissionLower.ContactTranslation
open ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (phi : Polynomial K →+* Ω)
variable (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

/-- Box cost supplied by actual pole masses rather than coordinate finranks. -/
def poleComponentCost
    (c : Fin 3 → PHJFRI.Stage3.PoleBoundedCoordinate.Coordinate Ω
      (CoordinateField Ω P))
    (cap : Fin 3 → ℕ) : ℕ :=
  ∑ j, cap j * (c j).degree

/-- Proper-node agreement fibers on a horizontal component. -/
theorem agreement_fiber_card_le
    (hz : Transcendental Ω (coordinate Ω P (2 : Fin 3)))
    (hfinite :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P (2 : Fin 3) hz
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hseparable :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P (2 : Fin 3) hz
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (c : Fin 3 → PHJFRI.Stage3.PoleBoundedCoordinate.Coordinate Ω
      (CoordinateField Ω P))
    (hc : ∀ j, (c j).value = coordinate Ω P j)
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (p w : ℕ) [CharP Ω p] (hchar : w < p)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ gamma ∈ Gamma, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
    (x u0 u1 : K)
    (hproper : agreementPolynomial phi F w x u0 u1 ∉ P)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ j, (agreementPolynomial phi F w x u0 u1).degreeOf j ≤ cap j) :
    (Gamma.filter (fun gamma => (selected gamma).eval x = u0 + gamma * u1)).card ≤
      poleComponentCost P c cap := by
  classical
  let fiber := Gamma.filter (fun gamma => (selected gamma).eval x = u0 + gamma * u1)
  let points := fiber.image (selectedPoint phi selected)
  have hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact hpoint gamma (Finset.mem_filter.mp hgamma).1
  have hpointsF : ∀ v ∈ points,
      MvPolynomial.aeval v (agreementPolynomial phi F w x u0 u1) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hGamma, hagree⟩ := Finset.mem_filter.mp hgamma
    exact (selected_agreement_zero_iff phi F selected p w hchar gamma
      (hdegree gamma hGamma) (hsolution gamma hGamma) (hregular gamma hGamma)
      x u0 u1).mpr hagree
  have hcount :=
    PHJFRI.Stage3.ActualCurvePoleZeroCount.finite_zero_points_le_box_of_anchor
      Ω P (2 : Fin 3) hz hfinite hseparable c hc
      (agreementPolynomial phi F w x u0 u1) hproper cap hcap
      points hpointsP hpointsF
  have hcard : points.card = fiber.card :=
    Finset.card_image_of_injective _ (selectedPoint_injective phi selected)
  rw [hcard] at hcount
  unfold poleComponentCost
  exact_mod_cast hcount

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

/-- Horizontal per-prime incidence with the sharp proper-node coefficient.
    No `Y`- or `R`-projection separability occurs in the statement. -/
theorem prime_seed_incidence_sharp
    (hz : Transcendental Ω (coordinate Ω P (2 : Fin 3)))
    (hfinite :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P (2 : Fin 3) hz
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hseparable :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P (2 : Fin 3) hz
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (c : Fin 3 → PHJFRI.Stage3.PoleBoundedCoordinate.Coordinate Ω
      (CoordinateField Ω P))
    (hc : ∀ j, (c j).value = coordinate Ω P j)
    (hseedPos : 1 ≤ (c (2 : Fin 3)).degree)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K)
    (hF : surfaceMap phi F ∈ P)
    (hH : surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u0 u1 : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ gamma ∈ Gamma, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial phi F w (x i) (u0 i) (u1 i)).degreeOf j ≤ cap j) :
    Gamma.card * (a - w) ≤
      (nodes.card - w) * poleComponentCost P c cap +
        (e + 1) * (a - w) * (c (2 : Fin 3)).degree := by
  classical
  let I := identityNodes phi P F nodes x u0 u1 w
  let relation : K → ι → Prop :=
    fun gamma i => (selected gamma).eval (x i) = u0 i + gamma * u1 i
  by_cases hI : I.card ≤ w
  · have hfiber : ∀ i ∈ nodes \ I,
        (Gamma.filter (fun gamma => relation gamma i)).card ≤
          poleComponentCost P c cap := by
      intro i hi
      obtain ⟨hinodes, hnotI⟩ := Finset.mem_sdiff.mp hi
      have hproper : agreementPolynomial phi F w (x i) (u0 i) (u1 i) ∉ P := by
        intro hmem
        apply hnotI
        exact Finset.mem_filter.mpr ⟨hinodes, hmem⟩
      exact agreement_fiber_card_le phi P hz hfinite hseparable c hc F selected
        Gamma p w hchar hdegree hsolution hregular hpoint
        (x i) (u0 i) (u1 i) hproper cap (hcap i hinodes)
    have hcount := ProximityPrize.SubmissionLower.ContactIncidence.sharp_incidence_bound
      relation Gamma nodes I a w (poleComponentCost P c cap)
      (identityNodes_subset phi P F nodes x u0 u1 w) hI hwa han
      hagreement hfiber
    omega
  · have hcI : w < I.card := Nat.lt_of_not_ge hI
    have hvalues : ∀ (t : {gamma : K // gamma ∈ Gamma}) i, i ∈ I →
        (selected t.1).eval (x i) = u0 i + t.1 * u1 i := by
      intro t
      exact selected_agrees_on_identity_nodes phi P F nodes x u0 u1 p w hchar
        (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
        (hregular t.1 t.2) (hpoint t.1 t.2)
    obtain ⟨P0, P1, h0, h1, _, hpencil⟩ :=
      exists_common_pencil_of_many_identities phi P F hF hH nodes x u0 u1 w hinj hcI
        (fun t : {gamma : K // gamma ∈ Gamma} => t.1)
        (fun t => selected t.1) (fun t => hdegree t.1 t.2) hvalues
    have hfilter :
        Gamma.filter (fun gamma => selected gamma = P0 + Polynomial.C gamma * P1) =
          Gamma := Finset.filter_eq_self.mpr
            (fun gamma hgamma => hpencil ⟨gamma, hgamma⟩)
    have hGamma : Gamma.card ≤ e + 1 := by
      have h := hnoPencil P0 P1 h0 h1
      rwa [hfilter] at h
    have hcharge : Gamma.card * (a - w) ≤
        (e + 1) * (a - w) * (c (2 : Fin 3)).degree := by
      calc
        _ ≤ (e + 1) * (a - w) := Nat.mul_le_mul_right _ hGamma
        _ ≤ _ := by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left ((e + 1) * (a - w)) hseedPos
    omega

/-- Conservative form matching the existing mixed-degree ledger. -/
theorem prime_seed_incidence
    (hz : Transcendental Ω (coordinate Ω P (2 : Fin 3)))
    (hfinite :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P (2 : Fin 3) hz
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hseparable :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P (2 : Fin 3) hz
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (c : Fin 3 → PHJFRI.Stage3.PoleBoundedCoordinate.Coordinate Ω
      (CoordinateField Ω P))
    (hc : ∀ j, (c j).value = coordinate Ω P j)
    (hseedPos : 1 ≤ (c (2 : Fin 3)).degree)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K)
    (hF : surfaceMap phi F ∈ P)
    (hH : surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u0 u1 : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ gamma ∈ Gamma, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial phi F w (x i) (u0 i) (u1 i)).degreeOf j ≤ cap j) :
    Gamma.card * (a - w) ≤
      nodes.card * poleComponentCost P c cap +
        (e + 1) * (a - w) * (c (2 : Fin 3)).degree := by
  have hsharp := prime_seed_incidence_sharp phi P hz hfinite hseparable c hc hseedPos
    hnonpoint F hF hH selected Gamma nodes x u0 u1 hinj p w a e hw hchar hwa han
    hdegree hsolution hregular hpoint hagreement hnoPencil cap hcap
  have hnodes : nodes.card - w ≤ nodes.card := Nat.sub_le _ _
  have hcost :
      (nodes.card - w) * poleComponentCost P c cap ≤
        nodes.card * poleComponentCost P c cap :=
    Nat.mul_le_mul_right _ hnodes
  omega

#print axioms agreement_fiber_card_le
#print axioms prime_seed_incidence_sharp
#print axioms prime_seed_incidence

end

end PHJFRI.Stage3.ContactPrimeSeedIncidencePole
