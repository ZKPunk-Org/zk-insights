import ProximityPrize.SubmissionLower.PlaneRootSeparability

/-!
# Characteristic-free finiteness of actual plane-root fields

The existing backend proves finite *and separable* by imposing degree-below-
p characteristic gates on both coordinate annihilators.  For the
scheme-length/resultant backend only finiteness is required.  The resultant
annihilator for `Y` and the specialized plane equation for `R` already give
integrality in every characteristic.
-/

namespace PHJFRI.Stage3.PlaneRootFiniteness

noncomputable section

open ProximityPrize.SubmissionLower

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq L := Classical.decEq L

/-- Two integral generators spanning the whole intermediate field give a
    finite extension; no separability hypothesis is needed. -/
theorem finite_of_two_integral_generators (y r : L)
    (hy : IsIntegral K y) (hr : IsIntegral K r)
    (hgenerate : IntermediateField.adjoin K ({y, r} : Set L) = ⊤) :
    FiniteDimensional K L := by
  letI : FiniteDimensional K (IntermediateField.adjoin K ({y, r} : Set L)) :=
    IntermediateField.finiteDimensional_adjoin_pair hy hr
  letI : FiniteDimensional K (⊤ : IntermediateField K L) := by
    rw [← hgenerate]
    infer_instance
  exact Module.Finite.of_surjective
    (IntermediateField.topEquiv (F := K) (E := L)).toLinearMap
    (IntermediateField.topEquiv (F := K) (E := L)).surjective

/-- Proper common roots of an irreducible positive-outer-degree plane
    equation generate a finite extension in arbitrary characteristic. -/
theorem finite_of_proper_plane_roots
    (P Q : Polynomial (Polynomial K))
    (hirreducible : Irreducible P) (hpositive : 0 < P.natDegree)
    (hproper : ¬ P ∣ Q)
    (y r : L)
    (hP : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P = 0)
    (hQ : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q = 0)
    (hgenerate : IntermediateField.adjoin K ({y, r} : Set L) = ⊤) :
    FiniteDimensional K L := by
  classical
  let resultant := Polynomial.resultant P Q P.natDegree Q.natDegree
  have hresne : resultant ≠ 0 :=
    PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
      P Q hirreducible hpositive hproper
  have hresroot : Polynomial.aeval y resultant = 0 :=
    PlaneRootSeparability.resultant_aeval_eq_zero_of_common_root P Q
      P.natDegree Q.natDegree le_rfl le_rfl
      (Or.inl (Nat.ne_of_gt hpositive)) y r hP hQ
  have hy : IsIntegral K y := IsAlgebraic.isIntegral ⟨resultant, hresne, hresroot⟩
  let S : IntermediateField K L := IntermediateField.adjoin K {y}
  let yS : S := ⟨y, IntermediateField.mem_adjoin_simple_self K y⟩
  letI : DecidableEq S := Classical.decEq S
  let g : Polynomial K →+* S := Polynomial.eval₂RingHom (algebraMap K S) yS
  let Py : Polynomial S := P.map g
  have hPyne : Py ≠ 0 := by
    have h := PlaneCoefficientExtension.bimap_specialization_ne_zero
      (algebraMap K S) P (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
    rw [PlaneCoefficientExtension.bimap_specialization] at h
    exact h
  have hcoefficient : (algebraMap S L).comp g =
      Polynomial.eval₂RingHom (algebraMap K L) y := by
    apply Polynomial.ringHom_ext
    · intro c
      change algebraMap S L
          (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c)) =
        Polynomial.eval₂ (algebraMap K L) y (Polynomial.C c)
      rw [Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K S L c).symm
    · change algebraMap S L
          (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X) =
        Polynomial.eval₂ (algebraMap K L) y Polynomial.X
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X]
      rfl
  have hPyroot : Polynomial.aeval r Py = 0 := by
    change Polynomial.eval₂ (algebraMap S L) r (P.map g) = 0
    rw [Polynomial.eval₂_map, hcoefficient]
    exact hP
  have hrS : IsIntegral S r := IsAlgebraic.isIntegral ⟨Py, hPyne, hPyroot⟩
  letI : FiniteDimensional K S :=
    IntermediateField.finiteDimensional_adjoin_simple hy
  have hrK : IsIntegral K r := hrS.trans_isAlgebraic.isIntegral
  exact finite_of_two_integral_generators y r hy hrK hgenerate

#print axioms finite_of_two_integral_generators
#print axioms finite_of_proper_plane_roots

end

end PHJFRI.Stage3.PlaneRootFiniteness
