module
public import FoliationQM.ModTwoAllCover
public import FoliationQM.SpinModTwoComparison
public import FoliationQM.SpinHTwoUniversal

/-!
# Comparing global physical signs with independent mod-two cohomology

For the Spin-frame component of v13 `prop:takabayasi`, the proved
coefficient equivalence commutes with restriction and therefore induces
an additive equivalence over all covers. The target is the independently
defined locally constant cohomology group. In particular it does not
depend on a differentiability order. This is a coefficient comparison,
not an identification with a conventionally constructed characteristic class.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalModTwoComparison
open SpinHOneDirected SpinModTwoComparison

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞)

/-- Convert every smooth Clifford sign class into its independent additive mod-two class. -/
def toModTwo : Additive (SpinAllCoverHTwo.GlobalH2 I B n) →+ ModTwoAllCover.GlobalH2 B :=
  (SpinHTwoUniversal.descend
    (fun P => ((ModTwoAllCover.ofPoint P).comp (classEquiv I P.domain n).toAddMonoidHom).toMultiplicativeRight)
    (by
      intro P Q h c
      change Multiplicative.ofAdd (ModTwoAllCover.ofPoint Q
        (classEquiv I Q.domain n (Additive.ofMul (SpinHTwoDirected.transition I n P Q h c)))) =
          Multiplicative.ofAdd (ModTwoAllCover.ofPoint P (classEquiv I P.domain n (Additive.ofMul c)))
      exact congrArg Multiplicative.ofAdd
        ((congrArg (ModTwoAllCover.ofPoint Q)
          (classEquiv_restrict (I := I) (n := n) (refine h) c)).trans
            (ModTwoAllCover.ofPoint_transition h _)))).toAdditiveLeft

/-- Decode locally constant mod-two coefficients as actual smooth Clifford signs. -/
def fromModTwo : ModTwoAllCover.GlobalH2 B →+ Additive (SpinAllCoverHTwo.GlobalH2 I B n) :=
  ModTwoAllCover.descend
    (fun P => (SpinAllCoverHTwo.ofPoint P).toAdditive.comp (classEquiv I P.domain n).symm.toAddMonoidHom)
    (by
      intro P Q h c
      have he : (classEquiv I Q.domain n).symm (ModTwoAllCover.transition P Q h c) =
          Additive.ofMul (SpinHTwoDirected.transition I n P Q h
            ((classEquiv I P.domain n).symm c).toMul) := by
        apply (classEquiv I Q.domain n).injective
        rw [AddEquiv.apply_symm_apply]
        exact ((classEquiv_restrict (I := I) (n := n) (refine h)
          ((classEquiv I P.domain n).symm c).toMul).trans
            (congrArg (ModTwoRestriction.restrictHom (refine h))
              ((classEquiv I P.domain n).apply_symm_apply c))).symm
      change Additive.ofMul (SpinAllCoverHTwo.ofPoint Q
        ((classEquiv I Q.domain n).symm (ModTwoAllCover.transition P Q h c)).toMul) =
          Additive.ofMul (SpinAllCoverHTwo.ofPoint P ((classEquiv I P.domain n).symm c).toMul)
      rw [he]
      exact congrArg Additive.ofMul (SpinAllCoverHTwo.ofPoint_transition h _))

/-- The global forward map is exactly the coefficient change on every point-cover representative. -/
theorem toModTwo_ofPoint (P : Cover B) (c : SpinSignCohomology.ObstructionClass I P.domain n) :
    toModTwo I n (Additive.ofMul (SpinAllCoverHTwo.ofPoint P c)) =
      ModTwoAllCover.ofPoint P (classEquiv I P.domain n (Additive.ofMul c)) := rfl

/-- The global reverse map decodes each point-cover representative to its physical signs. -/
theorem fromModTwo_ofPoint (P : Cover B) (c : ModTwoCohomology.H2 P.domain) :
    fromModTwo I n (ModTwoAllCover.ofPoint P c) =
      Additive.ofMul (SpinAllCoverHTwo.ofPoint P ((classEquiv I P.domain n).symm c).toMul) := rfl

/-- Global smooth sign cohomology is additively equivalent to independently defined mod-two cohomology. -/
def coefficientEquiv : Additive (SpinAllCoverHTwo.GlobalH2 I B n) ≃+ ModTwoAllCover.GlobalH2 B where
  toFun := toModTwo I n
  invFun := fromModTwo I n
  left_inv c := by
    obtain ⟨P, a, ha⟩ := SpinAllCoverHTwo.exists_representative c.toMul
    have h : c = Additive.ofMul (SpinAllCoverHTwo.ofPoint P a) := ha
    rw [h, toModTwo_ofPoint, fromModTwo_ofPoint, AddEquiv.symm_apply_apply]
    rfl
  right_inv c := by
    obtain ⟨P, a, rfl⟩ := ModTwoAllCover.exists_representative c
    rw [fromModTwo_ofPoint, toModTwo_ofPoint]
    change ModTwoAllCover.ofPoint P (classEquiv I P.domain n ((classEquiv I P.domain n).symm a)) = _
    rw [AddEquiv.apply_symm_apply]
  map_add' := (toModTwo I n).map_add

/-- The equivalence retains the actual coefficient change on representatives. -/
theorem coefficientEquiv_ofPoint (P : Cover B)
    (c : SpinSignCohomology.ObstructionClass I P.domain n) :
    coefficientEquiv I n (Additive.ofMul (SpinAllCoverHTwo.ofPoint P c)) =
      ModTwoAllCover.ofPoint P (classEquiv I P.domain n (Additive.ofMul c)) := rfl

/-- On any indexed cover, coefficient comparison commutes with its canonical global map. -/
theorem coefficientEquiv_ofCover {ι : Type*} (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (c : SpinSignCohomology.ObstructionClass I U n) :
    coefficientEquiv I n (Additive.ofMul (SpinAllCoverHTwo.ofCover U hU c)) =
      ModTwoAllCover.ofCover U hU (classEquiv I U n (Additive.ofMul c)) := by
  change ModTwoAllCover.ofPoint (anchor U hU)
      (classEquiv I (anchor U hU).domain n
        (Additive.ofMul (SpinSignHTwo.restrictHom (SignCommonRefinement.pointCover U hU) c))) = _
  exact congrArg (ModTwoAllCover.ofPoint (anchor U hU))
    (classEquiv_restrict (I := I) (n := n) (SignCommonRefinement.pointCover U hU) c)

/-- The independent additive zero detects exactly the original global sign identity. -/
theorem coefficientEquiv_eq_zero_iff (c : SpinAllCoverHTwo.GlobalH2 I B n) :
    coefficientEquiv I n (Additive.ofMul c) = 0 ↔ c = 1 :=
  (coefficientEquiv I n).map_eq_zero_iff (x := Additive.ofMul c)

/-- Changing the differentiability order preserves global degree-two sign cohomology canonically. -/
def regularityEquiv (m : WithTop ℕ∞) :
    Additive (SpinAllCoverHTwo.GlobalH2 I B n) ≃+ Additive (SpinAllCoverHTwo.GlobalH2 I B m) :=
  (coefficientEquiv I n).trans (coefficientEquiv I m).symm

/-- The regularity equivalence preserves the class in the same independent coefficient group. -/
theorem regularityEquiv_coefficients (m : WithTop ℕ∞)
    (c : Additive (SpinAllCoverHTwo.GlobalH2 I B n)) :
    coefficientEquiv I m (regularityEquiv I n m c) = coefficientEquiv I n c :=
  (coefficientEquiv I m).apply_symm_apply _

end FoliationQM.GlobalModTwoComparison
