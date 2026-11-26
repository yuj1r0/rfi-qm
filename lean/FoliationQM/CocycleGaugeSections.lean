module
public import FoliationQM.CocycleGaugeBundles
public import FoliationQM.CocycleGaugeFamilies
public import FoliationQM.PolarCocycleSections

/-!
# Smooth cocycle sections under a change of local matrix frames

Source: coordinate independence of the supplied-cocycle interpretation of
v13 `prop:takabayasi`. A supplied local matrix frame change is smooth on
each actual open chart domain. The transformed transitions are derived
from those matrices, with their ordinary cocycle laws proved separately.
The actual total-space gauge diffeomorphisms induce genuine bijections of
sections independently defined by smoothness of their total-space graphs.

The selected chart index occurs only in the fiber-coordinate formula.
Smoothness follows the actual total-space diffeomorphisms, whose local
expressions use the smooth chartwise matrix fields. The graph maps and
previous compatible-local-family maps agree exactly, commute with actual
polar realization, and preserve the actual invariant density. No global
smoothness of a chosen chart index, abstract Spin identification, or
covariance of a differentiated field equation is inferred.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CocycleGaugeSections
open DiracMatrices PolarSignQuotient SourcePolarProductQuotient
open PolarTransitionCocycle PolarCocycleBundles PolarCocycleSections
open CocycleGaugeTransform

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {ι : Type*} {n : WithTop ℕ∞}
  (D : Data I B ι n) (h : FrameChange D) [IsManifold I n B]

/-- A supplied local frame change gives a genuine bijection of actual graph-smooth polar sections of the original and transformed cocycle bundles. -/
def polarSectionEquiv : PolarSection D ≃ PolarSection (transformed D h) where
  toFun s := ⟨fun x => DensityFrameAction.productAction (h.value (indexAt D x) x) (s.val x),
    (CocycleGaugeBundles.polarDiffeomorph D h).contMDiff.comp s.property⟩
  invFun s := ⟨fun x => DensityFrameAction.productAction (h.value (indexAt D x) x)⁻¹ (s.val x),
    (CocycleGaugeBundles.polarDiffeomorph D h).symm.contMDiff.comp s.property⟩
  left_inv s := Subtype.ext (funext fun x => DensityFrameAction.productAction_inv_left _ (s.val x))
  right_inv s := Subtype.ext (funext fun x => DensityFrameAction.productAction_inv_right _ (s.val x))

/-- The actual represented matrix action gives the corresponding genuine bijection of graph-smooth regular-spinor sections. -/
def spinorSectionEquiv : SpinorSection D ≃ SpinorSection (transformed D h) where
  toFun s := ⟨fun x => RegularSpinorAction.act (h.value (indexAt D x) x) (s.val x),
    (CocycleGaugeBundles.spinorDiffeomorph D h).contMDiff.comp s.property⟩
  invFun s := ⟨fun x => RegularSpinorAction.act (h.value (indexAt D x) x)⁻¹ (s.val x),
    (CocycleGaugeBundles.spinorDiffeomorph D h).symm.contMDiff.comp s.property⟩
  left_inv s := Subtype.ext (funext fun x => RegularSpinorAction.act_inv_act _ (s.val x))
  right_inv s := Subtype.ext (funext fun x => RegularSpinorAction.act_act_inv _ (s.val x))

/-- The changed polar section uses the actual matrix action in the selected actual fiber coordinate. -/
theorem polarSectionEquiv_apply (s : PolarSection D) (x : B) :
    (polarSectionEquiv D h s).val x =
      DensityFrameAction.productAction (h.value (indexAt D x) x) (s.val x) := rfl

/-- Inverse polar section change uses the true inverse matrix in that same actual fiber coordinate. -/
theorem polarSectionEquiv_symm_apply (s : PolarSection (transformed D h)) (x : B) :
    ((polarSectionEquiv D h).symm s).val x =
      DensityFrameAction.productAction (h.value (indexAt D x) x)⁻¹ (s.val x) := rfl

/-- The changed regular-spinor section uses the independently defined represented matrix action. -/
theorem spinorSectionEquiv_apply (s : SpinorSection D) (x : B) :
    (spinorSectionEquiv D h s).val x =
      RegularSpinorAction.act (h.value (indexAt D x) x) (s.val x) := rfl

/-- Inverse regular-spinor section change uses the actual represented inverse matrix. -/
theorem spinorSectionEquiv_symm_apply (s : SpinorSection (transformed D h)) (x : B) :
    ((spinorSectionEquiv D h).symm s).val x =
      RegularSpinorAction.act (h.value (indexAt D x) x)⁻¹ (s.val x) := rfl

/-- The actual polar gauge total-space diffeomorphism maps each smooth section graph exactly to the changed section graph. -/
theorem polarSectionEquiv_graph (s : PolarSection D) (x : B) :
    CocycleGaugeBundles.polarDiffeomorph D h (⟨x, s.val x⟩ : PolarTotal D) =
      (⟨x, (polarSectionEquiv D h s).val x⟩ : PolarTotal (transformed D h)) := rfl

/-- The actual represented-spinor total-space gauge diffeomorphism commutes exactly with smooth section graphs. -/
theorem spinorSectionEquiv_graph (s : SpinorSection D) (x : B) :
    CocycleGaugeBundles.spinorDiffeomorph D h (⟨x, s.val x⟩ : SpinorTotal D) =
      (⟨x, (spinorSectionEquiv D h s).val x⟩ : SpinorTotal (transformed D h)) := rfl

/-- In every actual chart, the changed graph-smooth polar section agrees exactly with the previously constructed compatible local-family change. -/
theorem polarSectionEquiv_family (s : PolarSection D) :
    PolarCocycleSections.polarFamilyEquiv (transformed D h) (polarSectionEquiv D h s) =
      CocycleGaugeFamilies.polarFamilyEquiv D h (PolarCocycleSections.polarFamilyEquiv D s) := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  exact congrArg Prod.snd
    (CocycleGaugeBundles.localTriv_polarMap D h i (⟨x.val, s.val x.val⟩ : PolarTotal D))

/-- The changed graph-smooth regular-spinor section has precisely the compatible represented local-family gauge coordinates. -/
theorem spinorSectionEquiv_family (s : SpinorSection D) :
    PolarCocycleSections.spinorFamilyEquiv (transformed D h) (spinorSectionEquiv D h s) =
      CocycleGaugeFamilies.spinorFamilyEquiv D h (PolarCocycleSections.spinorFamilyEquiv D s) := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  exact congrArg Prod.snd
    (CocycleGaugeBundles.localTriv_spinorMap D h i (⟨x.val, s.val x.val⟩ : SpinorTotal D))

/-- Actual section realization commutes with changing the local matrix frames, for the independently constructed gauge maps. -/
theorem realization_commutes (s : PolarSection D) :
    PolarCocycleSections.sectionEquiv (transformed D h) (polarSectionEquiv D h s) =
      spinorSectionEquiv D h (PolarCocycleSections.sectionEquiv D s) := by
  apply Subtype.ext
  funext x
  exact RegularSpinorAction.realization_equivariant _ (s.val x)

/-- Actual inverse polar reconstruction commutes with undoing the local matrix-frame change. -/
theorem reconstruction_commutes (s : SpinorSection (transformed D h)) :
    (polarSectionEquiv D h).symm ((PolarCocycleSections.sectionEquiv (transformed D h)).symm s) =
      (PolarCocycleSections.sectionEquiv D).symm ((spinorSectionEquiv D h).symm s) := by
  apply Subtype.ext
  funext x
  exact (RegularSpinorAction.reconstruction_equivariant _ (s.val x)).symm

/-- Actual positive density of a polar section is unchanged by any supplied local frame change. -/
theorem polarSectionEquiv_density (s : PolarSection D) (x : B) :
    ((polarSectionEquiv D h s).val x).1 = (s.val x).1 := rfl

/-- The actual scalar-pseudoscalar bilinear invariant density of the original spinor section is unchanged by the represented local frame change. -/
theorem spinorSectionEquiv_density (s : SpinorSection D) (x : B) :
    SpinorRegularity.invariantDensity ((spinorSectionEquiv D h s).val x).val =
      SpinorRegularity.invariantDensity (s.val x).val :=
  RegularSpinorAction.invariantDensity_act _ (s.val x)

end FoliationQM.CocycleGaugeSections
