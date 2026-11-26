module
public import FoliationQM.CliffordSpinTopology
public import FoliationQM.CliffordSpinLorentz
public import FoliationQM.SpinLorentzCovering

/-!
# The genuine Clifford Spin covering of the proper future Lorentz group

Source scope: the abstract spin-frame identification in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The source is Mathlib's actual
Minkowski spin group with the subtype topology inherited from the
independently specified real Clifford module topology. The target is
the independently defined proper future Lorentz group with its existing
natural topology. The proved Spin-to-matrix homeomorphism transfers the
actual matrix covering to this literal Clifford homomorphism.

Every Lorentz fiber is homeomorphic to its actual matrix fiber and has
two elements. Genuine open partial inverses yield continuous local
sections through any prescribed Spin lift, and continuous lifts on a
preconnected domain are determined by one value. The natural group
quotient by the exact sign kernel is multiplicatively homeomorphic to
the full Lorentz target. Its inverse selects only a sign class. No
global individual section, universal-cover property, or smooth
Spin/Lorentz atlas identification is asserted.
-/

@[expose] public section
noncomputable section
open scoped Topology
open Set Topology
namespace FoliationQM.CliffordSpinCovering
open CliffordSpinMap CliffordSpinTopology CliffordSpinLorentz LorentzMatrixGroup

/-- The actual Clifford Spin homomorphism is a covering in the independently fixed natural topologies. -/
theorem lorentzHom_isCoveringMap : IsCoveringMap lorentzHom := by
  simpa only [Function.comp_def, spinHomeomorph_apply, ← lorentzHom_apply] using
    SpinLorentzCovering.properFutureHom_isCoveringMap.comp_homeomorph spinHomeomorph

/-- The genuine Clifford homomorphism is a local homeomorphism at every Spin element. -/
theorem lorentzHom_isLocalHomeomorph : IsLocalHomeomorph lorentzHom :=
  lorentzHom_isCoveringMap.isLocalHomeomorph

/-- The actual Spin-to-matrix homeomorphism identifies each Clifford Lorentz fiber with its genuine matrix fiber. -/
def lorentzFiberHomeomorph (L : ProperFutureLorentz) :
    (lorentzHom ⁻¹' {L}) ≃ₜ (SpinLorentzOrientation.properFutureHom ⁻¹' {L}) :=
  spinHomeomorph.subtype (fun s => by
    change lorentzHom s = L ↔ SpinLorentzOrientation.properFutureHom (spinHomeomorph s) = L
    rw [spinHomeomorph_apply, lorentzHom_apply])

/-- Each actual Clifford Lorentz fiber is equivalent to the two-element type through its proved matrix fiber. -/
def lorentzFiberEquiv (L : ProperFutureLorentz) : (lorentzHom ⁻¹' {L}) ≃ Fin 2 :=
  (lorentzFiberHomeomorph L).toEquiv.trans (SpinLorentzCovering.fiberEquivTwo L)

/-- Every independently specified proper future Lorentz element has exactly two genuine Clifford Spin lifts. -/
theorem lorentz_fiber_card (L : ProperFutureLorentz) :
    Nat.card (lorentzHom ⁻¹' {L}) = 2 := by
  simpa using Nat.card_congr (lorentzFiberEquiv L)

/-- Every Lorentz point has an evenly covered neighborhood with the actual discrete fiber Fin 2. -/
theorem lorentzHom_isEvenlyCovered_two (L : ProperFutureLorentz) :
    IsEvenlyCovered lorentzHom L (Fin 2) := by
  let := (lorentzHom_isCoveringMap L).discreteTopology_fiber
  exact (lorentzHom_isCoveringMap L).of_fiber_homeomorph
    (lorentzFiberEquiv L).toHomeomorphOfDiscrete

/-- The genuine Clifford homomorphism is a covering with exactly two elements in every fiber. -/
theorem lorentzHom_two_sheeted :
    IsCoveringMap lorentzHom ∧
      ∀ L : ProperFutureLorentz, Nat.card (lorentzHom ⁻¹' {L}) = 2 :=
  ⟨lorentzHom_isCoveringMap, lorentz_fiber_card⟩

/-- An actual open partial inverse of the Clifford Lorentz map chosen through a prescribed Spin lift. -/
def localInverseAt (s : Spin) : OpenPartialHomeomorph ProperFutureLorentz Spin :=
  lorentzHom_isLocalHomeomorph.localInverseAt s

/-- The image of the prescribed Spin lift lies in the open domain of its actual local inverse. -/
theorem image_mem_localInverseAt_source (s : Spin) :
    lorentzHom s ∈ (localInverseAt s).source :=
  lorentzHom_isLocalHomeomorph.apply_self_mem_localInverseAt_source

/-- The actual local inverse returns precisely the prescribed Spin lift at its Lorentz image. -/
theorem localInverseAt_image (s : Spin) : localInverseAt s (lorentzHom s) = s :=
  lorentzHom_isLocalHomeomorph.localInverseAt_apply_self

/-- The Clifford Lorentz image of the local inverse returns every point in its genuine open domain. -/
theorem image_localInverseAt {s : Spin} {L : ProperFutureLorentz}
    (hL : L ∈ (localInverseAt s).source) : lorentzHom (localInverseAt s L) = L :=
  lorentzHom_isLocalHomeomorph.apply_localInverseAt_of_mem hL

/-- Every prescribed genuine Spin lift extends to a continuous local section on an open Lorentz neighborhood. -/
theorem exists_local_section (s : Spin) :
    ∃ U : Set ProperFutureLorentz, IsOpen U ∧ lorentzHom s ∈ U ∧
      ∃ f : ProperFutureLorentz → Spin, ContinuousOn f U ∧ f (lorentzHom s) = s ∧
        ∀ L ∈ U, lorentzHom (f L) = L := by
  refine ⟨(localInverseAt s).source, (localInverseAt s).open_source,
    image_mem_localInverseAt_source s, localInverseAt s,
    (localInverseAt s).continuousOn, localInverseAt_image s, ?_⟩
  intro L hL
  exact image_localInverseAt hL

/-- A continuous Lorentz-valued field has a continuous local Clifford Spin lift through every specified lift of its value. -/
theorem exists_local_lift {X : Type*} [TopologicalSpace X]
    (f : X → ProperFutureLorentz) (hf : Continuous f) (x : X)
    (s : Spin) (hs : f x = lorentzHom s) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ g : X → Spin, ContinuousOn g U ∧ g x = s ∧
        ∀ y ∈ U, lorentzHom (g y) = f y := by
  obtain ⟨V, hV, hsV, g, hg, hgs, hsec⟩ := exists_local_section s
  refine ⟨f ⁻¹' V, hV.preimage hf, ?_, g ∘ f,
    hg.comp hf.continuousOn (fun _ hy => hy), ?_, ?_⟩
  · simpa only [Set.mem_preimage, hs] using hsV
  · exact (congrArg g hs).trans hgs
  · intro y hy
    exact hsec (f y) hy

/-- Two continuous Spin lifts over a preconnected base coincide if their Lorentz images and one lift value coincide. -/
theorem continuous_lift_unique {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → Spin} (hf : Continuous f) (hg : Continuous g)
    (he : lorentzHom ∘ f = lorentzHom ∘ g) (x : X) (hx : f x = g x) : f = g :=
  lorentzHom_isCoveringMap.eq_of_comp_eq hf hg he x hx

/-- The natural group quotient of the actual Clifford Spin group by its proved two-sign kernel. -/
abbrev SignQuotient := Spin ⧸ lorentzHom.ker

/-- The actual Clifford sign quotient is multiplicatively homeomorphic to the full independently defined Lorentz target, without replacing either topology. -/
def quotientMulHomeomorph : SignQuotient ≃ₜ* ProperFutureLorentz := by
  let e : SignQuotient ≃* ProperFutureLorentz :=
    QuotientGroup.quotientKerEquivOfSurjective lorentzHom lorentzHom_surjective
  have hc : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk lorentzHom.ker).continuous_iff.mpr
    exact lorentzHom_isCoveringMap.continuous
  have ho : IsOpenMap e := by
    apply IsOpenMap.of_comp
      (f := (QuotientGroup.mk : Spin → SignQuotient))
      QuotientGroup.continuous_mk QuotientGroup.mk_surjective
    exact lorentzHom_isCoveringMap.isOpenMap
  exact {
    toMulEquiv := e
    continuous_toFun := hc
    continuous_invFun :=
      (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).continuous_symm }

/-- The quotient homeomorphism sends every actual sign class to the original Clifford Lorentz image. -/
theorem quotientMulHomeomorph_mk (s : Spin) :
    quotientMulHomeomorph (QuotientGroup.mk s) = lorentzHom s := rfl

/-- Two actual Clifford quotient classes coincide exactly when their representatives differ by the genuine central sign. -/
theorem quotient_mk_eq_iff (s t : Spin) :
    (QuotientGroup.mk s : SignQuotient) = QuotientGroup.mk t ↔
      s = t ∨ s = CliffordSpinEquivalence.negativeOne * t := by
  rw [← quotientMulHomeomorph.injective.eq_iff,
    quotientMulHomeomorph_mk, quotientMulHomeomorph_mk, lorentzHom_eq_iff]

/-- The continuous quotient inverse recovers the sign class of any displayed Spin lift, without selecting an individual representative. -/
theorem quotientMulHomeomorph_symm_image (s : Spin) :
    quotientMulHomeomorph.symm (lorentzHom s) = QuotientGroup.mk s :=
  quotientMulHomeomorph.symm_apply_apply (QuotientGroup.mk s)

end FoliationQM.CliffordSpinCovering
