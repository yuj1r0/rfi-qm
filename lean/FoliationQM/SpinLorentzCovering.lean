module
public import FoliationQM.LorentzMatrixTopology
public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Covering.Quotient

/-!
# The actual two-sheet special linear covering of the full Lorentz target

Source scope: the concrete special linear Lorentz covering associated
with v13 `prop:takabayasi` and `eq:tetrad_rotor_map`. The previously
constructed homomorphism is continuous and surjective onto the
independently specified full proper future Lorentz group. Natural
source sigma compactness and target Baire separation give an actual
open mapping theorem. Its proved discrete two-element kernel then
supplies a genuine covering in these unchanged topologies.

Every target has an evenly covered neighborhood with discrete fiber
Fin 2. Actual local inverses give continuous local sections through
any specified lift, and continuous fields have corresponding anchored
local lifts. Continuous lifts on a preconnected domain are determined
by one value. No global individual section, universal-cover property,
target smooth atlas, or abstract Clifford spin-group identification is
asserted by these topological statements.
-/

@[expose] public section
noncomputable section
open scoped Topology
open Set Topology
namespace FoliationQM.SpinLorentzCovering
open SourcePolarDatum LorentzMatrixGroup SpinLorentzOrientation SpinLorentzSurjective
open SpinLorentzSignQuotient

/-- The actual full Lorentz homomorphism is open for the unchanged natural group topologies, by the sigma-compact open mapping theorem. -/
theorem isOpenMap_properFutureHom : IsOpenMap properFutureHom :=
  properFutureHom.isOpenMap_of_sigmaCompact properFutureHom_surjective continuous_properFutureHom

/-- The actual full Lorentz homomorphism is a quotient map, using its proved continuity, openness, and full surjectivity. -/
theorem isQuotientMap_properFutureHom : IsQuotientMap properFutureHom :=
  isOpenMap_properFutureHom.isQuotientMap continuous_properFutureHom properFutureHom_surjective

/-- The full Lorentz homomorphism is a quotient covering for its genuine discrete two-sign kernel. -/
theorem properFutureHom_isQuotientCoveringMap :
    IsQuotientCoveringMap properFutureHom SignKernel :=
  isQuotientMap_properFutureHom.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (SetLike.isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology SignKernel))

/-- The actual special linear map is a genuine covering of the entire independently defined proper future Lorentz group. -/
theorem properFutureHom_isCoveringMap : IsCoveringMap properFutureHom :=
  properFutureHom_isQuotientCoveringMap.isCoveringMap

/-- The actual Lorentz map is a local homeomorphism at every special linear matrix. -/
theorem properFutureHom_isLocalHomeomorph : IsLocalHomeomorph properFutureHom :=
  properFutureHom_isCoveringMap.isLocalHomeomorph

/-- Each actual Lorentz fiber is equivalent to Fin 2 through its genuine kernel torsor and the already classified two signs. -/
def fiberEquivTwo (L : ProperFutureLorentz) : (properFutureHom ⁻¹' {L}) ≃ Fin 2 :=
  (properFutureHom_isQuotientCoveringMap.fiberEquivGroup
    ⟨(properFutureHom_surjective L).choose, (properFutureHom_surjective L).choose_spec⟩).trans
    (boolKernelEquiv.symm.trans finTwoEquiv.symm)

/-- Every independently specified Lorentz target point has a genuine evenly covered neighborhood with discrete fiber Fin 2. -/
theorem properFutureHom_isEvenlyCovered_two (L : ProperFutureLorentz) :
    IsEvenlyCovered properFutureHom L (Fin 2) := by
  let := (properFutureHom_isCoveringMap L).discreteTopology_fiber
  exact (properFutureHom_isCoveringMap L).of_fiber_homeomorph
    (fiberEquivTwo L).toHomeomorphOfDiscrete

/-- The actual full Lorentz map is a covering and every one of its fibers has cardinality exactly two. -/
theorem properFutureHom_two_sheeted :
    IsCoveringMap properFutureHom ∧
      ∀ L : ProperFutureLorentz, Nat.card (properFutureHom ⁻¹' {L}) = 2 :=
  ⟨properFutureHom_isCoveringMap, natCard_lorentzFiber⟩

/-- An actual open partial inverse to the full Lorentz map anchored at a prescribed special linear representative. -/
def localInverseAt (A : SpecialLinearMatrix) :
    OpenPartialHomeomorph ProperFutureLorentz SpecialLinearMatrix :=
  properFutureHom_isLocalHomeomorph.localInverseAt A

/-- The image of the prescribed representative belongs to the genuine open domain of its anchored local inverse. -/
theorem image_mem_localInverseAt_source (A : SpecialLinearMatrix) :
    properFutureHom A ∈ (localInverseAt A).source :=
  properFutureHom_isLocalHomeomorph.apply_self_mem_localInverseAt_source

/-- The chosen actual local inverse returns exactly its prescribed representative at that representative's image. -/
theorem localInverseAt_image (A : SpecialLinearMatrix) :
    localInverseAt A (properFutureHom A) = A :=
  properFutureHom_isLocalHomeomorph.localInverseAt_apply_self

/-- The actual Lorentz image of the local inverse equals every target in its genuine open domain. -/
theorem image_localInverseAt {A : SpecialLinearMatrix} {L : ProperFutureLorentz}
    (hL : L ∈ (localInverseAt A).source) :
    properFutureHom (localInverseAt A L) = L :=
  properFutureHom_isLocalHomeomorph.apply_localInverseAt_of_mem hL

/-- Every prescribed special linear lift extends to a continuous local section on an actual open neighborhood of its Lorentz image. -/
theorem exists_local_section (A : SpecialLinearMatrix) :
    ∃ U : Set ProperFutureLorentz, IsOpen U ∧ properFutureHom A ∈ U ∧
      ∃ s : ProperFutureLorentz → SpecialLinearMatrix,
        ContinuousOn s U ∧ s (properFutureHom A) = A ∧
          ∀ L ∈ U, properFutureHom (s L) = L := by
  refine ⟨(localInverseAt A).source, (localInverseAt A).open_source,
    image_mem_localInverseAt_source A, localInverseAt A,
    (localInverseAt A).continuousOn, localInverseAt_image A, ?_⟩
  intro L hL
  exact image_localInverseAt hL

/-- A continuous Lorentz-valued field has a continuous local special linear lift through every prescribed representative of its value. -/
theorem exists_local_lift {X : Type*} [TopologicalSpace X]
    (f : X → ProperFutureLorentz) (hf : Continuous f) (x : X)
    (A : SpecialLinearMatrix) (hA : f x = properFutureHom A) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ s : X → SpecialLinearMatrix, ContinuousOn s U ∧ s x = A ∧
        ∀ y ∈ U, properFutureHom (s y) = f y := by
  obtain ⟨V, hV, hAV, s, hs, hsA, hsec⟩ := exists_local_section A
  refine ⟨f ⁻¹' V, hV.preimage hf, ?_, s ∘ f,
    hs.comp hf.continuousOn (fun _ hy => hy), ?_, ?_⟩
  · simpa only [Set.mem_preimage, hA] using hAV
  · exact (congrArg s hA).trans hsA
  · intro y hy
    exact hsec (f y) hy

/-- Two continuous lifts on a preconnected base agree everywhere if their Lorentz images and one prescribed lift value agree. -/
theorem continuous_lift_unique {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → SpecialLinearMatrix} (hf : Continuous f) (hg : Continuous g)
    (he : properFutureHom ∘ f = properFutureHom ∘ g) (x : X) (hx : f x = g x) : f = g :=
  properFutureHom_isCoveringMap.eq_of_comp_eq hf hg he x hx

end FoliationQM.SpinLorentzCovering
