module
public import FoliationQM.IntrinsicAtlasComparison
public import FoliationQM.LorentzLocalPaths

/-!
# Local Lorentz gauge paths on a point-indexed refinement

For v13 `prop:takabayasi`, shrink a chart around each base point to the
inverse image of a Cayley neighborhood of its gauge value. Restricting
the actual continuous gauge then gives joint paths on this refinement.
This proves all-cover gauge comparison on a locally path connected base
for independently supplied joint transition families.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzGaugeRefinement
open LorentzMatrixGroup PathTransitionData IntrinsicPathGauge CliffordSpinCoverRefinement
open GlobalIntrinsicPathObstruction BasedPathGroup

variable {B ι : Type*} [TopologicalSpace B] {D E : Data ProperFutureLorentz B ι}

/-- Choose a chart containing the anchor point. -/
def parent (D : Data ProperFutureLorentz B ι) (a : B) : ι := Classical.choose (D.covers a)

/-- The chosen original chart contains its anchor point. -/
theorem mem_parent (D : Data ProperFutureLorentz B ι) (a : B) : a ∈ D.domain (parent D a) :=
  Classical.choose_spec (D.covers a)

/-- Shrink the chosen chart to the open preimage of a local Lorentz path domain. -/
def domain (A : Gauge D) (a : B) : TopologicalSpace.Opens B :=
  ⟨(D.domain (parent D a) : Set B) ∩ (A.value (parent D a)) ⁻¹'
      (LorentzLocalPaths.neighborhood (A.value (parent D a) a) : Set ProperFutureLorentz),
    (A.continuous_value _).isOpen_inter_preimage (D.domain _).isOpen
      (LorentzLocalPaths.neighborhood _).isOpen⟩

/-- Each shrunken chart contains the point used to choose it. -/
theorem mem_domain (A : Gauge D) (a : B) : a ∈ domain A a :=
  ⟨mem_parent D a, LorentzLocalPaths.mem_neighborhood _⟩

/-- The shrunken chart domains form an actual open refinement of the given cover. -/
def refinement (A : Gauge D) : Refinement D.domain B where
  parent := parent D
  domain := domain A
  covers a := ⟨a, mem_domain A a⟩
  subset _ _ h := h.1

/-- Restrict the chart gauges along the designated parent assignment. -/
def gauge (A : Gauge D) : Gauge (IntrinsicPathRestriction.data D (refinement A)) where
  value a := A.value (parent D a)
  continuous_value a := (A.continuous_value _).mono ((refinement A).subset a)

/-- The original chart gauge takes values in the selected Cayley neighborhood throughout the shrunken chart. -/
def coordinate (A : Gauge D) (a : B) :
    C(↥(domain A a), ↥(LorentzLocalPaths.neighborhood (A.value (parent D a) a))) :=
  ⟨fun x => ⟨A.value (parent D a) x, x.property.2⟩,
    ((A.continuous_value _).comp_continuous continuous_subtype_val (fun x => x.property.1)).subtype_mk _⟩

/-- The actual local paths composed with the continuous gauge give joint
identity-to-gauge paths on every domain of the constructed refinement. -/
def paths (A : Gauge D) : GaugePaths (gauge A) where
  homotopy a := (LorentzLocalPaths.joint (A.value (parent D a) a)).comp
    ⟨fun z => (z.1, coordinate A a z.2),
      continuous_fst.prodMk ((coordinate A a).continuous.comp continuous_snd)⟩
  source a x := LorentzLocalPaths.joint_zero _ (coordinate A a x)
  target a x := LorentzLocalPaths.joint_one _ (coordinate A a x)

/-- The all-cover obstruction agrees across a continuous Lorentz chart
gauge on true overlaps. The target's local geometry supplies all gauge paths. -/
theorem obstruction_eq [LocallyPathConnectedSpace B]
    (e : (projection (G := ProperFutureLorentz)).ker →* Multiplicative (ZMod 2))
    (P : Family D) (Q : Family E) (A : Gauge D) (hd : D.domain = E.domain)
    (ht : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      A.value j x * D.transition i j x * (A.value i x)⁻¹ = E.transition i j x) :
    obstruction e P = obstruction e Q := by
  let R := refinement A
  let S : Refinement E.domain B :=
    { parent := R.parent
      domain := R.domain
      covers := R.covers
      subset := fun a => by rw [← hd]; exact R.subset a }
  apply (restrict e P R).symm.trans
  apply Eq.trans _ (restrict e Q S)
  exact IntrinsicAtlasComparison.obstruction_of_gaugePaths e
    (IntrinsicPathRestriction.family P R) (IntrinsicPathRestriction.family Q S)
    (gauge A) (paths A) rfl (fun i j x hi hj =>
      ht (R.parent i) (R.parent j) x (R.subset i hi) (R.subset j hj))

end FoliationQM.LorentzGaugeRefinement
