module
public import FoliationQM.LorentzLocalPaths
public import FoliationQM.PresentedLorentzBundle

/-!
# Local Lorentz transition paths and normalized families

For the geometric frame component of v13 `prop:takabayasi`, each
transition has joint identity-to-transition paths near every point of
its overlap. If each off-diagonal transition image lies in a single
selected Cayley neighborhood, the whole atlas has a normalized
transition-path family and presents its actual Lorentz bundle.
-/

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace FoliationQM.LorentzLocalPathFamily
open LorentzMatrixGroup PathTransitionData

variable {X : Type*} [TopologicalSpace X]

/-- A continuous map landing in a selected Lorentz neighborhood has an actual joint homotopy
from the identity to the map, obtained by evaluation on the Cayley neighborhood. -/
def boundedJoint (F : C(X, ProperFutureLorentz)) (g : ProperFutureLorentz)
    (hg : ∀ x, F x ∈ LorentzLocalPaths.neighborhood g) : (ContinuousMap.const X 1).Homotopy F where
  toFun z := LorentzLocalPaths.joint g (z.1, ⟨F z.2, hg z.2⟩)
  continuous_toFun := (LorentzLocalPaths.joint g).continuous.comp
    (continuous_fst.prodMk ((F.continuous.comp continuous_snd).subtype_mk _))
  map_zero_left x := LorentzLocalPaths.joint_zero g ⟨F x, hg x⟩
  map_one_left x := LorentzLocalPaths.joint_one g ⟨F x, hg x⟩

variable {B ι : Type*} [TopologicalSpace B] (D : Data ProperFutureLorentz B ι)

/-- An open subset of the base around an overlap point on which the transition stays in
the chosen Lorentz neighborhood of its value at the point. -/
def patch (i j : ι) (a : pairOverlap D i j) : Opens B :=
  ⟨(pairOverlap D i j : Set B) ∩ (D.transition i j) ⁻¹'
      (LorentzLocalPaths.neighborhood (D.transition i j a) : Set ProperFutureLorentz),
    (D.continuous_transition i j).isOpen_inter_preimage
      (pairOverlap D i j).isOpen (LorentzLocalPaths.neighborhood _).isOpen⟩

/-- The overlap point used to construct the patch belongs to it. -/
theorem mem_patch (i j : ι) (a : pairOverlap D i j) : a.val ∈ patch D i j a :=
  ⟨a.property, LorentzLocalPaths.mem_neighborhood _⟩

/-- Every point of the patch lies in the original pair of charts. -/
theorem patch_subset (i j : ι) (a : pairOverlap D i j) : patch D i j a ≤ pairOverlap D i j :=
  fun _ hx => hx.1

/-- The actual transition at any point of the patch lies in the neighborhood at the anchor value. -/
theorem patch_image (i j : ι) (a : pairOverlap D i j) {b : B} (hb : b ∈ patch D i j a) :
    D.transition i j b ∈ LorentzLocalPaths.neighborhood (D.transition i j a) := hb.2

/-- The identity-to-transition paths on the patch vary jointly in time and base point. -/
def patchJoint (i j : ι) (a : pairOverlap D i j) : C(unitInterval × ↥(patch D i j a), ProperFutureLorentz) :=
  let F : C(↥(patch D i j a), ProperFutureLorentz) :=
    ⟨fun x => D.transition i j x,
      (D.continuous_transition i j).comp_continuous continuous_subtype_val (fun x => x.property.1)⟩
  (boundedJoint F (D.transition i j a) (fun x => x.property.2)).toContinuousMap

/-- Each patch path starts at the actual Lorentz group identity. -/
theorem patchJoint_zero (i j : ι) (a : pairOverlap D i j) (x : patch D i j a) :
    patchJoint D i j a (0, x) = 1 :=
  LorentzLocalPaths.joint_zero _ ⟨D.transition i j x, x.property.2⟩

/-- Each patch path ends at the supplied transition at that point of the true overlap. -/
theorem patchJoint_one (i j : ι) (a : pairOverlap D i j) (x : patch D i j a) :
    patchJoint D i j a (1, x) = D.transition i j x :=
  LorentzLocalPaths.joint_one _ ⟨D.transition i j x, x.property.2⟩

/-- Each off-diagonal transition image lies within one selected Cayley neighborhood.
The center may depend on the pair. -/
def PairBounded : Prop :=
  ∀ i j, i ≠ j → ∃ g : ProperFutureLorentz, ∀ x : pairOverlap D i j,
    D.transition i j x ∈ LorentzLocalPaths.neighborhood g

/-- It suffices to bound the transition images of the nonempty off-diagonal overlaps. -/
theorem pairBounded_iff_nonempty : PairBounded D ↔
    ∀ i j, i ≠ j → Nonempty ↥(pairOverlap D i j) →
      ∃ g : ProperFutureLorentz, ∀ x : pairOverlap D i j, D.transition i j x ∈ LorentzLocalPaths.neighborhood g := by
  classical
  refine ⟨fun h i j hij _ => h i j hij, ?_⟩
  intro h i j hij
  by_cases hn : Nonempty ↥(pairOverlap D i j)
  · exact h i j hij hn
  · exact ⟨1, fun x => (hn ⟨x⟩).elim⟩

/-- Choose the bounded homotopy on off-diagonal pairs and the constant identity homotopy
on each diagonal, including when the chart is empty. -/
def edgeHomotopy (h : PairBounded D) (i j : ι) :
    (ContinuousMap.const ↥(pairOverlap D i j) 1).Homotopy (ContractibleTransitionPaths.transitionMap D i j) := by
  classical
  by_cases hij : i = j
  · subst j
    exact (ContinuousMap.Homotopy.refl (ContinuousMap.const ↥(pairOverlap D i i) (1 : ProperFutureLorentz))).cast
      rfl (ContinuousMap.ext (fun x => (D.identity i x x.property.1).symm))
  · exact boundedJoint (ContractibleTransitionPaths.transitionMap D i j) (h i j hij).choose (h i j hij).choose_spec

/-- The constructed paths are normalized to the identity at every time on diagonal pairs. -/
theorem edgeHomotopy_diagonal (h : PairBounded D) (i : ι) (t : unitInterval) (x : pairOverlap D i i) :
    edgeHomotopy D h i i (t, x) = 1 := by
  classical
  simp only [edgeHomotopy]
  rfl

/-- Bounded transition images give a normalized jointly continuous family on the original atlas. -/
def family (h : PairBounded D) : Family D where
  homotopy i j := (edgeHomotopy D h i j).toContinuousMap
  source i j x := (edgeHomotopy D h i j).apply_zero x
  target i j x := (edgeHomotopy D h i j).apply_one x
  diagonal := edgeHomotopy_diagonal D h

/-- The path family retains the constructed joint homotopy on every actual pair domain. -/
theorem family_homotopy (h : PairBounded D) (i j : ι) :
    (family D h).homotopy i j = (edgeHomotopy D h i j).toContinuousMap := rfl

variable {T : Type*} [TopologicalSpace T] {proj : T → B}

/-- A principal atlas with bounded off-diagonal transition images presents the actual
projected space and its specified right action. -/
theorem hasPresentation (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (h : PairBounded (PrincipalAtlasCrossGauge.data A)) :
    PresentedLorentzBundle.HasPresentation proj A.right :=
  PresentedLorentzBundle.has_of_atlas A rfl (family (PrincipalAtlasCrossGauge.data A) h)

end FoliationQM.LorentzLocalPathFamily
