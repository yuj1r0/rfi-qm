module
public import FoliationQM.SmoothLorentzLocalFrame
public import FoliationQM.GeometricLorentzNormalization

/-!
# Independent Lorentz metric geometry and actual compatible open domains

Source scope: the geometric tetrad component of v13 `prop:takabayasi`.
The inputs are an original smooth vector bundle, a smooth bilinear metric,
pointwise Lorentz-signature witnesses, an orientation whose equality loci in
original bundle coordinates are open, and an open actual future-cone total
subset. No smoothness of a pointwise choice of signature witness is required.

Each chosen anchor basis has an original smooth local extension. Its computed
normalization domain is intersected with the actual orientation and future
loci. The resulting open domains contain their anchors and hence cover the
base. The local normalized tetrad and geometric Spin construction are derived
downstream; neither is a field of the input record.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set Module
open scoped Manifold Topology
namespace FoliationQM.SmoothLorentzMetricGeometry

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Independent smooth metric, pointwise signature and continuous orientation/future geometry on the original vector bundle, without any smooth tetrad input. -/
structure Data (n : WithTop ℕ∞) [ContMDiffVectorBundle n F V I] where
  /-- The actual continuous bilinear form in each original fiber. -/
  metric : ∀ x : B, V x →L[ℝ] V x →L[ℝ] ℝ
  /-- Smoothness of the actual metric graph in the original iterated Hom bundle. -/
  smooth_metric : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun x => (⟨x, metric x⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
      (fun x : B => V x →L[ℝ] V x →L[ℝ] ℝ)))
  /-- The specified exterior-form orientation of each fiber. -/
  orientation : ∀ x : B, Orientation ℝ (V x) (Fin 4)
  /-- The specified future timelike cone in each fiber. -/
  future : ∀ x : B, Set (V x)
  /-- A pointwise algebraic Lorentz-signature and cone witness, with no regularity or local-section condition. -/
  signature : ∀ x : B, Nonempty
    (GeometricLorentzFrame.Frame (metric x).toLinearMap₁₂ (orientation x) (future x))
  /-- Independent continuity of the orientation in every original anchor trivialization and fixed model basis. -/
  orientation_open : ∀ (x : B) (b : Basis (Fin 4) ℝ F),
    IsOpen {y : B | ∃ hy : y ∈ (trivializationAt F V x).baseSet,
      ((trivializationAt F V x).basisAt b hy).orientation = orientation y}
  /-- Independent openness of the actual future-cone subset of the original vector-bundle total space. -/
  future_open : IsOpen {p : TotalSpace F V | p.2 ∈ future p.1}

variable {I V} {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  (D : Data (F := F) I V n)

/-- An algebraically chosen frame in each fiber; no smoothness of this choice is asserted or used. -/
def referenceFrame (x : B) :
    GeometricLorentzFrame.Frame (D.metric x).toLinearMap₁₂ (D.orientation x) (D.future x) :=
  Classical.choice (D.signature x)

/-- Symmetry of the actual metric follows from its pointwise Lorentz-signature witness. -/
theorem metric_symm (x : B) : LinearMap.BilinForm.IsSymm (D.metric x).toLinearMap₁₂ :=
  GeometricLorentzFrameRecognition.metric_symm (referenceFrame D x)

/-- The actual smooth seed sections extend only the chosen anchor basis through its original bundle chart. -/
def seed (x : B) : Fin 4 → ∀ y : B, V y :=
  SmoothFrameExtension.frame (F := F) x (referenceFrame D x).basis

/-- The true open locus where the original extended seed basis has the specified orientation. -/
def orientationLocus (x : B) : TopologicalSpace.Opens B :=
  ⟨{y : B | ∃ hy : y ∈ (trivializationAt F V x).baseSet,
      ((trivializationAt F V x).basisAt
        (SmoothFrameExtension.modelBasis (F := F) x (referenceFrame D x).basis) hy).orientation =
          D.orientation y},
    D.orientation_open x (SmoothFrameExtension.modelBasis (F := F) x (referenceFrame D x).basis)⟩

/-- The genuine open future locus uses the seed graph only within its original open chart, without global continuity of its zero extension. -/
def futureLocus (x : B) : TopologicalSpace.Opens B :=
  ⟨(SmoothFrameExtension.domain (F := F) (V := V) x : Set B) ∩
      {y : B | seed D x 0 y ∈ D.future y},
    (SmoothFrameExtension.contMDiffOn_frame (I := I) (n := n) x
      (referenceFrame D x).basis 0).continuousOn.isOpen_inter_preimage
        (SmoothFrameExtension.domain (F := F) (V := V) x).isOpen D.future_open⟩

/-- The actual open domain for metric normalization compatible with both independently specified orientation and future cone. -/
def domain (x : B) : TopologicalSpace.Opens B :=
  SmoothLorentzLocalFrame.anchorDomain D.metric D.smooth_metric x (referenceFrame D x).basis ⊓
    (orientationLocus D x ⊓ futureLocus D x)

/-- Each anchor lies in its computed compatible domain, by its actual eta basis, orientation and future zeroth vector. -/
theorem mem_domain (x : B) : x ∈ domain D x := by
  refine ⟨SmoothLorentzLocalFrame.mem_anchorDomain D.metric D.smooth_metric x
    (referenceFrame D x).basis (GeometricLorentzFrame.metric_basis (referenceFrame D x)), ?_, ?_⟩
  · refine ⟨SmoothFrameExtension.mem_domain (F := F) x, ?_⟩
    change (SmoothFrameExtension.basisAt (F := F) x (referenceFrame D x).basis x
      (SmoothFrameExtension.mem_domain (F := F) x)).orientation = D.orientation x
    rw [SmoothFrameExtension.basisAt_anchor]
    exact (referenceFrame D x).oriented
  · refine ⟨SmoothFrameExtension.mem_domain (F := F) x, ?_⟩
    change SmoothFrameExtension.frame (F := F) x (referenceFrame D x).basis 0 x ∈ D.future x
    rw [SmoothFrameExtension.frame_at]
    exact GeometricLorentzNormalization.basis_zero_mem_future (referenceFrame D x)

/-- The constructed compatible open domains cover the original base, indexed by their anchors. -/
theorem covers (y : B) : ∃ x : B, y ∈ domain D x := ⟨y, mem_domain D y⟩

/-- The compatible domain is contained in the exact computed normalization domain of its original seed extension. -/
theorem domain_subset_anchorDomain (x : B) : (domain D x : Set B) ⊆
    SmoothLorentzLocalFrame.anchorDomain D.metric D.smooth_metric x (referenceFrame D x).basis :=
  fun _ hy => hy.1

/-- Every compatible-domain point lies in the original anchor bundle chart. -/
theorem domain_subset_chart (x : B) : (domain D x : Set B) ⊆
    SmoothFrameExtension.domain (F := F) (V := V) x := fun _ hy => hy.1.1

/-- All four actual signed pivots of the original seed are positive on the constructed compatible domain. -/
theorem domain_good (x : B) {y : B} (hy : y ∈ domain D x) :
    LorentzGramSchmidt.Good (D.metric y).toLinearMap₁₂ (fun i => seed D x i y) := hy.1.2

/-- The original extended seed basis has exactly the supplied geometric orientation on the compatible domain. -/
theorem domain_orientation (x : B) {y : B} (hy : y ∈ domain D x) :
    (SmoothFrameExtension.basisAt (F := F) x (referenceFrame D x).basis y
      (domain_subset_chart D x hy)).orientation = D.orientation y := by
  obtain ⟨hy', ho⟩ := hy.2.1
  exact ho

/-- The zeroth original seed vector belongs to the specified actual future cone throughout the compatible domain. -/
theorem domain_future (x : B) {y : B} (hy : y ∈ domain D x) :
    seed D x 0 y ∈ D.future y := hy.2.2.2

end FoliationQM.SmoothLorentzMetricGeometry
