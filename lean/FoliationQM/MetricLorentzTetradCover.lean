module
public import FoliationQM.SmoothLorentzMetricGeometry
public import FoliationQM.SmoothLorentzTetrad
public import FoliationQM.GeometricLorentzNormalization

/-!
# Actual smooth Lorentz tetrads constructed from geometric metric data

Source scope: the geometric tetrad component of v13 `prop:takabayasi`.
The inputs are an actual smooth bilinear metric, pointwise Lorentz signature,
and independently specified orientation and future-cone regularity. No smooth
local tetrad or regularity of the pointwise chosen signature witness is input.

The chosen frame at an anchor supplies only an actual seed basis. The original
bundle trivialization extends it, and the verified signed algorithm normalizes
that extension on its computed open domain. Orientation and future conditions
restrict that domain. These genuine smooth sections are proved to be actual
geometric Lorentz frames and assembled into the original tetrad interface,
retaining exactly the original metric, orientation, future cone and bundle.
No global tetrad or unconditional geometric Spin structure is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set Module
open scoped Manifold Topology
namespace FoliationQM.MetricLorentzTetradCover
open SmoothLorentzMetricGeometry GeometricLorentzFrame

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  (D : SmoothLorentzMetricGeometry.Data (F := F) I V n)

/-- The actual tetrad sections are the explicit signed normalization of the original-trivialization extension of the chosen anchor basis. -/
def tetrad (anchor : B) : Fin 4 → ∀ y : B, V y :=
  SmoothLorentzGramSchmidt.normalized D.metric (seed D anchor)

/-- The metric-derived tetrad is a genuine smooth local frame on its computed geometric domain, by restriction of the independently constructed normalized extension. -/
theorem local_frame (anchor : B) :
    IsLocalFrameOn I F n (tetrad D anchor) (domain D anchor) :=
  (SmoothLorentzLocalFrame.isLocalFrameOn_anchor D.metric D.smooth_metric anchor
    (referenceFrame D anchor).basis (metric_symm D)).mono (domain_subset_anchorDomain D anchor)

/-- On its true geometric domain the normalized actual vectors define a geometric Lorentz frame; the pointwise signature witness is used only to recognize the original metric and future cone. -/
def frameAt (anchor y : B) (hy : y ∈ domain D anchor) :
    Frame (D.metric y).toLinearMap₁₂ (D.orientation y) (D.future y) := by
  let b := SmoothFrameExtension.basisAt (F := F) anchor (referenceFrame D anchor).basis y
    (domain_subset_chart D anchor hy)
  have hb : ⇑b = fun i => seed D anchor i y := by
    funext i
    exact (SmoothFrameExtension.frame_eq_basisAt (F := F) anchor
      (referenceFrame D anchor).basis y (domain_subset_chart D anchor hy) i).symm
  have hGood : LorentzGramSchmidt.Good (D.metric y).toLinearMap₁₂ b := by
    rw [hb]
    exact domain_good D anchor hy
  have hf : b 0 ∈ D.future y := by
    rw [congrFun hb 0]
    exact domain_future D anchor hy
  exact GeometricLorentzNormalization.normalizedFrame (referenceFrame D y) b hGood
    (domain_orientation D anchor hy) hf

/-- The constructed actual geometric frame has exactly the metric-derived smooth tetrad vectors, so no regularity of the independently chosen pointwise witnesses is used. -/
theorem frameAt_vectors (anchor y : B) (hy : y ∈ domain D anchor) (i : Fin 4) :
    (frameAt D anchor y hy).basis i = tetrad D anchor i y := by
  simp only [frameAt, GeometricLorentzNormalization.normalizedFrame_vectors]
  have hb : ⇑(SmoothFrameExtension.basisAt (F := F) anchor
      (referenceFrame D anchor).basis y (domain_subset_chart D anchor hy)) =
      fun j => seed D anchor j y := by
    funext j
    exact (SmoothFrameExtension.frame_eq_basisAt (F := F) anchor
      (referenceFrame D anchor).basis y (domain_subset_chart D anchor hy) j).symm
  rw [hb]
  rfl

/-- The geometric frame basis is precisely the basis of the actual smooth local tetrad, including its original order and vector values. -/
theorem frameAt_basis (anchor y : B) (hy : y ∈ domain D anchor) :
    (frameAt D anchor y hy).basis = (local_frame D anchor).toBasisAt hy := by
  apply DFunLike.ext
  intro i
  rw [IsLocalFrameOn.toBasisAt_coe]
  exact frameAt_vectors D anchor y hy i

/-- Each metric-derived tetrad returns the chosen independent geometric anchor basis exactly at its own anchor. -/
theorem tetrad_anchor (x : B) (i : Fin 4) :
    tetrad D x i x = (referenceFrame D x).basis i :=
  SmoothLorentzLocalFrame.normalized_anchor D.metric x (referenceFrame D x).basis
    (metric_basis (referenceFrame D x)) i

/-- The actual geometric frame constructed at its own anchor is exactly the independent signature witness chosen there. -/
theorem frameAt_anchor (x : B) : frameAt D x x (mem_domain D x) = referenceFrame D x := by
  apply frame_ext
  apply DFunLike.ext
  intro i
  rw [frameAt_vectors, tetrad_anchor]

/-- Smooth metric, pointwise signature, and independent orientation/future regularity construct genuine smooth Lorentz tetrad data on the actual computed cover, with no supplied tetrad. -/
def tetradData : SmoothLorentzTetrad.Data (F := F) I V B n where
  metric := D.metric
  smooth_metric := D.smooth_metric
  orientation := D.orientation
  future := D.future
  domain := domain D
  covers x := ⟨x, mem_domain D x⟩
  tetrad := tetrad D
  local_frame := local_frame D
  gram := by
    intro anchor y hy a b
    rw [← frameAt_vectors D anchor y hy a, ← frameAt_vectors D anchor y hy b]
    exact metric_basis (frameAt D anchor y hy) a b
  oriented := by
    intro anchor y hy
    rw [← frameAt_basis D anchor y hy]
    exact (frameAt D anchor y hy).oriented
  future_iff := by
    intro anchor y hy v
    rw [← frameAt_basis D anchor y hy]
    exact (frameAt D anchor y hy).future_iff v

/-- The constructed tetrad interface retains exactly the originally supplied actual bilinear metric. -/
theorem tetradData_metric : (tetradData D).metric = D.metric := rfl

/-- The constructed tetrad interface retains exactly the original independent fiber orientation. -/
theorem tetradData_orientation : (tetradData D).orientation = D.orientation := rfl

/-- The constructed tetrad interface retains exactly the original independent geometric future cone. -/
theorem tetradData_future : (tetradData D).future = D.future := rfl

/-- The tetrad cover is exactly the computed open geometric cover, without shrinking it implicitly or replacing the original base topology. -/
theorem tetradData_domain : (tetradData D).domain = domain D := rfl

/-- Every actual tetrad section in the constructed interface is the explicit metric-derived normalized section. -/
theorem tetradData_tetrad (anchor : B) (i : Fin 4) (y : B) :
    (tetradData D).tetrad anchor i y = tetrad D anchor i y := rfl

/-- The geometric frame recovered by the existing tetrad interface is exactly the independently constructed actual normalized frame on its true domain. -/
theorem tetradData_frameAt (anchor y : B) (hy : y ∈ domain D anchor) :
    SmoothLorentzTetrad.frameAt (tetradData D) anchor y hy = frameAt D anchor y hy := by
  apply frame_ext
  exact (frameAt_basis D anchor y hy).symm

/-- The complete actual local basis of the constructed tetrad data at its anchor is the originally chosen geometric anchor basis, not merely an isomorphic coordinate basis. -/
theorem tetradData_toBasisAt_anchor (x : B) :
    ((tetradData D).local_frame x).toBasisAt (mem_domain D x) = (referenceFrame D x).basis := by
  apply DFunLike.ext
  intro i
  rw [IsLocalFrameOn.toBasisAt_coe]
  exact tetrad_anchor D x i

end FoliationQM.MetricLorentzTetradCover
