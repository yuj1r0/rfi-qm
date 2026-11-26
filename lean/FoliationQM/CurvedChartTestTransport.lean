module

public import FoliationQM.CurvedGradientCovariance
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Compact test fields under smooth chart changes

A test supported inside one chart pulls across the inverse chart transition
and extends by zero. Its support lies in the compact image of the original
support inside the new chart, so the extension is locally zero at boundary
points. Reversing the transition recovers the original global test.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedChartTestTransport

open RealLorentzFrame Set
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F]
variable {n : WithTop ℕ∞} {η : Covector → F}

/-- Transport a test by the inverse coordinate map, extending by zero outside its target. -/
def transport (e : OpenPartialHomeomorph Covector Covector) (η : Covector → F) : Covector → F :=
  e.target.indicator (η ∘ e.symm)

/-- On the target the zero extension is the original test composed with the inverse transition. -/
theorem transport_apply (e : OpenPartialHomeomorph Covector Covector) (η : Covector → F)
    {y : Covector} (hy : y ∈ e.target) : transport e η y = η (e.symm y) :=
  indicator_of_mem hy _

/-- Pulling the transported test back agrees with the original at every source point. -/
theorem transport_apply_image (e : OpenPartialHomeomorph Covector Covector) (η : Covector → F)
    {x : Covector} (hx : x ∈ e.source) : transport e η (e x) = η x := by
  rw [transport_apply e η (e.map_source hx), e.left_inv hx]

/-- The topological support of the zero extension is contained in the compact image of the original support. -/
theorem transport_tsupport_image_subset (e : OpenPartialHomeomorph Covector Covector)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ e.source) : tsupport (transport e η) ⊆ e '' tsupport η := by
  apply closure_minimal _ (hc.image_of_continuousOn (e.continuousOn.mono hs)).isClosed
  intro y hy
  by_cases ht : y ∈ e.target
  · refine ⟨e.symm y, subset_closure ?_, e.right_inv ht⟩
    change η (e.symm y) ≠ 0
    simpa only [Function.mem_support, transport_apply e η ht] using hy
  · exact (hy (indicator_of_notMem ht _)).elim

/-- The transported closed support stays inside the target, including at chart boundary points. -/
theorem transport_tsupport_subset (e : OpenPartialHomeomorph Covector Covector)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ e.source) : tsupport (transport e η) ⊆ e.target := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := transport_tsupport_image_subset e hc hs hy
  exact e.map_source (hs hx)

/-- Compact support survives zero extension across the target boundary. -/
theorem transport_compact (e : OpenPartialHomeomorph Covector Covector)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ e.source) : HasCompactSupport (transport e η) :=
  (hc.image_of_continuousOn (e.continuousOn.mono hs)).of_isClosed_subset (isClosed_tsupport _)
    (transport_tsupport_image_subset e hc hs)

/-- Local regularity of the inverse chart at order n gives global Cⁿ regularity of the extended test. -/
theorem transport_contDiff [NormedSpace ℝ F] (e : OpenPartialHomeomorph Covector Covector)
    (heInv : ∀ y ∈ e.target, ContDiffAt ℝ n e.symm y) (hη : ContDiff ℝ n η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ e.source) : ContDiff ℝ n (transport e η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ e.target
  · apply (hη.contDiffAt.comp y (heInv y hy)).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact transport_apply e η hz
  · exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp fun h => hy (transport_tsupport_subset e hc hs h))

/-- Reversing the chart transition recovers the entire source test, with its exterior zero values. -/
theorem transport_symm_transport (e : OpenPartialHomeomorph Covector Covector)
    (hs : tsupport η ⊆ e.source) : transport e.symm (transport e η) = η := by
  funext x
  by_cases hx : x ∈ e.source
  · rw [transport_apply e.symm _ hx, e.symm_symm, transport_apply_image e η hx]
  · exact (indicator_of_notMem hx _).trans (image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))).symm

/-- Fields with prescribed differentiability and compact closed support inside the supplied chart domain. -/
abbrev Test (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (n : WithTop ℕ∞) (U : Set Covector) :=
  {η : Covector → F // ContDiff ℝ n η ∧ HasCompactSupport η ∧ tsupport η ⊆ U}

/-- Forward and inverse transitions give inverse bijections of the compact interior test spaces. -/
def testEquiv [NormedSpace ℝ F] (e : OpenPartialHomeomorph Covector Covector)
    (he : ∀ x ∈ e.source, ContDiffAt ℝ n e x) (heInv : ∀ y ∈ e.target, ContDiffAt ℝ n e.symm y) :
    Test F n e.source ≃ Test F n e.target where
  toFun η := ⟨transport e η, transport_contDiff e heInv η.2.1 η.2.2.1 η.2.2.2,
    transport_compact e η.2.2.1 η.2.2.2, transport_tsupport_subset e η.2.2.1 η.2.2.2⟩
  invFun ξ := ⟨transport e.symm ξ, transport_contDiff e.symm he ξ.2.1 ξ.2.2.1 ξ.2.2.2,
    transport_compact e.symm ξ.2.2.1 ξ.2.2.2, transport_tsupport_subset e.symm ξ.2.2.1 ξ.2.2.2⟩
  left_inv η := Subtype.ext (transport_symm_transport e η.2.2.2)
  right_inv ξ := Subtype.ext (transport_symm_transport e.symm ξ.2.2.2)

end FoliationQM.CurvedChartTestTransport
