module
public import FoliationQM.GeometricPrincipalSmoothAtlas
public import FoliationQM.PathTransitionData

/-!
# Coordinate changes between principal atlases of one geometric target

For the frame-bundle component of v13 `prop:takabayasi`, two actual
principal atlases on the same projection give cross-chart maps by
expressing an original unit section in the other atlas. Their regularity
follows from the original trivializations. When the atlases use the same
right action, these maps intertwine their coordinates and conjugate their
transition functions on the common domains.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.PrincipalAtlasCrossGauge

variable {B P G ι κ : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace G] [Group G] {proj : P → B}
  (A : GeometricPrincipalAtlas.Data (G := G) proj ι)
  (C : GeometricPrincipalAtlas.Data (G := G) proj κ)

/-- The actual transition data extracted from the principal trivializations. -/
def data : PathTransitionData.Data G B ι where
  domain i := ⟨(A.triv i).baseSet, (A.triv i).open_baseSet⟩
  covers := A.covers
  transition := A.transition
  continuous_transition := A.continuousOn_transition
  identity := A.transition_self
  comp := A.transition_comp

/-- The second atlas coordinate of the actual canonical section of the first atlas. -/
def cross (i : ι) (u : κ) (x : B) : G := (C.triv u (A.localSection i x)).2

/-- The cross-chart map is continuous on the intersection of its two chart domains. -/
theorem continuousOn_cross (i : ι) (u : κ) :
    ContinuousOn (cross A C i u) ((A.triv i).baseSet ∩ (C.triv u).baseSet) := by
  have hs : ContinuousOn (A.localSection i) ((A.triv i).baseSet ∩ (C.triv u).baseSet) :=
    (A.continuousOn_localSection i).mono inter_subset_left
  have ht := (C.triv u).toOpenPartialHomeomorph.continuousOn.comp hs (by
    intro x hx
    apply (C.triv u).mem_source.mpr
    rw [A.proj_localSection i x hx.1]
    exact hx.2)
  exact ht.snd

/-- Shared right translation makes the cross-chart map the left multiplier between
coordinates of every actual point lying over the common chart domain. -/
theorem coordinate (hr : A.right = C.right) (i : ι) (u : κ) (p : P)
    (hi : proj p ∈ (A.triv i).baseSet) (hu : proj p ∈ (C.triv u).baseSet) :
    (C.triv u p).2 = cross A C i u (proj p) * (A.triv i p).2 := by
  have hs : proj (A.localSection i (proj p)) ∈ (C.triv u).baseSet := by
    rw [A.proj_localSection i (proj p) hi]
    exact hu
  have he := C.right_local u (A.localSection i (proj p)) (A.triv i p).2 hs
  rw [← hr, A.localSection_right_coordinate i p hi] at he
  exact he

/-- The two orders of changing an actual section's coordinates commute on the four domains. -/
theorem transition_intertwine (hr : A.right = C.right) (i j : ι) (u v : κ) (x : B)
    (hi : x ∈ (A.triv i).baseSet) (hj : x ∈ (A.triv j).baseSet)
    (hu : x ∈ (C.triv u).baseSet) (hv : x ∈ (C.triv v).baseSet) :
    C.transition u v x * cross A C i u x = cross A C j v x * A.transition i j x := by
  have hp := A.proj_localSection i x hi
  have hC := C.change_coordinate u v (A.localSection i x) (hp.symm ▸ hu) (hp.symm ▸ hv)
  have hA := coordinate A C hr j v (A.localSection i x) (hp.symm ▸ hj) (hp.symm ▸ hv)
  rw [hp] at hC hA
  exact hC.symm.trans hA

/-- The second atlas transition is the first atlas transition conjugated by its two
cross-chart gauges in target-times-transition-times-inverse-source order. -/
theorem transition_conjugate (hr : A.right = C.right) (i j : ι) (u v : κ) (x : B)
    (hi : x ∈ (A.triv i).baseSet) (hj : x ∈ (A.triv j).baseSet)
    (hu : x ∈ (C.triv u).baseSet) (hv : x ∈ (C.triv v).baseSet) :
    C.transition u v x = cross A C j v x * A.transition i j x * (cross A C i u x)⁻¹ :=
  eq_mul_inv_of_mul_eq (transition_intertwine A C hr i j u v x hi hj hu hv)

section Smooth
variable {EB EG EP HB HG HP : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HB] [TopologicalSpace HG] [TopologicalSpace HP]
  [ChartedSpace HB B] [ChartedSpace HG G] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ EB HB} {J : ModelWithCorners ℝ EG HG}
  {K : ModelWithCorners ℝ EP HP} {n : WithTop ℕ∞}

/-- If both principal atlases are smooth in the original charted spaces, their
actual cross-chart maps have the same regularity on the common domains. -/
theorem contMDiffOn_cross (SA : GeometricPrincipalSmoothAtlas.Data I J K A n)
    (SC : GeometricPrincipalSmoothAtlas.Data I J K C n) (i : ι) (u : κ) :
    ContMDiffOn I J n (cross A C i u) ((A.triv i).baseSet ∩ (C.triv u).baseSet) := by
  have hs : ContMDiffOn I K n (A.localSection i) ((A.triv i).baseSet ∩ (C.triv u).baseSet) :=
    (SA.contMDiffOn_localSection i).mono inter_subset_left
  have ht := (SC.smooth_triv u).comp hs (by
    intro x hx
    apply (C.triv u).mem_source.mpr
    rw [A.proj_localSection i x hx.1]
    exact hx.2)
  intro x hx
  exact (ht x hx).snd

end Smooth
end FoliationQM.PrincipalAtlasCrossGauge
