module
public import FoliationQM.GeometricSpinLift
public import FoliationQM.GeometricPrincipalSmoothAtlas
public import FoliationQM.CliffordSpinCocycleCorrection

/-!
# Extracting actual Spin cocycles from adapted geometric lifts

Source scope: the geometric Spin-structure bridge in v13 `prop:takabayasi`.
The source and target principal total spaces, topologies, projections and
smooth atlases are independent. Adaptation means only that their chart
base domains agree and the actual geometric map sends canonical source
unit sections to target unit sections. Equivariance then proves the
physical local coordinate formula and projection of their genuine
geometrically extracted transitions. No cocycle or transition projection
conclusion is supplied as an adaptation field. Smoothness of the map itself
is derived from those actual adapted charts and the smooth Clifford map.

This extracts a same-cover Spin cocycle from an already supplied adapted
geometric lift; it neither constructs arbitrary lifts nor assumes that an
arbitrary existing lift is adapted to a previously specified cover.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology
open scoped Manifold
namespace FoliationQM.AdaptedGeometricSpinLift
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth LorentzMatrixGroup

section Geometry
variable {B Q P : Type*} [TopologicalSpace B] [TopologicalSpace Q] [TopologicalSpace P]
  {spinProj : Q → B} {frameProj : P → B} {ι : Type*}
  {S : GeometricPrincipalAtlas.Data (G := Spin) spinProj ι}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι}

/-- Genuine same-cover adaptation: only identical actual chart domains and compatibility of the original canonical unit sections. -/
structure Adapted (F : GeometricSpinLift.Map S L) : Prop where
  /-- The source and target principal charts use exactly the same original base domains. -/
  domain_eq : ∀ i, (S.triv i).baseSet = (L.triv i).baseSet
  /-- The actual geometric lift maps each canonical source unit section to the corresponding original target unit section. -/
  unit : ∀ i x, x ∈ (L.triv i).baseSet → F (S.localSection i x) = L.localSection i x

namespace Adapted
variable {F : GeometricSpinLift.Map S L} (A : Adapted F)
include A

/-- In genuinely adapted principal charts, equivariance forces exactly the original physical Clifford homomorphism on the actual group coordinate. -/
theorem coordinate (i : ι) (q : Q) (hq : spinProj q ∈ (S.triv i).baseSet) :
    (L.triv i (F q)).2 = lorentzHom (S.triv i q).2 := by
  have ht : spinProj q ∈ (L.triv i).baseSet := by rw [← A.domain_eq i]; exact hq
  have he := F.equivariant (S.localSection i (spinProj q)) (S.triv i q).2
  rw [S.localSection_right_coordinate i q hq, A.unit i (spinProj q) ht] at he
  rw [he, L.right_local i _ _ (by rw [L.proj_localSection i (spinProj q) ht]; exact ht),
    L.localSection_coordinate i (spinProj q) ht, one_mul]

/-- The full actual adapted local map preserves the base and applies precisely the physical Clifford Lorentz homomorphism in its group coordinate. -/
theorem local_formula (i : ι) (q : Q) (hq : spinProj q ∈ (S.triv i).baseSet) :
    L.triv i (F q) = (spinProj q, lorentzHom (S.triv i q).2) := by
  apply Prod.ext
  · exact ((L.triv i).coe_fst' (by rw [F.proj, ← A.domain_eq i]; exact hq)).trans (F.proj q)
  · exact A.coordinate i q hq

/-- The actual adapted geometric map is reconstructed by the original target inverse chart and the physical Clifford image of the source coordinate. -/
theorem map_eq_symm (i : ι) (q : Q) (hq : spinProj q ∈ (S.triv i).baseSet) :
    F q = (L.triv i).toOpenPartialHomeomorph.symm
      (spinProj q, lorentzHom (S.triv i q).2) := by
  rw [← A.local_formula i q hq]
  exact ((L.triv i).left_inv ((L.triv i).mem_source.mpr
    (by rw [F.proj, ← A.domain_eq i]; exact hq))).symm

/-- The actual geometric Spin transitions project to the actual Lorentz transitions on each genuine overlap, derived solely from adapted unit sections and equivariance. -/
theorem transition_projection (i j : ι) (x : B)
    (hi : x ∈ (L.triv i).baseSet) (hj : x ∈ (L.triv j).baseSet) :
    lorentzHom (S.transition i j x) = L.transition i j x := by
  have hsi : x ∈ (S.triv i).baseSet := by rw [A.domain_eq i]; exact hi
  have hsj : x ∈ (S.triv j).baseSet := by rw [A.domain_eq j]; exact hj
  have h := A.coordinate j (S.localSection i x)
    (by rw [S.proj_localSection i x hsi]; exact hsj)
  rw [A.unit i x hi] at h
  exact h.symm

end Adapted
end Geometry

section Smooth
variable {E EQ EP H HQ HP B Q P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace H] [TopologicalSpace HQ] [TopologicalSpace HP]
  {I : ModelWithCorners ℝ E H} {KQ : ModelWithCorners ℝ EQ HQ}
  {KP : ModelWithCorners ℝ EP HP}
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace Q] [ChartedSpace HQ Q]
  [TopologicalSpace P] [ChartedSpace HP P]
  {spinProj : Q → B} {frameProj : P → B} {ι : Type*} {n : WithTop ℕ∞}
  {S : GeometricPrincipalAtlas.Data (G := Spin) spinProj ι}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι}

/-- An independently smooth geometric Spin principal atlas yields actual Clifford Spin cocycle data through its genuine chart sections and transitions. -/
def spinData (SM : GeometricPrincipalSmoothAtlas.Data I spinModel KQ S n) :
    CliffordSpinPolarCocycle.Data I B ι n where
  domain i := ⟨(S.triv i).baseSet, (S.triv i).open_baseSet⟩
  covers := S.covers
  transition := S.transition
  smooth_transition := SM.contMDiffOn_transition
  identity := S.transition_self
  comp := S.transition_comp

/-- An independently smooth geometric Lorentz principal atlas yields actual Lorentz cocycle data on its original chart domains. -/
def lorentzData (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n) :
    CliffordSpinLorentzTransitions.Data I B ι n where
  domain i := ⟨(L.triv i).baseSet, (L.triv i).open_baseSet⟩
  covers := L.covers
  transition := L.transition
  smooth_transition := LM.contMDiffOn_transition
  identity := L.transition_self
  comp := L.transition_comp

namespace Adapted
variable {F : GeometricSpinLift.Map S L} (A : Adapted F)
  (SM : GeometricPrincipalSmoothAtlas.Data I spinModel KQ S n)
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
include A SM LM

/-- Smoothness of an adapted geometric Spin map is derived from the original independent smooth charts and the physical Clifford local formula, without a smooth-map premise. -/
theorem contMDiff : ContMDiff KQ KP n F := by
  intro q
  obtain ⟨i, hi⟩ := S.covers (spinProj q)
  have ht : spinProj q ∈ (L.triv i).baseSet := by rw [← A.domain_eq i]; exact hi
  have hs := SM.contMDiffAt_triv i q hi
  have hb := SM.contMDiff_proj.contMDiffAt (x := q)
  have hr := (contMDiff_lorentzHom n).contMDiffAt.comp q hs.snd
  have h := (LM.contMDiffAt_symm i (spinProj q, lorentzHom (S.triv i q).2) ht).comp q
    (hb.prodMk hr)
  apply h.congr_of_eventuallyEq
  filter_upwards [S.continuous_proj.continuousAt.preimage_mem_nhds
    ((S.triv i).open_baseSet.mem_nhds hi)] with r hri
  exact A.map_eq_symm i r hri

/-- Extracted smooth Spin and Lorentz cocycles have identical actual chart domains when the original geometric lift is adapted. -/
theorem extracted_domain_eq : (spinData SM).domain = (lorentzData LM).domain := by
  funext i
  exact TopologicalSpace.Opens.ext (A.domain_eq i)

/-- Every supplied adapted geometric Spin lift yields a genuine same-cover smooth Clifford Spin cocycle lift of the independently extracted Lorentz data. -/
theorem hasSpinCocycleLift : CliffordSpinCocycleCorrection.HasSpinCocycleLift (lorentzData LM) :=
  ⟨spinData SM, A.extracted_domain_eq SM LM, A.transition_projection⟩

end Adapted
end Smooth
end FoliationQM.AdaptedGeometricSpinLift
