module
public import FoliationQM.GeometricLorentzFrame
public import FoliationQM.CliffordSpinLorentzTransitions
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Lorentz transitions derived from smooth geometric tetrads

The supplied objects are an actual real vector bundle, a continuous bilinear
metric whose Hom-bundle graph is smooth, and actual local tetrad sections.
The tetrads form bases only on their specified open chart domains. Their Gram,
orientation, and future-cone conditions produce geometric Lorentz frames there.

Transition functions are derived from these actual frames, with the group
identity as an arbitrary off-overlap extension. Their intrinsic Lorentz
smoothness is proved using signed metric pairings and smooth bundle evaluation;
no transition smoothness or geometric Spin lift is assumed. The result is
literal Lorentz cocycle data on exactly the supplied open cover. No total
frame-bundle topology or arbitrary tetrad existence is concluded here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Bundle Matrix
open scoped Manifold Bundle Topology Matrix.Norms.Operator
namespace FoliationQM.SmoothLorentzTetrad
open GeometricLorentzFrame LorentzMatrixGroup RealLorentzFrame

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Smooth metric and actual local tetrads on a real vector bundle; all basis and geometric conditions are confined to the specified chart domains. -/
structure Data (ι : Type*) (n : WithTop ℕ∞) [ContMDiffVectorBundle n F V I] where
  /-- The supplied actual fiberwise continuous bilinear metric. -/
  metric : ∀ x : B, V x →L[ℝ] V x →L[ℝ] ℝ
  /-- The metric graph is smooth in the genuine iterated Hom bundle atlas. -/
  smooth_metric : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun x => (⟨x, metric x⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
      (fun x : B => V x →L[ℝ] V x →L[ℝ] ℝ)))
  /-- The specified exterior-form orientation in each actual fiber. -/
  orientation : ∀ x : B, Orientation ℝ (V x) (Fin 4)
  /-- The specified geometric future cone in each actual fiber. -/
  future : ∀ x : B, Set (V x)
  /-- The actual open domains on which the supplied tetrads are frames. -/
  domain : ι → TopologicalSpace.Opens B
  /-- The local tetrad domains cover the base. -/
  covers : ∀ x : B, ∃ i, x ∈ domain i
  /-- The four actual vector-bundle sections for each chart, with no off-domain regularity assumption. -/
  tetrad : ι → Fin 4 → ∀ x : B, V x
  /-- The actual sections are smooth and form a basis on the specified chart. -/
  local_frame : ∀ i, IsLocalFrameOn I F n (tetrad i) (domain i)
  /-- The actual tetrad metric pairings have Gram matrix (+---) on their chart. -/
  gram : ∀ i x, x ∈ domain i → ∀ a b : Fin 4,
    metric x (tetrad i a x) (tetrad i b x) = eta a b
  /-- Each actual local tetrad has the supplied fiber orientation. -/
  oriented : ∀ i x (hx : x ∈ domain i),
    ((local_frame i).toBasisAt hx).orientation = orientation x
  /-- Each local tetrad identifies the supplied future cone with the actual model future timelike cone. -/
  future_iff : ∀ i x (hx : x ∈ domain i) (v : Covector),
    ((local_frame i).toBasisAt hx).equivFun.symm v ∈ future x ↔ futureCone v

variable {I V} {ι : Type*} {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  (D : Data (F := F) I V ι n)

/-- The genuine geometric frame is derived from the actual local sections where they form a basis. -/
def frameAt (i : ι) (x : B) (hx : x ∈ D.domain i) :
    Frame (D.metric x).toLinearMap₁₂ (D.orientation x) (D.future x) where
  basis := (D.local_frame i).toBasisAt hx
  metric := by
    ext a b
    simp only [LinearMap.BilinForm.toMatrix_apply, IsLocalFrameOn.toBasisAt_coe,
      ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
    exact D.gram i x hx a b
  oriented := D.oriented i x hx
  future_iff := D.future_iff i x hx

/-- The vectors in the derived geometric frame are exactly the originally supplied tetrad sections. -/
theorem frameAt_basis (i : ι) (x : B) (hx : x ∈ D.domain i) (a : Fin 4) :
    (frameAt D i x hx).basis a = D.tetrad i a x :=
  (D.local_frame i).toBasisAt_coe hx a

/-- The actual Lorentz transition is geometric change of frame on the pair overlap, extended by the identity elsewhere. -/
def transition (i j : ι) (x : B) : ProperFutureLorentz := by
  classical
  exact if hx : x ∈ D.domain i ∧ x ∈ D.domain j then
    GeometricLorentzFrame.change (frameAt D i x hx.1) (frameAt D j x hx.2)
  else 1

/-- On its true overlap the transition is exactly the independently defined geometric change of frame. -/
theorem transition_eq_change (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    transition D i j x = GeometricLorentzFrame.change (frameAt D i x hi) (frameAt D j x hj) := by
  simp [transition, hi, hj]

/-- The off-overlap extension is literally the group identity; no off-overlap smoothness is claimed. -/
theorem transition_eq_one_of_not_mem (i j : ι) (x : B)
    (hx : ¬ (x ∈ D.domain i ∧ x ∈ D.domain j)) : transition D i j x = 1 := by
  simp [transition, hx]

/-- Every actual transition entry is a signed metric pairing of the two supplied local tetrad sections on the true overlap. -/
theorem transition_matrix_entry (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (a b : Fin 4) :
    matrix (transition D i j x).val a b =
      sign a * D.metric x (D.tetrad j a x) (D.tetrad i b x) := by
  rw [transition_eq_change D i j x hi hj, change_matrix_entry, frameAt_basis, frameAt_basis]
  rfl

/-- The derived transition sends the actual coordinates of the first tetrad to those of the second. -/
theorem transition_coordinates (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (v : Covector) :
    matrix (transition D i j x).val *ᵥ v =
      (frameAt D j x hj).basis.equivFun ((frameAt D i x hi).basis.equivFun.symm v) := by
  rw [transition_eq_change D i j x hi hj, change_matrix]
  exact change_coordinates _ _ _

/-- Geometric self-transitions are the identity on the actual chart domain. -/
theorem transition_self (i : ι) (x : B) (hx : x ∈ D.domain i) :
    transition D i i x = 1 := by
  rw [transition_eq_change D i i x hx hx, change_self]

/-- The derived geometric transitions obey the genuine chart i to j to k cocycle order on triple overlaps. -/
theorem transition_comp (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    transition D j k x * transition D i j x = transition D i k x := by
  rw [transition_eq_change D j k x hj hk, transition_eq_change D i j x hi hj,
    transition_eq_change D i k x hi hk, change_comp]

/-- Reversing the actual geometric chart transition takes its group inverse on the pair overlap. -/
theorem transition_reverse (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    transition D j i x = (transition D i j x)⁻¹ := by
  rw [transition_eq_change D j i x hj hi, transition_eq_change D i j x hi hj, change_reverse]

/-- Pairing two actual local tetrad sections with the smooth Hom-bundle metric gives a smooth scalar on their actual overlap. -/
theorem contMDiffOn_metric_pairing (i j : ι) (a b : Fin 4) :
    ContMDiffOn I 𝓘(ℝ, ℝ) n
      (fun x => D.metric x (D.tetrad j a x) (D.tetrad i b x))
      ((D.domain i : Set B) ∩ (D.domain j : Set B)) := by
  have hj := ((D.local_frame j).contMDiffOn a).mono
    (show (D.domain i : Set B) ∩ (D.domain j : Set B) ⊆ D.domain j from inter_subset_right)
  have hi := ((D.local_frame i).contMDiffOn b).mono
    (show (D.domain i : Set B) ∩ (D.domain j : Set B) ⊆ D.domain i from inter_subset_left)
  have hp : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) n
      (fun x => (⟨x, D.metric x (D.tetrad j a x) (D.tetrad i b x)⟩ :
        TotalSpace ℝ (Bundle.Trivial B ℝ)))
      ((D.domain i : Set B) ∩ (D.domain j : Set B)) :=
    D.smooth_metric.contMDiffOn.clm_bundle_apply₂ hj hi
  intro x hx
  simpa using (Bundle.contMDiffWithinAt_totalSpace.mp (hp x hx)).2

/-- Actual geometric transition entries are smooth on their overlap, derived from the metric and tetrad graph regularity. -/
theorem contMDiffOn_transition_entry (i j : ι) (a b : Fin 4) :
    ContMDiffOn I 𝓘(ℝ, ℝ) n (fun x => matrix (transition D i j x).val a b)
      ((D.domain i : Set B) ∩ (D.domain j : Set B)) := by
  have hc : ContDiff ℝ n (fun t : ℝ => sign a * t) := by fun_prop
  apply (hc.contMDiff.comp_contMDiffOn (contMDiffOn_metric_pairing D i j a b)).congr
  intro x hx
  exact transition_matrix_entry D i j x hx.1 hx.2 a b

private def matrixOfEntries : ((Fin 4 × Fin 4) → ℝ) →L[ℝ] Mat4 :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v a b => v (a, b)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The actual real matrix-valued transition is smooth for the existing ambient matrix topology. -/
theorem contMDiffOn_transition_matrix (i j : ι) :
    ContMDiffOn I 𝓘(ℝ, Mat4) n (fun x => matrix (transition D i j x).val)
      ((D.domain i : Set B) ∩ (D.domain j : Set B)) := by
  have he : ContMDiffOn I 𝓘(ℝ, (Fin 4 × Fin 4) → ℝ) n
      (fun (x : B) (ab : Fin 4 × Fin 4) => matrix (transition D i j x).val ab.1 ab.2)
      ((D.domain i : Set B) ∩ (D.domain j : Set B)) := by
    apply contMDiffOn_pi_module_iff.mpr
    intro ab
    exact contMDiffOn_transition_entry D i j ab.1 ab.2
  exact matrixOfEntries.contDiff.contMDiff.comp_contMDiffOn he

/-- Actual geometric transitions are intrinsically smooth into the independent Lorentz manifold, proved from their signed metric entries. -/
theorem contMDiffOn_transition (i j : ι) :
    ContMDiffOn I LorentzManifold.model n (transition D i j)
      ((D.domain i : Set B) ∩ (D.domain j : Set B)) :=
  LorentzManifold.contMDiffOn_iff_value.mpr (contMDiffOn_transition_matrix D i j)

/-- Actual metric and tetrad data produce literal smooth Lorentz cocycle data on the original cover, with no supplied transition-smoothness premise. -/
def lorentzData : CliffordSpinLorentzTransitions.Data I B ι n where
  domain := D.domain
  covers := D.covers
  transition := transition D
  smooth_transition := contMDiffOn_transition D
  identity := transition_self D
  comp := transition_comp D

/-- The derived Lorentz cocycle retains exactly the supplied geometric chart domains. -/
theorem lorentzData_domain : (lorentzData D).domain = D.domain := rfl

/-- The derived Lorentz cocycle uses exactly the proved geometric transitions. -/
theorem lorentzData_transition (i j : ι) (x : B) :
    (lorentzData D).transition i j x = transition D i j x := rfl

end FoliationQM.SmoothLorentzTetrad
