module
public import FoliationQM.SpinLiftIsomorphism

/-!
# Extracting chart signs from a physical isomorphism of adapted lifts

For the global Spin-frame component of v13 `prop:takabayasi`, an
equivariant diffeomorphism over the original Lorentz bundle sends a
source unit section to a point with the same Lorentz image. Its target
Spin coordinate is consequently a kernel sign. The resulting smooth
chart coefficients give the actual gauge relation of the transitions.
-/

@[expose] public section
noncomputable section
open Set
open scoped Manifold
namespace FoliationQM.AdaptedSpinGaugeExtraction
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth LorentzMatrixGroup
open CliffordSpinSignKernel SpinLiftIsomorphism

variable {E H B P ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] {frameProj : P → B} {n : WithTop ℕ∞}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι}
  (A T : GeometricSpinStructure.Lift I L n) (e : Between A T)

/-- The target coordinate of the image of the source chart's actual canonical unit section. -/
def raw (i : ι) (x : B) : Spin := (T.atlas.triv i (e.diffeo (A.atlas.localSection i x))).2

/-- The coordinate of the mapped unit section projects to the Lorentz identity on the chart. -/
theorem raw_projection (i : ι) (x : B) (hx : x ∈ (L.triv i).baseSet) :
    lorentzHom (raw A T e i x) = 1 := by
  have ha : x ∈ (A.atlas.triv i).baseSet := by rwa [A.adapted.domain_eq]
  have ht : T.proj (e.diffeo (A.atlas.localSection i x)) ∈ (T.atlas.triv i).baseSet := by
    rw [base_eq e, A.atlas.proj_localSection i x ha, T.adapted.domain_eq]
    exact hx
  rw [raw, ← T.adapted.coordinate i _ ht, e.over, A.adapted.unit i x hx,
    L.localSection_coordinate i x hx]

/-- On the chart the coordinate of the mapped unit section varies smoothly with its base point. -/
theorem smooth_raw (i : ι) : ContMDiffOn I spinModel n (raw A T e i) (L.triv i).baseSet := by
  have hs := A.smoothAtlas.contMDiffOn_localSection i
  rw [A.adapted.domain_eq] at hs
  have he := e.diffeo.contMDiff.comp_contMDiffOn hs
  have ht := (T.smoothAtlas.smooth_triv i).comp he (by
    intro x hx
    apply (T.atlas.triv i).mem_source.mpr
    have ha : x ∈ (A.atlas.triv i).baseSet := by rwa [A.adapted.domain_eq]
    change T.proj (e.diffeo (A.atlas.localSection i x)) ∈ (T.atlas.triv i).baseSet
    rw [base_eq e, A.atlas.proj_localSection i x ha, T.adapted.domain_eq]
    exact hx)
  intro x hx
  exact (ht x hx).snd

/-- The actual target coordinate of any image point is its chart sign times its source Spin coordinate. -/
theorem raw_coordinate (i : ι) (q : A.Carrier) (hq : A.proj q ∈ (L.triv i).baseSet) :
    (T.atlas.triv i (e.diffeo q)).2 = raw A T e i (A.proj q) * (A.atlas.triv i q).2 := by
  have ha : A.proj q ∈ (A.atlas.triv i).baseSet := by rwa [A.adapted.domain_eq]
  have ht : T.proj (e.diffeo (A.atlas.localSection i (A.proj q))) ∈ (T.atlas.triv i).baseSet := by
    rw [base_eq e, A.atlas.proj_localSection i _ ha, T.adapted.domain_eq]
    exact hq
  have he := e.equivariant (A.atlas.localSection i (A.proj q)) (A.atlas.triv i q).2
  rw [A.atlas.localSection_right_coordinate i q ha] at he
  exact (congrArg (fun y => (T.atlas.triv i y).2) he).trans (T.atlas.right_local i _ _ ht)

/-- Evaluating at the unit section uniquely determines any proposed local coefficient of the isomorphism. -/
theorem raw_unique (i : ι) (b : B → Spin)
    (h : ∀ q : A.Carrier, A.proj q ∈ (L.triv i).baseSet →
      (T.atlas.triv i (e.diffeo q)).2 = b (A.proj q) * (A.atlas.triv i q).2)
    (x : B) (hx : x ∈ (L.triv i).baseSet) : b x = raw A T e i x := by
  have ha : x ∈ (A.atlas.triv i).baseSet := by rwa [A.adapted.domain_eq]
  have he := h (A.atlas.localSection i x) (by rwa [A.atlas.proj_localSection i x ha])
  rw [A.atlas.proj_localSection i x ha, A.atlas.localSection_coordinate i x ha, mul_one] at he
  exact he.symm

/-- In intersecting charts the two local coefficients intertwine the genuine Spin transitions in their physical order. -/
theorem raw_transition (i j : ι) (x : B) (hi : x ∈ (L.triv i).baseSet)
    (hj : x ∈ (L.triv j).baseSet) :
    T.atlas.transition i j x * raw A T e i x = raw A T e j x * A.atlas.transition i j x := by
  have ha : x ∈ (A.atlas.triv i).baseSet := by rwa [A.adapted.domain_eq]
  have hx := A.atlas.proj_localSection i x ha
  have ht := (base_eq e (A.atlas.localSection i x)).trans hx
  have h₁ := T.atlas.change_coordinate i j (e.diffeo (A.atlas.localSection i x))
    (by rw [ht, T.adapted.domain_eq]; exact hi) (by rw [ht, T.adapted.domain_eq]; exact hj)
  have h₂ := raw_coordinate A T e j (A.atlas.localSection i x) (by rwa [hx])
  rw [ht] at h₁
  rw [hx] at h₂
  exact h₁.symm.trans h₂

/-- Take the physical kernel sign on its chart and fill the coefficient by the kernel unit elsewhere. -/
def chartSign (i : ι) (x : B) : Kernel := by
  classical
  exact if hx : x ∈ (L.triv i).baseSet then ⟨raw A T e i x, raw_projection A T e i x hx⟩ else 1

/-- At an actual chart point the kernel sign has the underlying Spin value read from the mapped section. -/
theorem chartSign_val (i : ι) (x : B) (hx : x ∈ (L.triv i).baseSet) :
    (chartSign A T e i x).val = raw A T e i x := by
  classical
  simp only [chartSign, dite_eq_left hx]

variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}

/-- The unit-section coordinates of a physical isomorphism form a smooth chartwise Clifford sign cochain. -/
def chartGauge (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
    (A T : GeometricSpinStructure.Lift I L n) (e : Between A T) :
    SpinSignHOne.ZeroCochain I (AdaptedGeometricSpinLift.lorentzData LM).domain n where
  value := chartSign A T e
  smooth_value i := (smooth_raw A T e i).congr (fun x hx => chartSign_val A T e i x hx)

/-- A physical Spin-principal isomorphism over the Lorentz total space induces chartwise gauge equivalence of the two extracted genuine lifts. -/
theorem gauge_of_between (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
    (A T : GeometricSpinStructure.Lift I L n) (e : Between A T) :
    SpinLiftChartGauge.GaugeEq (transitions LM A) (transitions LM T) := by
  refine ⟨chartGauge LM A T e, ?_⟩
  intro i j x hi hj
  change T.atlas.transition i j x =
    ((chartSign A T e j x).val * (chartSign A T e i x).val⁻¹) * A.atlas.transition i j x
  have hc := kernel_mul_comm (chartSign A T e i x)⁻¹ (A.atlas.transition i j x)
  change (chartSign A T e i x).val⁻¹ * _ = _ * (chartSign A T e i x).val⁻¹ at hc
  rw [chartSign_val A T e i x hi] at hc
  rw [chartSign_val A T e j x hj, chartSign_val A T e i x hi]
  calc
    T.atlas.transition i j x = (T.atlas.transition i j x * raw A T e i x) * (raw A T e i x)⁻¹ :=
      (mul_inv_cancel_right _ _).symm
    _ = _ := by rw [raw_transition A T e i j x hi hj, mul_assoc, ← hc, ← mul_assoc]

end FoliationQM.AdaptedSpinGaugeExtraction
