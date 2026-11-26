module
public import FoliationQM.GlobalIntrinsicPathObstruction

/-!
# Gauge invariance of the independent path obstruction

For the geometric component of v13 `prop:takabayasi`, actual continuous
chart gauges and joint paths from the identity change the transition data.
The intrinsic triple defect is conjugated by a path class, and intrinsic
kernel centrality proves its equality with the original defect. This gives
fixed-cover and all-cover invariance without a physical Spin comparison.
Joint gauge paths are explicit here; constructing them from contractible
charts is a separate theorem.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntrinsicPathGauge
open PathTransitionData BasedPathGroup

variable {G B ι : Type*} [TopologicalSpace G] [Group G]
  [TopologicalSpace B] {D : Data G B ι}

/-- Actual continuous gauge maps on the original chart domains. -/
structure Gauge (D : Data G B ι) where
  /-- Total representatives of the chart maps. -/
  value : ι → B → G
  /-- Continuity is required on the actual domain. -/
  continuous_value : ∀ i, ContinuousOn (value i) (D.domain i)

/-- Jointly continuous paths from the identity to actual chart gauges. -/
structure GaugePaths (A : Gauge D) where
  /-- The actual time and chart dependent maps. -/
  homotopy : ∀ i, C(unitInterval × ↥(D.domain i), G)
  /-- Every gauge path starts at the identity. -/
  source : ∀ i (x : D.domain i), homotopy i (0, x) = 1
  /-- Every gauge path ends at the specified gauge value. -/
  target : ∀ i (x : D.domain i), homotopy i (1, x) = A.value i x

variable [IsTopologicalGroup G]

/-- The original cover with transitions transformed by the actual gauges. -/
def gaugedData (A : Gauge D) : Data G B ι where
  domain := D.domain
  covers := D.covers
  transition i j x := A.value j x * D.transition i j x * (A.value i x)⁻¹
  continuous_transition i j :=
    (((A.continuous_value j).mono Set.inter_subset_right).mul
      (D.continuous_transition i j)).mul
      (((A.continuous_value i).mono Set.inter_subset_left).inv)
  identity i x hi := by rw [D.identity i x hi, mul_one, mul_inv_cancel]
  comp i j k x hi hj hk := by
    calc
      _ = A.value k x * (D.transition j k x * D.transition i j x) *
          (A.value i x)⁻¹ := by group
      _ = _ := by rw [D.comp i j k x hi hj hk]

/-- Gauge transformation preserves the precise original cover. -/
theorem gaugedData_domain (A : Gauge D) : (gaugedData A).domain = D.domain := rfl

/-- The transformed transition is the usual ordered chart-gauge formula. -/
theorem gaugedData_transition (A : Gauge D) (i j : ι) (x : B) :
    (gaugedData A).transition i j x = A.value j x * D.transition i j x *
      (A.value i x)⁻¹ := rfl

/-- Actual gauge paths transform the joint transition paths on true pairs. -/
def gaugedFamily (P : Family D) {A : Gauge D} (H : GaugePaths A) :
    Family (gaugedData A) where
  homotopy i j := (show C(unitInterval × ↥(pairOverlap D i j), G) from
    ⟨fun z => H.homotopy j (z.1, ⟨z.2, z.2.property.2⟩) *
      P.homotopy i j z * (H.homotopy i (z.1, ⟨z.2, z.2.property.1⟩))⁻¹,
      by fun_prop⟩)
  source i j x := by
    change ↥(pairOverlap D i j) at x
    change H.homotopy j (0, ⟨x, x.property.2⟩) * P.homotopy i j (0, x) *
      (H.homotopy i (0, ⟨x, x.property.1⟩))⁻¹ = 1
    rw [H.source, P.source, H.source, inv_one, one_mul, one_mul]
  target i j x := by
    change ↥(pairOverlap D i j) at x
    change H.homotopy j (1, ⟨x, x.property.2⟩) * P.homotopy i j (1, x) *
      (H.homotopy i (1, ⟨x, x.property.1⟩))⁻¹ =
        A.value j x * D.transition i j x * (A.value i x)⁻¹
    rw [H.target, P.target, H.target]
  diagonal i t x := by
    change ↥(pairOverlap D i i) at x
    change H.homotopy i (t, ⟨x, x.property.1⟩) * P.homotopy i i (t, x) *
      (H.homotopy i (t, ⟨x, x.property.1⟩))⁻¹ = 1
    rw [P.diagonal, mul_one, mul_inv_cancel]

/-- The gauge path at an actual chart point is an intrinsic based path. -/
def gaugeBasedPath {A : Gauge D} (H : GaugePaths A) (i : ι) (x : B)
    (hi : x ∈ D.domain i) : BasedPath G :=
  ⟨(H.homotopy i).comp
    ((ContinuousMap.id unitInterval).prodMk (.const unitInterval ⟨x, hi⟩)),
    H.source i ⟨x, hi⟩⟩

/-- The gauge representative retains its actual joint path values. -/
theorem gaugeBasedPath_apply {A : Gauge D} (H : GaugePaths A) (i : ι) (x : B)
    (hi : x ∈ D.domain i) (t : unitInterval) :
    (gaugeBasedPath H i x hi).val t = H.homotopy i (t, ⟨x, hi⟩) := rfl

/-- The intrinsic gauge class is defined by the actual gauge path. -/
def gaugeLift {A : Gauge D} (H : GaugePaths A) (i : ι) (x : B)
    (hi : x ∈ D.domain i) : PathCover G := classOf (gaugeBasedPath H i x hi)

/-- The intrinsic gauge class projects to the original chart gauge. -/
theorem projection_gaugeLift {A : Gauge D} (H : GaugePaths A) (i : ι) (x : B)
    (hi : x ∈ D.domain i) : projection (gaugeLift H i x hi) = A.value i x :=
  H.target i ⟨x, hi⟩

/-- The transformed intrinsic lift obeys the actual chart-gauge group formula. -/
theorem lift_gauged (P : Family D) {A : Gauge D} (H : GaugePaths A)
    (i j : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    lift (gaugedFamily P H) i j x hi hj =
      gaugeLift H j x hj * lift P i j x hi hj * (gaugeLift H i x hi)⁻¹ := by
  change classOf (basedPath (gaugedFamily P H) i j x hi hj) =
    classOf (gaugeBasedPath H j x hj) * classOf (basedPath P i j x hi hj) *
      (classOf (gaugeBasedPath H i x hi))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg classOf
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rfl

/-- Intrinsic kernel centrality makes the actual triple defect gauge invariant. -/
theorem defect_gauged (P : Family D) {A : Gauge D} (H : GaugePaths A)
    (i j k : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j)
    (hk : x ∈ D.domain k) :
    IntrinsicPathCocycle.defect (gaugedFamily P H) i j k x hi hj hk =
      IntrinsicPathCocycle.defect P i j k x hi hj hk := by
  apply Subtype.ext
  change lift (gaugedFamily P H) j k x hj hk * lift (gaugedFamily P H) i j x hi hj *
    (lift (gaugedFamily P H) i k x hi hk)⁻¹ = _
  rw [lift_gauged, lift_gauged, lift_gauged]
  calc
    _ = gaugeLift H k x hk * (IntrinsicPathCocycle.defect P i j k x hi hj hk).val *
        (gaugeLift H k x hk)⁻¹ := by
      rw [IntrinsicPathCocycle.defect_val]
      group
    _ = _ := by
      rw [← (BasedPathCentrality.kernel_central
        (IntrinsicPathCocycle.defect P i j k x hi hj hk) (gaugeLift H k x hk)).eq,
        mul_assoc, mul_inv_cancel, mul_one]

/-- Every intrinsic kernel character gives identical true-overlap coefficients after gauge change. -/
theorem coefficient_gauged (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) {A : Gauge D} (H : GaugePaths A)
    (i j k : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j)
    (hk : x ∈ D.domain k) :
    IntrinsicPathCocycle.coefficient e (gaugedFamily P H) i j k x hi hj hk =
      IntrinsicPathCocycle.coefficient e P i j k x hi hj hk := by
  unfold IntrinsicPathCocycle.coefficient
  rw [defect_gauged]

variable [LocallyPathConnectedSpace B]

/-- The independently constructed fixed-cover class is unchanged by the joint gauge paths. -/
theorem class_gauged (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) {A : Gauge D} (H : GaugePaths A) :
    ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e (gaugedFamily P H)) =
      ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e P) := by
  apply ModTwoCohomology.classOf_eq_of_eqOn
  intro i j k x hi hj hk
  rw [IntrinsicPathCocycle.cocycle_value e (gaugedFamily P H) i j k x hi hj hk,
    IntrinsicPathCocycle.cocycle_value e P i j k x hi hj hk]
  exact coefficient_gauged e P H i j k x hi hj hk

/-- Gauge change preserves the independently constructed all-cover class. -/
theorem obstruction_gauged (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) {A : Gauge D} (H : GaugePaths A) :
    GlobalIntrinsicPathObstruction.obstruction e (gaugedFamily P H) =
      GlobalIntrinsicPathObstruction.obstruction e P :=
  congrArg (ModTwoAllCover.ofCover D.domain D.covers) (class_gauged e P H)

/-- Any normalized joint paths for the gauged transitions have the same native fixed-cover class. -/
theorem class_any_gauged (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) {A : Gauge D} (H : GaugePaths A) (Q : Family (gaugedData A)) :
    ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e Q) =
      ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e P) :=
  (IntrinsicPathChoice.class_independent e Q (gaugedFamily P H)).trans (class_gauged e P H)

/-- Any normalized joint paths for the gauged transitions have the same native all-cover class. -/
theorem obstruction_any_gauged (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) {A : Gauge D} (H : GaugePaths A) (Q : Family (gaugedData A)) :
    GlobalIntrinsicPathObstruction.obstruction e Q =
      GlobalIntrinsicPathObstruction.obstruction e P :=
  (GlobalIntrinsicPathObstruction.independent e Q (gaugedFamily P H)).trans
    (obstruction_gauged e P H)

end FoliationQM.IntrinsicPathGauge
