module
public import FoliationQM.ContractibleTransitionPaths
public import FoliationQM.IntrinsicPathGauge

/-!
# Native gauge invariance from standard chart contractibility

For the geometric component of v13 `prop:takabayasi`, standard
contractibility of nonempty charts constructs actual joint gauge paths.
Contractibility of nonempty pair overlaps includes the diagonal charts,
so it constructs both transition and gauge paths. The independent native
Cech obstruction is therefore invariant under every continuous chart
gauge on this specified cover. Locally path connectedness of the base
remains explicit; cofinal good covers and arbitrary atlas comparison
are not concluded.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ContractiblePathGauge
open PathTransitionData BasedPathGroup IntrinsicPathGauge ContractibleTransitionPaths

variable {G B ι : Type*} [TopologicalSpace G] [Group G] [TopologicalSpace B]
  {D : Data G B ι}

/-- Standard contractibility on precisely the nonempty original charts. -/
def ChartContractible (D : Data G B ι) : Prop :=
  ∀ i, Nonempty ↥(D.domain i) → ContractibleSpace ↥(D.domain i)

/-- Diagonal pair overlaps supply the required chart contractibility. -/
theorem charts_of_pairs (h : PairContractible D) : ChartContractible D :=
  chart_contractible D h

/-- The original continuous gauge as a continuous map on its chart. -/
def gaugeMap (A : Gauge D) (i : ι) : C(↥(D.domain i), G) :=
  ⟨fun x => A.value i x,
    (A.continuous_value i).comp_continuous continuous_subtype_val (fun x => x.property)⟩

/-- Restricting a gauge to its true chart preserves its actual value. -/
theorem gaugeMap_apply (A : Gauge D) (i : ι) (x : D.domain i) :
    gaugeMap A i x = A.value i x := rfl

variable [PathConnectedSpace G]

/-- Contractible nonempty charts construct actual identity-to-gauge homotopies;
on empty charts the constant map satisfies the endpoints vacuously. -/
def joint (A : Gauge D) (h : ChartContractible D) (i : ι) :
    (ContinuousMap.const ↥(D.domain i) 1).Homotopy (gaugeMap A i) := by
  classical
  by_cases hn : Nonempty ↥(D.domain i)
  · letI : ContractibleSpace ↥(D.domain i) := h i hn
    exact fromOne (gaugeMap A i)
  · exact
      { toFun := fun _ => 1
        continuous_toFun := continuous_const
        map_zero_left := fun _ => rfl
        map_one_left := fun x => (hn ⟨x⟩).elim }

/-- The constructed gauge homotopy starts at the group identity. -/
theorem joint_zero (A : Gauge D) (h : ChartContractible D) (i : ι)
    (x : D.domain i) : joint A h i (0, x) = 1 := (joint A h i).apply_zero x

/-- The constructed gauge homotopy ends at the original gauge value. -/
theorem joint_one (A : Gauge D) (h : ChartContractible D) (i : ι)
    (x : D.domain i) : joint A h i (1, x) = A.value i x := (joint A h i).apply_one x

/-- Actual chart topology constructs the joint gauge paths, with no supplied lift or nullhomotopy. -/
def paths (A : Gauge D) (h : ChartContractible D) : GaugePaths A where
  homotopy i := (joint A h i).toContinuousMap
  source := joint_zero A h
  target := joint_one A h

variable [IsTopologicalGroup G]

omit [PathConnectedSpace G] in
/-- Gauge changes preserve the same actual pair domains and their standard contractibility. -/
theorem pairs_gauged (A : Gauge D) (h : PairContractible D) :
    PairContractible (gaugedData A) := h

variable [LocallyPathConnectedSpace B]

/-- On contractible nonempty charts, arbitrary continuous gauges preserve
the fixed-cover class for any normalized families on the two transitions. -/
theorem class_any_gauge (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) (A : Gauge D) (h : ChartContractible D) (Q : Family (gaugedData A)) :
    ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e Q) =
      ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e P) :=
  class_any_gauged e P (paths A h) Q

/-- On contractible nonempty charts, arbitrary continuous gauges preserve
the native all-cover class for any normalized transition-path choices. -/
theorem obstruction_any_gauge (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (P : Family D) (A : Gauge D) (h : ChartContractible D) (Q : Family (gaugedData A)) :
    GlobalIntrinsicPathObstruction.obstruction e Q =
      GlobalIntrinsicPathObstruction.obstruction e P :=
  obstruction_any_gauged e P (paths A h) Q

/-- Pair contractibility constructs both families and proves the native
fixed-cover class invariant under every actual continuous chart gauge. -/
theorem constructed_class_gauge
    (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (A : Gauge D) (h : PairContractible D) :
    ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e
      (family (gaugedData A) (pairs_gauged A h))) =
      ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle e (family D h)) :=
  class_any_gauge e (family D h) A (charts_of_pairs h) _

/-- Pair contractibility constructs both families and proves the native
all-cover class invariant under every actual continuous chart gauge. -/
theorem constructed_obstruction_gauge
    (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))
    (A : Gauge D) (h : PairContractible D) :
    GlobalIntrinsicPathObstruction.obstruction e
      (family (gaugedData A) (pairs_gauged A h)) =
      GlobalIntrinsicPathObstruction.obstruction e (family D h) :=
  obstruction_any_gauge e (family D h) A (charts_of_pairs h) _

end FoliationQM.ContractiblePathGauge
