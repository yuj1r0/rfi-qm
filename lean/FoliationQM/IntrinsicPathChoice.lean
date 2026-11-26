module
public import FoliationQM.IntrinsicPathCocycle

/-!
# Independence of intrinsic path-transition choices

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, two genuine normalized path families to the same
topological transitions differ by actual intrinsic kernel elements.
Jointly continuous loop families prove their local constancy. Generic
central-extension algebra identifies the resulting change of cocycles
as the native pair coboundary. No physical Spin comparison is used.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntrinsicPathChoice
open BasedPathGroup PathTransitionData IntrinsicPathCocycle

variable {G B ι : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace B] {D : Data G B ι}

/-- Two intrinsic representatives of the same transition differ by an actual endpoint-kernel element. -/
def kernelDifference (P Q : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) : (projection (G := G)).ker :=
  CentralExtensionDefect.difference projection (lift P i j x hi hj) (lift Q i j x hi hj)
    (by rw [projection_lift, projection_lift])

/-- The intrinsic difference is the actual new-to-old quotient-group ratio. -/
theorem kernelDifference_val (P Q : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (kernelDifference P Q i j x hi hj).val = lift Q i j x hi hj * (lift P i j x hi hj)⁻¹ := rfl

/-- Normalized diagonal path families have trivial diagonal difference. -/
theorem kernelDifference_diagonal (P Q : Family D) (i : ι) (x : B)
    (hi : x ∈ D.domain i) : kernelDifference P Q i i x hi hi = 1 := by
  apply Subtype.ext
  rw [kernelDifference_val, lift_diagonal, lift_diagonal, inv_one, one_mul]
  rfl

/-- The actual quotient of two transition paths is a jointly continuous
loop family on their original pair intersection. -/
def pairLoop (P Q : Family D) (i j : ι) : C(unitInterval × ↥(pairOverlap D i j), G) :=
  Q.homotopy i j * (P.homotopy i j)⁻¹

/-- Every actual difference loop starts at the unit. -/
theorem pairLoop_zero (P Q : Family D) (i j : ι) (x : pairOverlap D i j) :
    pairLoop P Q i j (0, x) = 1 := by
  change Q.homotopy i j (0, x) * (P.homotopy i j (0, x))⁻¹ = 1
  rw [Q.source, P.source, inv_one, one_mul]

/-- Equality of the actual transition endpoints closes every difference loop. -/
theorem pairLoop_one (P Q : Family D) (i j : ι) (x : pairOverlap D i j) :
    pairLoop P Q i j (1, x) = 1 := by
  change Q.homotopy i j (1, x) * (P.homotopy i j (1, x))⁻¹ = 1
  rw [Q.target, P.target, mul_inv_cancel]

/-- The difference-loop slice is exactly the actual intrinsic kernel ratio. -/
theorem kernelSlice_eq_difference (P Q : Family D) (i j : ι) (x : pairOverlap D i j) :
    kernelSlice (pairLoop P Q i j) (pairLoop_zero P Q i j) (pairLoop_one P Q i j) x =
      kernelDifference P Q i j x x.property.1 x.property.2 := by
  apply Subtype.ext
  change classOf (slice _ _ x) = _
  rw [kernelDifference_val]
  change classOf (slice _ _ x) = classOf (basedPath Q i j x x.property.1 x.property.2) *
    (classOf (basedPath P i j x x.property.1 x.property.2))⁻¹
  rw [← map_inv, ← map_mul]
  apply congrArg classOf
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rfl

/-- Actual path-choice differences are locally constant on each true open pair overlap. -/
theorem kernelDifference_locallyConstant [LocallyPathConnectedSpace B]
    (P Q : Family D) (i j : ι) :
    IsLocallyConstant (fun x : pairOverlap D i j =>
      kernelDifference P Q i j x x.property.1 x.property.2) := by
  have he := funext (kernelSlice_eq_difference P Q i j)
  exact (congrArg IsLocallyConstant he).mp
    (kernelSlice_locallyConstant_open (pairOverlap D i j)
      (pairLoop P Q i j) (pairLoop_zero P Q i j) (pairLoop_one P Q i j))

/-- Changing actual transition paths changes their intrinsic triple
defect by the actual kernel pair coboundary. -/
theorem defect_change (P Q : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    defect Q i j k x hi hj hk = kernelDifference P Q j k x hj hk *
      kernelDifference P Q i j x hi hj * defect P i j k x hi hj hk *
        (kernelDifference P Q i k x hi hk)⁻¹ :=
  CentralExtensionDefect.defect_change projection projection_central
    (lift P i j x hi hj) (lift P j k x hj hk) (lift P i k x hi hk)
    (lift Q i j x hi hj) (lift Q j k x hj hk) (lift Q i k x hi hk) _ _ _ _ _

variable (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))

/-- The normalized mod-two difference coefficient of two actual transition paths. -/
def pairCoefficient (P Q : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) : ZMod 2 :=
  Multiplicative.toAdd (e (kernelDifference P Q i j x hi hj))

/-- Extend the actual difference coefficient by zero outside its pair domain. -/
def pairValue (P Q : Family D) (i j : ι) (x : B) : ZMod 2 := by
  classical
  exact if h : x ∈ D.domain i ∧ x ∈ D.domain j then pairCoefficient e P Q i j x h.1 h.2 else 0

/-- The total pair representative retains its actual intrinsic coefficient on the overlap. -/
theorem pairValue_mem (P Q : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    pairValue e P Q i j x = pairCoefficient e P Q i j x hi hj := by
  classical
  exact dite_eq_left ⟨hi, hj⟩

/-- The actual path-choice ratio defines a normalized native locally constant pair cochain. -/
def difference [LocallyPathConnectedSpace B] (P Q : Family D) :
    ModTwoCohomology.OneCochain D.domain where
  value := pairValue e P Q
  local_value i j := by
    have he : (fun x : pairOverlap D i j => pairValue e P Q i j x) =
        (fun x : pairOverlap D i j => pairCoefficient e P Q i j x x.property.1 x.property.2) :=
      funext (fun x => pairValue_mem e P Q i j x x.property.1 x.property.2)
    exact (congrArg IsLocallyConstant he).mpr
      ((kernelDifference_locallyConstant P Q i j).comp (fun z => Multiplicative.toAdd (e z)))
  identity i x hi := by
    rw [pairValue_mem e P Q i i x hi hi, pairCoefficient, kernelDifference_diagonal, map_one]
    rfl

/-- The native pair cochain retains the actual path-choice ratio at every true overlap. -/
theorem difference_value [LocallyPathConnectedSpace B] (P Q : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (difference e P Q).value i j x = pairCoefficient e P Q i j x hi hj :=
  pairValue_mem e P Q i j x hi hj

/-- The independent mod-two cocycles change by the exact additive pair coboundary. -/
theorem coefficient_change (P Q : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    coefficient e Q i j k x hi hj hk =
      (pairCoefficient e P Q j k x hj hk + pairCoefficient e P Q i j x hi hj -
        pairCoefficient e P Q i k x hi hk) + coefficient e P i j k x hi hj hk := by
  have h := congrArg (fun z => Multiplicative.toAdd (e z)) (defect_change P Q i j k x hi hj hk)
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv] at h
  change Multiplicative.toAdd (e (defect Q i j k x hi hj hk)) = _
  rw [h]
  simp only [coefficient, pairCoefficient, sub_eq_add_neg]
  abel

/-- The constructed pair cochain witnesses the genuine native coboundary relation. -/
theorem cocycle_related [LocallyPathConnectedSpace B] (P Q : Family D) :
    ModTwoCohomology.Related (cocycle e P) (cocycle e Q) := by
  refine ⟨difference e P Q, fun i j k x hi hj hk => ?_⟩
  rw [cocycle_value e Q i j k x hi hj hk, cocycle_value e P i j k x hi hj hk]
  unfold ModTwoCohomology.boundary
  rw [difference_value e P Q j k x hj hk, difference_value e P Q i j x hi hj,
    difference_value e P Q i k x hi hk]
  exact coefficient_change e P Q i j k x hi hj hk

/-- The native fixed-cover class is independent of all supplied
normalized jointly continuous transition-path choices. -/
theorem class_independent [LocallyPathConnectedSpace B] (P Q : Family D) :
    ModTwoCohomology.classOf (cocycle e P) = ModTwoCohomology.classOf (cocycle e Q) :=
  (ModTwoCohomology.classOf_eq_iff _ _).mpr (cocycle_related e P Q)

end FoliationQM.IntrinsicPathChoice
