module
public import FoliationQM.PathTransitionData
public import FoliationQM.BasedPathLocalConstancy
public import FoliationQM.BasedPathCentrality
public import FoliationQM.CentralExtensionDefect
public import FoliationQM.ModTwoCohomology

/-!
# The independent intrinsic path-transition cocycle

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, actual group transition paths define triple defects
in the intrinsic path-class endpoint kernel. Centrality proves the
degree-two equation. Actual closed-loop families and local path
connectivity prove local constancy. Applying a specified kernel
coefficient homomorphism gives the native mod-two cocycle.
No physical Spin object, physical defect, or comparison theorem enters
this construction or its proofs.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntrinsicPathCocycle
open BasedPathGroup PathTransitionData

variable {G B ι : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace B] {D : Data G B ι}

/-- The independently constructed endpoint extension has the centrality
required by the generic defect algebra. -/
theorem projection_central : CentralExtensionDefect.Central (projection (G := G)) :=
  fun z a => (BasedPathCentrality.kernel_central z a).eq

/-- The ordered triple defect of the intrinsic transition-path classes. -/
def defect (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    (projection (G := G)).ker :=
  CentralExtensionDefect.defect projection (lift P i j x hi hj) (lift P j k x hj hk)
    (lift P i k x hi hk) (by rw [projection_lift, projection_lift, projection_lift]; exact D.comp i j k x hi hj hk)

/-- The intrinsic defect is the actual ordered quotient-group ratio. -/
theorem defect_val (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    (defect P i j k x hi hj hk).val =
      lift P j k x hj hk * lift P i j x hi hj * (lift P i k x hi hk)⁻¹ := rfl

/-- A repeated first chart gives the unit intrinsic defect. -/
theorem defect_self_left (P : Family D) (i k : ι) (x : B)
    (hi : x ∈ D.domain i) (hk : x ∈ D.domain k) : defect P i i k x hi hi hk = 1 := by
  apply Subtype.ext
  rw [defect_val, lift_diagonal, mul_one, mul_inv_cancel]
  rfl

/-- A repeated second chart gives the unit intrinsic defect. -/
theorem defect_self_right (P : Family D) (i k : ι) (x : B)
    (hi : x ∈ D.domain i) (hk : x ∈ D.domain k) : defect P i k k x hi hk hk = 1 := by
  apply Subtype.ext
  rw [defect_val, lift_diagonal, one_mul, mul_inv_cancel]
  rfl

/-- The actual intrinsic kernel defects obey the degree-two equation,
as a consequence of centrality and the original transition composition. -/
theorem defect_quadruple (P : Family D) (i j k l : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k)
    (hl : x ∈ D.domain l) :
    defect P j k l x hj hk hl * defect P i j l x hi hj hl =
      defect P i j k x hi hj hk * defect P i k l x hi hk hl :=
  CentralExtensionDefect.quadruple projection projection_central
    (lift P i j x hi hj) (lift P j k x hj hk) (lift P i k x hi hk)
    (lift P j l x hj hl) (lift P k l x hk hl) (lift P i l x hi hl) _ _ _ _

/-- An actual jointly continuous closed-loop family on a true triple overlap,
formed by pointwise multiplication of the supplied transition paths. -/
def loopFamily (P : Family D) (i j k : ι) : C(unitInterval × ↥(tripleOverlap D i j k), G) where
  toFun z := P.homotopy j k (z.1, ⟨z.2, z.2.property.1.2, z.2.property.2⟩) *
    P.homotopy i j (z.1, ⟨z.2, z.2.property.1.1, z.2.property.1.2⟩) *
    (P.homotopy i k (z.1, ⟨z.2, z.2.property.1.1, z.2.property.2⟩))⁻¹
  continuous_toFun := by fun_prop

/-- Every actual triple loop starts at the identity. -/
theorem loopFamily_zero (P : Family D) (i j k : ι) (x : tripleOverlap D i j k) :
    loopFamily P i j k (0, x) = 1 := by
  change P.homotopy j k _ * P.homotopy i j _ * (P.homotopy i k _)⁻¹ = 1
  rw [P.source, P.source, P.source, inv_one, one_mul, one_mul]

/-- The original transition cocycle closes every actual triple loop. -/
theorem loopFamily_one (P : Family D) (i j k : ι) (x : tripleOverlap D i j k) :
    loopFamily P i j k (1, x) = 1 := by
  change P.homotopy j k _ * P.homotopy i j _ * (P.homotopy i k _)⁻¹ = 1
  rw [P.target, P.target, P.target, D.comp i j k x x.property.1.1 x.property.1.2 x.property.2,
    mul_inv_cancel]

/-- The actual triple-loop slice represents precisely the intrinsic kernel defect. -/
theorem kernelSlice_eq_defect (P : Family D) (i j k : ι) (x : tripleOverlap D i j k) :
    kernelSlice (loopFamily P i j k) (loopFamily_zero P i j k) (loopFamily_one P i j k) x =
      defect P i j k x x.property.1.1 x.property.1.2 x.property.2 := by
  apply Subtype.ext
  change classOf (slice _ _ x) = _
  rw [defect_val]
  change classOf (slice _ _ x) =
    classOf (basedPath P j k x x.property.1.2 x.property.2) *
    classOf (basedPath P i j x x.property.1.1 x.property.1.2) *
    (classOf (basedPath P i k x x.property.1.1 x.property.2))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg classOf
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rfl

/-- On a locally path connected base the intrinsic triple defects are
locally constant on their actual open intersection. -/
theorem defect_locallyConstant [LocallyPathConnectedSpace B] (P : Family D) (i j k : ι) :
    IsLocallyConstant (fun x : tripleOverlap D i j k =>
      defect P i j k x x.property.1.1 x.property.1.2 x.property.2) := by
  have he := funext (kernelSlice_eq_defect P i j k)
  exact (congrArg IsLocallyConstant he).mp
    (kernelSlice_locallyConstant_open (tripleOverlap D i j k)
      (loopFamily P i j k) (loopFamily_zero P i j k) (loopFamily_one P i j k))

variable (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))

/-- The mod-two coefficient is the supplied intrinsic-kernel character
evaluated on the actual triple path defect. -/
def coefficient (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) : ZMod 2 :=
  Multiplicative.toAdd (e (defect P i j k x hi hj hk))

/-- Extend the actual triple coefficient by zero away from its domain. -/
def value (P : Family D) (i j k : ι) (x : B) : ZMod 2 := by
  classical
  exact if h : (x ∈ D.domain i ∧ x ∈ D.domain j) ∧ x ∈ D.domain k then
    coefficient e P i j k x h.1.1 h.1.2 h.2 else 0

/-- On a true triple overlap the total value is exactly its intrinsic path coefficient. -/
theorem value_mem (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    value e P i j k x = coefficient e P i j k x hi hj hk := by
  classical
  exact dite_eq_left ⟨⟨hi, hj⟩, hk⟩

/-- Kernel-character coefficients inherit the genuine quadruple equation. -/
theorem coefficient_quadruple (P : Family D) (i j k l : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k)
    (hl : x ∈ D.domain l) :
    coefficient e P j k l x hj hk hl + coefficient e P i j l x hi hj hl =
      coefficient e P i j k x hi hj hk + coefficient e P i k l x hi hk hl := by
  have h := congrArg (fun z => Multiplicative.toAdd (e z))
    (defect_quadruple P i j k l x hi hj hk hl)
  simpa only [map_mul, toAdd_mul, coefficient] using h

/-- The independent intrinsic path values form a normalized locally
constant native mod-two cocycle on the original cover. -/
def cocycle [LocallyPathConnectedSpace B] (P : Family D) :
    ModTwoCohomology.TwoCocycle D.domain where
  value := value e P
  local_value i j k := by
    have he : (fun x : tripleOverlap D i j k => value e P i j k x) =
        (fun x : tripleOverlap D i j k => coefficient e P i j k x
          x.property.1.1 x.property.1.2 x.property.2) :=
      funext (fun x => value_mem e P i j k x x.property.1.1 x.property.1.2 x.property.2)
    exact (congrArg IsLocallyConstant he).mpr
      ((defect_locallyConstant P i j k).comp (fun z => Multiplicative.toAdd (e z)))
  self_left i k x hi hk := by
    rw [value_mem e P i i k x hi hi hk, coefficient, defect_self_left, map_one]
    rfl
  self_right i k x hi hk := by
    rw [value_mem e P i k k x hi hk hk, coefficient, defect_self_right, map_one]
    rfl
  quadruple i j k l x hi hj hk hl := by
    rw [value_mem e P j k l x hj hk hl, value_mem e P i j l x hi hj hl,
      value_mem e P i j k x hi hj hk, value_mem e P i k l x hi hk hl]
    exact coefficient_quadruple e P i j k l x hi hj hk hl

/-- The constructed native cocycle retains the exact intrinsic path
coefficient at every true triple intersection. -/
theorem cocycle_value [LocallyPathConnectedSpace B] (P : Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    (cocycle e P).value i j k x = coefficient e P i j k x hi hj hk :=
  value_mem e P i j k x hi hj hk

end FoliationQM.IntrinsicPathCocycle
