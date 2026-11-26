module

public import FoliationQM.LaboratoryTimeDerivatives
public import FoliationQM.PolarRegularity

/-!
# Actual physical-time pullback of normal-coordinate fields

Source: v13 `cor:schrodinger`, component kinds C and D.
The input Covector here has coordinate x⁰=t,
in seconds. The linear map `toNormal c` sends it to the established normal
coordinates (ct,x,y,z). All directional derivatives are actual real Fréchet
derivatives. Local C² regularity supplies the neighborhood identities needed
before differentiating a first derivative again.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LaboratoryCoordinates

open LorentzCoordinates OsmoticSliceFields PolarSecondDifferential PolarRegularity
open Madelung (coordinateVector)
open scoped Topology

/-- The genuine constant linear map from physical coordinates (t,x) to normal coordinates (ct,x). -/
def toNormal (c : ℝ) : Covector →L[ℝ] Covector :=
  ContinuousLinearMap.pi fun i =>
    (if i = 0 then c else 1) • (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ)

/-- Only coordinate zero is scaled by the normal-coordinate map. -/
theorem toNormal_apply (c : ℝ) (x : Covector) (i : Fin 4) :
    toNormal c x i = (if i = 0 then c else 1) * x i := by
  by_cases hi : i = 0 <;> simp [toNormal, hi]

/-- The actual normal image of a fixed-position physical-time slice is the ct slice. -/
theorem toNormal_slicePoint (c t : ℝ) (y : Spatial) :
    toNormal c (slicePoint t y) = slicePoint (c * t) y := by
  ext i
  fin_cases i <;> simp [toNormal_apply, slicePoint, assemble]

/-- The unit physical-time direction maps to c times the unit normal direction. -/
theorem toNormal_time (c : ℝ) :
    toNormal c (coordinateVector 0) = c • coordinateVector 0 := by
  ext i
  fin_cases i <;> simp [toNormal_apply, coordinateVector]

/-- Each actual spatial coordinate direction is unchanged by physical-time conversion. -/
theorem toNormal_spatial (c : ℝ) (i : Fin 3) :
    toNormal c (coordinateVector i.succ) = coordinateVector i.succ := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [toNormal_apply, coordinateVector, Pi.single_apply]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The same spacetime field evaluated at physical time through the actual ct map. -/
def pullback (c : ℝ) (ψ : Covector → F) (x : Covector) : F := ψ (toNormal c x)

/-- Local regularity of the original field gives local regularity of its actual laboratory pullback. -/
theorem contDiffAt_pullback {c : ℝ} {ψ : Covector → F} {x : Covector}
    {n : WithTop ℕ∞} (hψ : ContDiffAt ℝ n ψ (toNormal c x)) :
    ContDiffAt ℝ n (pullback c ψ) x :=
  hψ.comp x (toNormal c).contDiff.contDiffAt

/-- The real first differential of a pulled-back field is the original differential composed with ct. -/
theorem hasFDerivAt_pullback {c : ℝ} {ψ : Covector → F} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ (toNormal c x)) :
    HasFDerivAt (pullback c ψ) ((fderiv ℝ ψ (toNormal c x)).comp (toNormal c)) x :=
  hψ.hasFDerivAt.comp x (toNormal c).hasFDerivAt

/-- A genuine first directional derivative pulls back along the actual image of its direction. -/
theorem directionalDerivative_pullback {c : ℝ} {ψ : Covector → F} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ (toNormal c x)) (v : Covector) :
    directionalDerivative (pullback c ψ) v x =
      directionalDerivative ψ (toNormal c v) (toNormal c x) := by
  unfold directionalDerivative
  rw [(hasFDerivAt_pullback hψ).fderiv]
  rfl

/-- Local C² regularity permits differentiating the first-derivative function identity,
so both derivatives use the same actual image direction. -/
theorem secondDirectionalDerivative_pullback {c : ℝ} {ψ : Covector → F} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal c x)) (v : Covector) :
    secondDirectionalDerivative (pullback c ψ) v x =
      secondDirectionalDerivative ψ (toNormal c v) (toNormal c x) := by
  have hn := (toNormal c).continuous.continuousAt.eventually
    (eventually_differentiableAt_of_contDiffAt_two hψ)
  have he : directionalDerivative (pullback c ψ) v =ᶠ[𝓝 x]
      pullback c (directionalDerivative ψ (toNormal c v)) := by
    filter_upwards [hn] with z hz
    exact directionalDerivative_pullback hz v
  have hd := differentiableAt_directionalDerivative_of_contDiffAt_two hψ (toNormal c v)
  change (fderiv ℝ (directionalDerivative (pullback c ψ) v) x) v = _
  rw [he.fderiv_eq, (hasFDerivAt_pullback hd).fderiv]
  rfl

/-- Scaling a constant direction twice gives the square scalar factor on the actual second derivative. -/
theorem secondDirectionalDerivative_smul {ψ : Covector → F} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ x) (a : ℝ) (v : Covector) :
    secondDirectionalDerivative ψ (a • v) x =
      (a ^ 2) • secondDirectionalDerivative ψ v x := by
  have he : directionalDerivative ψ (a • v) = fun z => a • directionalDerivative ψ v z := by
    funext z
    exact map_smul (fderiv ℝ ψ z) a v
  have hd := (differentiableAt_directionalDerivative_of_contDiffAt_two hψ v).hasFDerivAt
  change (fderiv ℝ (directionalDerivative ψ (a • v)) x) (a • v) = _
  rw [he, (hd.fun_const_smul a).fderiv]
  simp only [smul_apply, map_smul, smul_smul, pow_two,
    secondDirectionalDerivative, directionalDerivative]

/-- The actual second physical-time partial of the pullback is c² times the normal second partial. -/
theorem time_second {c : ℝ} {ψ : Covector → F} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal c x)) :
    secondDirectionalDerivative (pullback c ψ) (coordinateVector 0) x =
      (c ^ 2) • secondDirectionalDerivative ψ (coordinateVector 0) (toNormal c x) := by
  rw [secondDirectionalDerivative_pullback hψ, toNormal_time,
    secondDirectionalDerivative_smul hψ]

/-- The actual second spatial partials are unchanged at the corresponding normal-coordinate point. -/
theorem spatial_second {c : ℝ} {ψ : Covector → F} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal c x)) (i : Fin 3) :
    secondDirectionalDerivative (pullback c ψ) (coordinateVector i.succ) x =
      secondDirectionalDerivative ψ (coordinateVector i.succ) (toNormal c x) := by
  rw [secondDirectionalDerivative_pullback hψ, toNormal_spatial]

end FoliationQM.LaboratoryCoordinates
