module
public import FoliationQM.DiracHSDensity
public import FoliationQM.DiracCurveAction

/-!
# HS action and compact action increments on the polar quotient

For v13 `thm:dirac_lift`, integrate the polar HS density itself on the
flat domain. The density comparison gives equality with the Dirac integral
on each represented locally differentiable field. Along a compact interior
polar variation the increment is integrable even if the background action
has not been assumed finite.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.DiracHSAction
open Set Filter MeasureTheory DiracMatrices DiracPolarCoordinates DiracPolarVariation
open DiracPolarVariationTransport

variable (hbar c m : ℝ)

/-- The polar HS action is the Lebesgue integral of the actual real polar density. -/
def action (q : Covector → Q) (U : Set Covector) : ℝ :=
  ∫ x in U, DiracHSDensity.density hbar c m q x

/-- The polar action increment integrates the change before taking separate integrals. -/
def relativeAction (q r : Covector → Q) (U : Set Covector) : ℝ :=
  ∫ x in U, DiracHSDensity.density hbar c m r x - DiracHSDensity.density hbar c m q x

variable {U : Set Covector} {q r : Covector → Q} {ψ φ : Covector → Spinor}

/-- Equality of the two density integrals on a represented locally C¹ field. -/
theorem action_eq (hU : IsOpen U) (h : Represents U q ψ) (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x) :
    action hbar c m q U = DiracRelativeAction.action hbar c m ψ U :=
  setIntegral_congr_fun hU.measurableSet (fun x hx => DiracHSDensity.density_eq_dens hbar c m hU h hx (hψ x hx))

/-- Finiteness of the ordinary background density agrees in the two field coordinates. -/
theorem integrable_iff (hU : IsOpen U) (h : Represents U q ψ) (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x) :
    IntegrableOn (DiracHSDensity.density hbar c m q) U ↔ IntegrableOn (DiracActionSupport.dens hbar c m ψ) U :=
  integrableOn_congr_fun (fun x hx => DiracHSDensity.density_eq_dens hbar c m hU h hx (hψ x hx)) hU.measurableSet

/-- The relative polar action equals the relative Dirac action for two represented fields. -/
theorem relative_eq (hU : IsOpen U) (h : Represents U q ψ) (hr : Represents U r φ)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x) (hφ : ∀ x ∈ U, ContDiffAt ℝ 1 φ x) :
    relativeAction hbar c m q r U = DiracRelativeAction.relativeAction hbar c m ψ φ U :=
  setIntegral_congr_fun hU.measurableSet (fun x hx =>
    congrArg₂ (fun a b : ℝ => a - b)
      (DiracHSDensity.density_eq_dens hbar c m hU hr hx (hφ x hx))
      (DiracHSDensity.density_eq_dens hbar c m hU h hx (hψ x hx)))

/-- For integrable polar densities the direct increment is the difference of ordinary actions. -/
theorem relative_eq_action_sub (hq : IntegrableOn (DiracHSDensity.density hbar c m q) U)
    (hr : IntegrableOn (DiracHSDensity.density hbar c m r) U) :
    relativeAction hbar c m q r U = action hbar c m r U - action hbar c m q U := integral_sub hr hq

/-- The integrand of a polar slice increment is the change in the actual transported spinor field. -/
theorem difference_eq (hU : IsOpen U) (h : Represents U q ψ) (P : PolarVariation U q)
    {t : ℝ} (ht : t ∈ P.params) {x : Covector} (hx : x ∈ U) :
    DiracHSDensity.density hbar c m (slice P t) x - DiracHSDensity.density hbar c m q x =
      DiracCurveJetCalculus.density hbar c m (toSpinor hU h P).family t x -
      DiracActionSupport.dens hbar c m ψ x := by
  have hr := toSpinor_represents hU h P t
  have hφ := (smooth_iff hU hr hx).mp (smooth_slice P ht hx)
  have hψ := (smooth_iff hU h hx).mp (smooth_background P hx)
  rw [DiracHSDensity.density_eq_dens hbar c m hU hr hx (hφ.of_le (by simp)),
    DiracHSDensity.density_eq_dens hbar c m hU h hx (hψ.of_le (by simp)),
    DiracCurveJetCalculus.density_eq_fieldDensityRe]
  rfl

/-- Every admissible slice increment is integrable, with only compact interior support
and the intrinsic variation regularity as analytic inputs. -/
theorem integrable_difference (hU : IsOpen U) (h : Represents U q ψ) (P : PolarVariation U q)
    {t : ℝ} (ht : t ∈ P.params) :
    IntegrableOn (fun x => DiracHSDensity.density hbar c m (slice P t) x - DiracHSDensity.density hbar c m q x) U :=
  (DiracCurveAction.integrable_difference hbar c m (toSpinor hU h P).toVariation hU ht).congr_fun
    (fun _ hx => (difference_eq hbar c m hU h P ht hx).symm) hU.measurableSet

/-- The polar variation alone supplies a finite increment by decoding its own background. -/
theorem integrable_polar_increment (hU : IsOpen U) (P : PolarVariation U q) {t : ℝ} (ht : t ∈ P.params) :
    IntegrableOn (fun x => DiracHSDensity.density hbar c m (slice P t) x - DiracHSDensity.density hbar c m q x) U :=
  integrable_difference hbar c m hU (show Represents U q (fun x => decode (q x)) from fun _ _ => rfl) P ht

/-- At each allowed parameter the actual relative integrals agree for the transported variation. -/
theorem relative_slice_eq (hU : IsOpen U) (h : Represents U q ψ) (P : PolarVariation U q)
    {t : ℝ} (ht : t ∈ P.params) :
    relativeAction hbar c m q (slice P t) U = DiracRelativeAction.relativeAction hbar c m ψ
      (DiracCurveJetCalculus.slice (toSpinor hU h P).family t) U :=
  setIntegral_congr_fun hU.measurableSet (fun _ hx => difference_eq hbar c m hU h P ht hx)

end FoliationQM.DiracHSAction
