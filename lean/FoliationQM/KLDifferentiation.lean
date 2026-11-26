module

public import FoliationQM.TranslatedKL
public import FoliationQM.DominatedIntegral

/-!
# Twice differentiating the actual translated KL integral

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, supplement
`prop:audit11_kl`. Common integrable envelopes bound the weighted first and
second actual derivatives of log density on one translation ball. These
are domination assumptions on the density, not an assumed derivative of KL.
Actual C2 regularity supplies all pointwise derivatives and measurability.
The mean value theorem first proves nearby KL integrability from its zero
base integrand, so no finite entropy assumption is added.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.KLDifferentiation

open MeasureTheory Filter Metric TranslatedKL
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

-- Cache the standard normed structures so nested operator-space topology
-- instances are resolved through the same operator norm in the pinned release.
local instance dualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Concrete common weighted log-derivative bounds on a positive translation
ball. No formula for a derivative of the KL integral is a field of this record. -/
structure Domination (f : E → ℝ) (μ : Measure E) (r : ℝ) where
  radius_pos : 0 < r
  firstBound : E → ℝ
  secondBound : E → ℝ
  first_integrable : Integrable firstBound μ
  second_integrable : Integrable secondBound μ
  first_le : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r, ‖firstIntegrand f a x‖ ≤ firstBound x
  second_le : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r, ‖secondIntegrand f a x‖ ≤ secondBound x

/-- The actual integral of the first translation differential. -/
def firstIntegral (f : E → ℝ) (μ : Measure E) (a : E) : E →L[ℝ] ℝ :=
  ∫ x, firstIntegrand f a x ∂μ

/-- The actual integral of the second translation differential. -/
def secondIntegral (f : E → ℝ) (μ : Measure E) (a : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  ∫ x, secondIntegrand f a x ∂μ

/-- Common first-derivative domination gives genuine derivative integrability. -/
theorem integrable_first {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) : Integrable (firstIntegrand f a) μ :=
  DominatedIntegral.integrable_derivative
    (fun b _ => (continuous_firstIntegrand hf hpos b).aestronglyMeasurable)
    D.first_le D.first_integrable ha

/-- Common second-derivative domination gives genuine Hessian-integrand integrability. -/
theorem integrable_second {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) : Integrable (secondIntegrand f a) μ :=
  DominatedIntegral.integrable_derivative
    (fun b _ => (continuous_secondIntegrand hf hpos b).aestronglyMeasurable)
    D.second_le D.second_integrable ha

omit [SecondCountableTopology E] in
/-- The actual translated KL density is integrable throughout the common ball,
derived from its zero value at the origin and the first derivative envelope. -/
theorem integrable_integrand {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) : Integrable (integrand f a) μ :=
  DominatedIntegral.integrable_slice D.radius_pos
    (fun b _ => (continuous_integrand hf hpos b).aestronglyMeasurable)
    (TranslatedKL.integrable_zero f μ) D.first_le D.first_integrable
    (Eventually.of_forall (fun x b _ => hasFDerivAt_integrand hf hpos b x)) ha

/-- First differentiation under the genuine translated KL integral follows
from the density's pointwise chain rule and common integrable envelope. -/
theorem hasFDerivAt_value {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) :
    HasFDerivAt (value f μ) (firstIntegral f μ a) a :=
  DominatedIntegral.hasFDerivAt_integral D.radius_pos
    (fun b _ => (continuous_integrand hf hpos b).aestronglyMeasurable)
    (TranslatedKL.integrable_zero f μ)
    (fun b _ => (continuous_firstIntegrand hf hpos b).aestronglyMeasurable)
    D.first_le D.first_integrable
    (Eventually.of_forall (fun x b _ => hasFDerivAt_integrand hf hpos b x)) ha

/-- The actual Frechet derivative of KL is the proved first integral. -/
theorem fderiv_value {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) :
    fderiv ℝ (value f μ) a = firstIntegral f μ a :=
  (hasFDerivAt_value hf hpos D ha).fderiv

/-- Differentiating the genuine first integral a second time uses the
actual second log derivative and its independent integrable envelope. -/
theorem hasFDerivAt_firstIntegral {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) :
    HasFDerivAt (firstIntegral f μ) (secondIntegral f μ a) a :=
  DominatedIntegral.hasFDerivAt_integral D.radius_pos
    (fun b _ => (continuous_firstIntegrand hf hpos b).aestronglyMeasurable)
    (integrable_first hf hpos D (mem_ball_self D.radius_pos))
    (fun b _ => (continuous_secondIntegrand hf hpos b).aestronglyMeasurable)
    D.second_le D.second_integrable
    (Eventually.of_forall (fun x b _ => hasFDerivAt_firstIntegrand hf hpos b x)) ha

/-- The actual derivative map of KL has the second-integral derivative.
The local equality needed to differentiate the first formula is proved on the ball. -/
theorem hasFDerivAt_fderiv_value {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) :
    HasFDerivAt (fderiv ℝ (value f μ)) (secondIntegral f μ a) a := by
  apply (hasFDerivAt_firstIntegral hf hpos D ha).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds ha] with b hb
  exact fderiv_value hf hpos D hb

/-- The actual Frechet Hessian of translated KL is the genuine second integral. -/
theorem fderiv_fderiv_value {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) :
    fderiv ℝ (fderiv ℝ (value f μ)) a = secondIntegral f μ a :=
  (hasFDerivAt_fderiv_value hf hpos D ha).fderiv

/-- Evaluation of the actual first KL derivative commutes with its integrable field. -/
theorem fderiv_value_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) (v : E) :
    fderiv ℝ (value f μ) a v = ∫ x, firstIntegrand f a x v ∂μ := by
  rw [fderiv_value hf hpos D ha]
  exact ContinuousLinearMap.integral_apply (integrable_first hf hpos D ha) v

/-- Both evaluations of the actual KL Hessian commute with the genuine
integrable continuous-bilinear-map field. -/
theorem fderiv_fderiv_value_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    {a : E} (ha : a ∈ ball (0 : E) r) (u v : E) :
    fderiv ℝ (fderiv ℝ (value f μ)) a u v = ∫ x, secondIntegrand f a x u v ∂μ := by
  rw [fderiv_fderiv_value hf hpos D ha]
  change (∫ x, secondIntegrand f a x ∂μ) u v = _
  rw [ContinuousLinearMap.integral_apply (integrable_second hf hpos D ha) u]
  have hi : Integrable (fun x => secondIntegrand f a x u) μ :=
    (integrable_second hf hpos D ha).apply_continuousLinearMap u
  exact ContinuousLinearMap.integral_apply hi v

end FoliationQM.KLDifferentiation
