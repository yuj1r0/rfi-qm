module

public import FoliationQM.NormalLogDensity

/-! Actual fields in the v13 weighted coercivity estimate, on the laboratory
slice x⁰ = ct. The lower osmotic momentum has the minus sign in main line 605.
Its inverse-Minkowski square uses the positive spatial Euclidean norm. -/

@[expose] public section
noncomputable section
namespace FoliationQM.OsmoticSliceFields
open DressedMassDensityVariation LogDensityTransport ObserverFluxDensity LorentzCoordinates

/-- A point of the laboratory slice with first coordinate t = ct_lab. -/
def slicePoint (t : ℝ) (y : Spatial) : Covector := assemble t y

/-- The normal derivative of the logarithm of the density in x⁰ coordinates. -/
def normalScore (ρ : Covector → ℝ) (x : Covector) : ℝ :=
  phaseDifferential (fun z => Real.log (ρ z)) x 0

/-- The three Euclidean spatial components of the same logarithmic derivative. -/
def spatialScore (ρ : Covector → ℝ) (x : Covector) : Spatial :=
  spatialGradient (fun z => Real.log (ρ z)) x

/-- The dilatation in the manuscript includes both the velocity divergence and
the material derivative of the logarithm of normal momentum. -/
def dilatation (c : ℝ) (S : Covector → ℝ) (x : Covector) : ℝ :=
  spatialDivergence (phaseDrift c S) x +
    material c (phaseDrift c S) (fun z => Real.log (normalMomentum S z)) x

/-- Physical lower osmotic momentum defined from the actual log-density differential. -/
def infoMomentum (p : MassiveParameters) (ρ : Covector → ℝ) (x : Covector) : Covector :=
  (-p.hbar / 2) • phaseDifferential (fun z => Real.log (ρ z)) x

/-- Its Minkowski square splits into normal and spatial logarithmic derivatives. -/
theorem info_square (p : MassiveParameters) (ρ : Covector → ℝ) (x : Covector) :
    minkowski (infoMomentum p ρ x) (infoMomentum p ρ x) =
      p.hbar^2 / 4 * ((normalScore ρ x)^2 - speedSq (spatialScore ρ x)) := by
  simp only [minkowski, infoMomentum, Pi.smul_apply, smul_eq_mul, normalScore, speedSq,
    spatialDot, spatialScore, spatialGradient]
  let d := phaseDifferential (fun z => Real.log (ρ z)) x
  change _ = p.hbar^2 / 4 * ((d 0)^2 - (d 1 * d 1 + d 2 * d 2 + d 3 * d 3))
  dsimp only [d]
  ring

/-- On the transport shell the two derivative terms and the physical dilatation
sum to zero, with exactly one factor c on the normal derivative. -/
theorem normal_balance {c : ℝ} {ρ S : Covector → ℝ} {x : Covector} (hc : 0 < c)
    (h : NormalLogDensity.Formulas c ρ S x) :
    c * normalScore ρ x = -spatialDot (phaseDrift c S x) (spatialScore ρ x) - dilatation c S x := by
  have hn := h.2
  change normalScore ρ x = -spatialDot (phaseDrift c S x) (spatialScore ρ x) / c -
    dilatation c S x / c at hn
  rw [hn]
  field_simp [hc.ne']

end FoliationQM.OsmoticSliceFields
