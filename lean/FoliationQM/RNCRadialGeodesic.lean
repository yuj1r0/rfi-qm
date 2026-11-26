module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Radial geodesics in normal coordinates

In affine normal coordinates the radial curve with initial velocity `v`
has coordinate expression `t ↦ t • v`. Its geodesic equation says that
the Christoffel contraction vanishes along this line near the center.
Differentiating that equality supplies the cubic constraint on the
Christoffel first jet used in the normal-coordinate curvature formula.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCRadialGeodesic

open scoped BigOperators Topology

/-- Four real coordinates for the affine normal chart. -/
abbrev V := Fin 4 → ℝ

/-- Each radial line satisfies the affine geodesic equation near the chart center. -/
def radialNormal (G : V → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ (v : V) (r : Fin 4), ∀ᶠ t : ℝ in 𝓝 0, ∑ b, ∑ c, G (t • v) r b c * v b * v c = 0

/-- The coordinate velocity of the radial curve is constant along the entire line. -/
theorem hasDerivAt_radial (v : V) (t : ℝ) : HasDerivAt (fun s : ℝ => s • v) v t := by
  simpa using (hasDerivAt_id t).smul_const v

/-- The ordinary coordinate acceleration of each affine radial line vanishes. -/
theorem acceleration_radial (v : V) (t : ℝ) :
    deriv (deriv (fun s : ℝ => s • v)) t = 0 := by
  have hv : deriv (fun s : ℝ => s • v) = fun _ => v := funext fun s => (hasDerivAt_radial v s).deriv
  rw [hv, deriv_const]

variable {G : V → Fin 4 → Fin 4 → Fin 4 → ℝ}

/-- Evaluation of the geodesic equation gives the quadratic constraint at the center. -/
theorem center_contraction (h : radialNormal G) (v : V) (r : Fin 4) :
    ∑ b, ∑ c, G 0 r b c * v b * v c = 0 := by
  simpa using (h v r).self_of_nhds

/-- The derivative of the Christoffel contraction along a radial geodesic is its cubic first-jet contraction. -/
theorem hasDerivAt_contraction
    (hG : ∀ r b c, DifferentiableAt ℝ (fun y => G y r b c) 0) (v : V) (r : Fin 4) :
    HasDerivAt (fun t : ℝ => ∑ b, ∑ c, G (t • v) r b c * v b * v c)
      (∑ b, ∑ c, fderiv ℝ (fun y => G y r b c) 0 v * v b * v c) 0 := by
  apply HasDerivAt.fun_sum
  intro b _
  apply HasDerivAt.fun_sum
  intro c _
  have hc := (hG r b c).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_radial v 0)
    (zero_smul ℝ v).symm
  exact (hc.mul_const (v b)).mul_const (v c)

/-- Differentiating the radial geodesic equation gives a zero cubic contraction at the chart center. -/
theorem derivative_contraction (h : radialNormal G)
    (hG : ∀ r b c, DifferentiableAt ℝ (fun y => G y r b c) 0) (v : V) (r : Fin 4) :
    ∑ b, ∑ c, fderiv ℝ (fun y => G y r b c) 0 v * v b * v c = 0 :=
  (hasDerivAt_contraction hG v r).unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq (h v r))

end FoliationQM.RNCRadialGeodesic
