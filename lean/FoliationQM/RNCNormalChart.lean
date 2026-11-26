module

public import FoliationQM.RNCConnectionCyclic
public import FoliationQM.RNCCoordinateConnection
public import FoliationQM.RNCMetricHalfDensity

/-!
# Metric normal-chart data at the chosen event

The inputs are the orthonormal value of the metric, its local symmetry, and
the radial affine geodesic property of its coordinate Levi-Civita connection.
The vanishing of the metric and connection first-order terms needed in the
curvature calculation follows by differentiation and polarization.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.RNCNormalChart

open LorentzMatrixGroup RNCCoordinateConnection RNCRadialGeodesic Filter

/-- A coordinate metric in an orthonormal radial normal chart centered at zero. -/
structure IsNormal (g : Covector → Mat4) : Prop where
  metric_center : g 0 = eta
  symmetric : ∀ᶠ y in 𝓝 0, (g y).IsSymm
  radial : radialNormal (christoffel g)

variable {g : Covector → Mat4}

/-- The Minkowski center is invertible. -/
theorem center_unit (h : IsNormal g) : IsUnit (g 0) :=
  (g 0).isUnit_iff_isUnit_det.mpr (by simp [h.metric_center, eta_det])

/-- Torsion symmetry holds as an equality of coordinate functions on a neighborhood of the center. -/
theorem symmetry_germ (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (r b c : Fin 4) :
    (fun y => christoffel g y r b c) =ᶠ[𝓝 0] (fun y => christoffel g y r c b) := by
  filter_upwards [PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hg,
    eventually_eventually_nhds.2 h.symmetric] with y hy hs
  exact christoffel_symmetric (dG_isSymm hy hs) r b c

/-- Every coefficient of the coordinate Levi-Civita connection vanishes at the normal center. -/
theorem connection_zero (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) (r b c : Fin 4) :
    christoffel g 0 r b c = 0 :=
  RNCConnectionCyclic.center_entries h.radial (christoffel_symmetric (dG_isSymm hg h.symmetric)) r b c

/-- The radial geodesic equation and metric compatibility imply stationarity of the entire metric matrix. -/
theorem metric_gradient_zero (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) : fderiv ℝ g 0 = 0 :=
  fderiv_eq_zero_of_christoffel_zero hg h.symmetric h.metric_center (connection_zero h hg)

/-- The exact first coordinate derivatives of the Levi-Civita symbols obey the normal-coordinate cyclic identity. -/
theorem connection_cyclic (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (r a b c : Fin 4) :
    fderiv ℝ (fun y => christoffel g y r b c) 0 (axis a) +
    fderiv ℝ (fun y => christoffel g y r c a) 0 (axis b) +
    fderiv ℝ (fun y => christoffel g y r a b) 0 (axis c) = 0 :=
  RNCConnectionCyclic.cyclic_entries h.radial
    (fun i j k => (contDiffAt_christoffel hg (center_unit h) i j k).differentiableAt_one)
    (symmetry_germ h hg) r a b c

/-- The signed metric Hessian formula applies to the actual determinant in every such normal chart. -/
theorem weight_hessian (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (u v : Covector) :
    fderiv ℝ (fderiv ℝ (RNCVolumeDensity.metricWeight ∘ g)) 0 u v =
      (eta * (fderiv ℝ (fderiv ℝ g) 0 u v)).trace / 4 :=
  RNCMetricHalfDensity.normal_hessian hg h.metric_center
    (metric_gradient_zero h (hg.differentiableAt (by decide))) u v

end FoliationQM.RNCNormalChart
