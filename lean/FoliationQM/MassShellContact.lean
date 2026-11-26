module

public import FoliationQM.ContactExteriorWedge
public import FoliationQM.MassShellForms
public import Mathlib.Tactic.Ring

/-!
# The actual mass-shell forms and their contact exterior product

Source: v13 `thm:contact_period`, part (i). The representatives below are
genuine homogeneous exterior-algebra expressions of degrees one and two.
Their determinant evaluations are proved equal to the actual pulled-back
Liouville form and its actual exterior derivative on every tangent tuple.
The seven-form is their actual exterior product, not a stipulated scalar
coefficient. The positive-energy chart also covers regular massless points.
Action compactification, capacity and rotor assertions remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.MassShellContact
open ContactExteriorBasics ContactExteriorWedge

/-- The degree-one exterior representative of the actual shell Liouville form. -/
def alphaRepresentative (m c : ℝ) (q : Space) : Forms :=
  alphaExterior (MassShellChart.energy m c q) (q 2) (q 4) (q 6)

/-- The degree-two exterior representative of the actual differentiated shell Liouville form. -/
def differentialRepresentative (m c : ℝ) (q : Space) : Forms :=
  omegaExterior (MassShellChart.energy m c q) (q 2) (q 4) (q 6)

/-- The actual exterior product of the shell one-form and the cube of its exterior differential. -/
def contactVolume (m c : ℝ) (q : Space) : Forms :=
  alphaRepresentative m c q * differentialRepresentative m c q ^ 3

/-- Determinant evaluation of the degree-one representative gives the full Liouville pairing. -/
theorem alphaExterior_evaluation (p0 p1 p2 p3 : ℝ) (v : Space) :
    evalOne (alphaExterior p0 p1 p2 p3) v =
      -(p0 * v 0 + p1 * v 1 + p2 * v 3 + p3 * v 5) := by
  simp only [alphaExterior, evalOne_add, evalOne_smul, evalOne_e]
  ring

/-- Determinant evaluation of the degree-two representative gives the full restricted canonical pairing. -/
theorem omegaExterior_evaluation (p0 p1 p2 p3 : ℝ) (v w : Space) :
    evalTwo (omegaExterior p0 p1 p2 p3) v w =
      v 0 * ((p1 * w 2 + p2 * w 4 + p3 * w 6) / p0) -
      w 0 * ((p1 * v 2 + p2 * v 4 + p3 * v 6) / p0) +
      (v 1 * w 2 - w 1 * v 2) + (v 3 * w 4 - w 3 * v 4) +
      (v 5 * w 6 - w 5 * v 6) := by
  simp only [omegaExterior, evalTwo_add, evalTwo_smul, evalTwo_e_mul_e]
  ring

/-- The degree-one exterior representative agrees with the actual chart pullback on every vector. -/
theorem alphaRepresentative_eq_pullback {m c : ℝ} {q : Space}
    (hE : 0 < MassShellChart.energy m c q) (v : Space) :
    evalOne (alphaRepresentative m c q) v =
      MassShellForms.pullback m c q ![v] := by
  rw [alphaRepresentative, alphaExterior_evaluation, MassShellForms.pullback_apply hE]
  rfl

/-- The degree-two exterior representative agrees with the actual exterior derivative on every pair. -/
theorem differentialRepresentative_eq_extDeriv {m c : ℝ} {q : Space}
    (hE : 0 < MassShellChart.energy m c q) (v w : Space) :
    evalTwo (differentialRepresentative m c q) v w =
      extDeriv (MassShellForms.pullback m c) q ![v, w] := by
  rw [differentialRepresentative, omegaExterior_evaluation,
    MassShellForms.extDeriv_pullback_coordinates hE]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The positive-square-root chart energy satisfies the exact source mass-shell polynomial. -/
theorem energy_shell_identity (m c : ℝ) (q : Space) :
    MassShellChart.energy m c q ^ 2 - q 2 ^ 2 - q 4 ^ 2 - q 6 ^ 2 = m ^ 2 * c ^ 2 := by
  have h := MassShellChart.energy_sq m c q
  dsimp [MassShellChart.energySquared] at h
  linarith

/-- The actual contact exterior product of the identified shell forms has the source coefficient. -/
theorem contactVolume_eq {m c : ℝ} {q : Space}
    (hE : 0 < MassShellChart.energy m c q) :
    contactVolume m c q = (-6 * m ^ 2 * c ^ 2 / MassShellChart.energy m c q) • volume := by
  exact alpha_mul_omega_cube_on_shell _ _ _ _ _ _ hE.ne' (energy_shell_identity m c q)

/-- Genuine determinant evaluation of the actual seven-form gives the source contact coefficient. -/
theorem contactVolume_evaluation {m c : ℝ} {q : Space}
    (hE : 0 < MassShellChart.energy m c q) :
    evaluation 7 tangent (contactVolume m c q) =
      -6 * m ^ 2 * c ^ 2 / MassShellChart.energy m c q := by
  rw [contactVolume_eq hE, map_smul, evaluation_volume, smul_eq_mul, mul_one]

/-- On every regular positive-energy shell point the actual contact volume is nonzero exactly for nonzero mass. -/
theorem contactVolume_ne_zero_iff {m c : ℝ} {q : Space}
    (hc : 0 < c) (hE : 0 < MassShellChart.energy m c q) :
    contactVolume m c q ≠ 0 ↔ m ≠ 0 :=
  contact_volume_ne_zero_iff _ _ _ _ _ _ hE hc (energy_shell_identity m c q)

/-- Under the source convention m ≥ 0, contact nondegeneracy holds exactly when m > 0. -/
theorem contactVolume_ne_zero_iff_mass_pos {m c : ℝ} {q : Space}
    (hm : 0 ≤ m) (hc : 0 < c) (hE : 0 < MassShellChart.energy m c q) :
    contactVolume m c q ≠ 0 ↔ 0 < m := by
  rw [contactVolume_ne_zero_iff hc hE]
  exact ⟨fun h => lt_of_le_of_ne hm h.symm, ne_of_gt⟩

/-- Every massive future-shell chart point has nonzero genuine contact volume. -/
theorem massive_contactVolume_ne_zero {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (q : Space) :
    contactVolume m c q ≠ 0 :=
  (contactVolume_ne_zero_iff hc (MassShellChart.energy_pos hm hc q)).mpr hm.ne'

/-- The actual exterior differential remains nonzero at massless positive energy although its contact seven-form vanishes. -/
theorem massless_differential_nonzero_volume_zero {c : ℝ} {q : Space}
    (hE : 0 < MassShellChart.energy 0 c q) :
    extDeriv (MassShellForms.pullback 0 c) q ≠ 0 ∧ contactVolume 0 c q = 0 := by
  refine ⟨MassShellForms.extDeriv_pullback_ne_zero hE, ?_⟩
  rw [contactVolume_eq hE]
  simp

/-- The positive-energy massless comparison has a concrete regular example, so its hypotheses are nonvacuous. -/
theorem massless_regular_example (c : ℝ) :
    MassShellChart.energy 0 c (tangent 2) = 1 ∧
      extDeriv (MassShellForms.pullback 0 c) (tangent 2) ≠ 0 ∧
      contactVolume 0 c (tangent 2) = 0 := by
  have h : MassShellChart.energy 0 c (tangent 2) = 1 := by
    norm_num [MassShellChart.energy, MassShellChart.energySquared, tangent, Pi.single_apply]
  exact ⟨h, massless_differential_nonzero_volume_zero (by rw [h]; norm_num)⟩

/-- The source Reeb vector expressed in the actual seven shell coordinates. -/
def chartReeb (m c : ℝ) (q : Space) : Space :=
  MassShellChart.inverse (ContactReeb.reeb m c (MassShellChart.chart m c q).2)

/-- The actual chart derivative sends the coordinate Reeb vector to the ambient restricted Reeb vector. -/
theorem fderiv_chart_chartReeb {m c : ℝ} {q : Space}
    (hE : 0 < MassShellChart.energy m c q) :
    fderiv ℝ (MassShellChart.chart m c) q (chartReeb m c q) =
      ContactReeb.reeb m c (MassShellChart.chart m c q).2 := by
  rw [MassShellChart.fderiv_chart hE, chartReeb]
  exact MassShellChart.chartDerivative_inverse hE (ContactReeb.reeb_tangent _ _ _)

/-- The actual shell Liouville pullback normalizes the coordinate Reeb vector to one. -/
theorem pullback_chartReeb {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (q : Space) :
    MassShellForms.pullback m c q (fun _ => chartReeb m c q) = 1 := by
  have hE := MassShellChart.energy_pos hm hc q
  change LiouvilleDifferential.liouville (MassShellChart.chart m c q)
    (fun _ => fderiv ℝ (MassShellChart.chart m c) q (chartReeb m c q)) = 1
  rw [fderiv_chart_chartReeb hE]
  exact LiouvilleDifferential.liouville_reeb_eq_one hm hc (MassShellChart.chart_onShell hE)

/-- The actual exterior derivative of the shell pullback annihilates the coordinate Reeb vector. -/
theorem extDeriv_pullback_chartReeb {m c : ℝ} {q : Space}
    (hE : 0 < MassShellChart.energy m c q) (v : Space) :
    extDeriv (MassShellForms.pullback m c) q ![chartReeb m c q, v] = 0 := by
  rw [MassShellForms.extDeriv_pullback_apply hE]
  change ContactReeb.canonicalTwo
    (MassShellChart.chartDerivative m c q (chartReeb m c q))
    (MassShellChart.chartDerivative m c q v) = 0
  rw [← MassShellChart.fderiv_chart hE, fderiv_chart_chartReeb hE,
    MassShellChart.fderiv_chart hE]
  exact ContactReeb.canonicalTwo_reeb_tangent _ _ _ _
    (MassShellChart.chartDerivative_tangent hE v)

/-- The genuine pulled-back one-form and its exterior derivative characterize the unique Reeb vector in shell coordinates. -/
theorem actual_chart_reeb_characterization {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (q w : Space) :
    (MassShellForms.pullback m c q (fun _ => w) = 1 ∧
      ∀ v : Space, extDeriv (MassShellForms.pullback m c) q ![w, v] = 0) ↔
      w = chartReeb m c q := by
  have hE := MassShellChart.energy_pos hm hc q
  constructor
  · rintro ⟨ha, hd⟩
    change LiouvilleDifferential.liouville (MassShellChart.chart m c q)
      (fun _ => fderiv ℝ (MassShellChart.chart m c) q w) = 1 at ha
    rw [LiouvilleDifferential.liouville_apply, MassShellChart.fderiv_chart hE] at ha
    have hh : ∀ v : ContactReeb.Ambient,
        ContactReeb.Tangent (MassShellChart.chart m c q).2 v →
        ContactReeb.canonicalTwo (MassShellChart.chartDerivative m c q w) v = 0 := by
      intro v hv
      have h := hd (MassShellChart.inverse v)
      rw [MassShellForms.extDeriv_pullback_apply hE] at h
      change ContactReeb.canonicalTwo (MassShellChart.chartDerivative m c q w)
        (MassShellChart.chartDerivative m c q (MassShellChart.inverse v)) = 0 at h
      rwa [MassShellChart.chartDerivative_inverse hE hv] at h
    have hy := ContactReeb.reeb_unique hm hc (MassShellChart.chart_onShell hE) ha hh
    apply MassShellChart.chartDerivative_injective m c q
    rw [hy, ← MassShellChart.fderiv_chart hE, fderiv_chart_chartReeb hE]
  · rintro rfl
    exact ⟨pullback_chartReeb hm hc q, fun v => extDeriv_pullback_chartReeb hE v⟩

end FoliationQM.MassShellContact
