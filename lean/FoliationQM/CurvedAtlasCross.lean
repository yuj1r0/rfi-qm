module

public import FoliationQM.CurvedAtlasVariation

/-!
# Polarized global action densities and finite variation sums

The mixed kinetic and mass density is computed from the atlas wave geometry.
It is real-linear in each field for real variations, so every finite
decomposition of a compact test yields the corresponding finite sum of
first-variation densities. The exact quadratic density identity controls
the finite action increment before integration.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasCross

open Set Filter CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasAction
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

/-- The zero field is regular in all metric charts. -/
theorem regular_zero (A : MetricAtlas X) : Regular A 2 (fun _ : X => (0 : ℂ)) :=
  fun _ _ _ => contDiffAt_const

/-- Sums of actual regular global fields remain regular in every chart. -/
theorem regular_add (A : MetricAtlas X) {u v : X → ℂ}
    (hu : Regular A 2 u) (hv : Regular A 2 v) : Regular A 2 (u + v) :=
  fun i y hy => (hu i y hy).add (hv i y hy)

/-- A real multiple of a regular global field is regular in every chart. -/
theorem regular_smul (A : MetricAtlas X) {u : X → ℂ}
    (hu : Regular A 2 u) (a : ℝ) : Regular A 2 (a • u) :=
  fun i y hy => contDiffAt_const.smul (hu i y hy)

/-- Every finite sum of regular global fields is regular. -/
theorem regular_sum {ι : Type*} (A : MetricAtlas X) (s : Finset ι) {u : ι → X → ℂ}
    (hu : ∀ i ∈ s, Regular A 2 (u i)) : Regular A 2 (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! regular_zero A
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact regular_add A (hu i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

/-- The global polarized kinetic-minus-mass density, conjugate-linear in its first field. -/
def crossField (p : MassiveParameters) (A : MetricAtlas X) (u v : X → ℂ) (x : X) : ℂ :=
  p.hbar ^ 2 • kineticField A u v x -
    (p.m ^ 2 * p.c ^ 2 - p.hbar ^ 2 / 6 * scalarField A x) • (star (u x) * v x)

/-- The polarized global density is computed by the literal coordinate cross density in every chart. -/
theorem crossField_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {u v : X → ℂ} (hu : Regular A 2 u) (hv : Regular A 2 v)
    (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    crossField p A u v x =
      CurvedKGFirstVariation.cross p (A.metric i) (repr A i u) (repr A i v) (A.chart i x) := by
  rw [crossField, CurvedKGFirstVariation.cross, CurvedPolarAction.massTerm,
    kineticField_chart A hA hu hv i hx, scalarField_chart A hA i hx,
    repr_chart A i u hx, repr_chart A i v hx]

/-- The zero first field gives zero polarized density. -/
theorem crossField_zero_left (p : MassiveParameters) (A : MetricAtlas X) (v : X → ℂ) :
    crossField p A (fun _ => 0) v = 0 := by
  funext x
  simp [crossField, kineticField, descend, CurvedFluxGreen.kinetic, CurvedAtlasDescent.repr, Function.comp_def]

/-- Real affine perturbation in the first slot gives the corresponding affine mixed density. -/
theorem crossField_perturb_left (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {u v w : X → ℂ} (hu : Regular A 2 u) (hv : Regular A 2 v) (hw : Regular A 2 w)
    (t : ℝ) :
    crossField p A (CurvedAtlasVariation.perturb u v t) w =
      crossField p A u w + t • crossField p A v w := by
  funext x
  obtain ⟨i, hi⟩ := exists_chart A x
  have hy := (A.chart i).map_source hi
  rw [crossField_chart p A hA (CurvedAtlasVariation.regular_perturb A hu hv t) hw i hi]
  change CurvedKGFirstVariation.cross p (A.metric i)
    (CurvedKGFirstVariation.perturb (repr A i u) (repr A i v) t) (repr A i w) (A.chart i x) = _
  rw [CurvedKGFirstVariation.cross_perturb_left p (A.metric i)
    ((hu i _ hy).differentiableAt (by decide)) ((hv i _ hy).differentiableAt (by decide))]
  simp only [Pi.add_apply, Pi.smul_apply, crossField_chart p A hA hu hw i hi,
    crossField_chart p A hA hv hw i hi]

/-- Additivity in the first slot is derived from the actual differentiated fields. -/
theorem crossField_add_left (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {u v w : X → ℂ} (hu : Regular A 2 u) (hv : Regular A 2 v) (hw : Regular A 2 w) :
    crossField p A (u + v) w = crossField p A u w + crossField p A v w := by
  have he : CurvedAtlasVariation.perturb u v 1 = u + v := by
    funext x
    simp only [CurvedAtlasVariation.perturb, one_smul, Pi.add_apply]
  simpa only [he, one_smul] using crossField_perturb_left p A hA hu hv hw 1

/-- The complex polarized density commutes with finite sums of regular test fields. -/
theorem crossField_sum_left {ι : Type*} (p : MassiveParameters) (A : MetricAtlas X)
    (hA : SmoothLorentz A) (s : Finset ι) {u : ι → X → ℂ} {v : X → ℂ}
    (hu : ∀ i ∈ s, Regular A 2 (u i)) (hv : Regular A 2 v) :
    crossField p A (∑ i ∈ s, u i) v = ∑ i ∈ s, crossField p A (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! crossField_zero_left p A v
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, crossField_add_left p A hA
      (hu i (Finset.mem_insert_self _ _)) (regular_sum A s (fun j hj => hu j (Finset.mem_insert_of_mem hj))) hv,
      ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))]

/-- The real self-pairing is the actual global quadratic action density. -/
theorem crossField_self_re (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {u : X → ℂ} (hu : Regular A 2 u) (x : X) :
    (crossField p A u u x).re = kgDensityField p A u x := by
  obtain ⟨i, hi⟩ := exists_chart A x
  rw [crossField_chart p A hA hu hu i hi, kgDensityField_chart p A hA hu i hi]
  exact CurvedKGFirstVariation.cross_self_re p (A.metric i) _ _

/-- The global finite-parameter action density has its exact linear and quadratic variation terms. -/
theorem density_perturb (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (t : ℝ) (x : X) :
    kgDensityField p A (CurvedAtlasVariation.perturb ψ η t) x =
      kgDensityField p A ψ x + 2 * t * (crossField p A η ψ x).re + t ^ 2 * kgDensityField p A η x := by
  obtain ⟨i, hi⟩ := exists_chart A x
  have hy := (A.chart i).map_source hi
  rw [kgDensityField_chart p A hA (CurvedAtlasVariation.regular_perturb A hψ hη t) i hi,
    kgDensityField_chart p A hA hψ i hi, kgDensityField_chart p A hA hη i hi,
    crossField_chart p A hA hη hψ i hi]
  exact CurvedKGFirstVariation.density_perturb p (hA.symmetric i _ hy)
    ((hψ i _ hy).differentiableAt (by decide)) ((hη i _ hy).differentiableAt (by decide)) t

/-- Equality of first-field germs gives the same polarized density. -/
theorem crossField_germ_left (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {u v w : X → ℂ} (hu : Regular A 2 u) (hv : Regular A 2 v) (hw : Regular A 2 w)
    {x : X} (he : u =ᶠ[𝓝 x] v) : crossField p A u w x = crossField p A v w x := by
  obtain ⟨i, hi⟩ := exists_chart A x
  have hc := (A.chart i).continuousAt_symm ((A.chart i).map_source hi)
  have hg : repr A i u =ᶠ[𝓝 (A.chart i x)] repr A i v := by
    have he' : ∀ᶠ z in 𝓝 ((A.chart i).symm (A.chart i x)), u z = v z := by
      simpa only [(A.chart i).left_inv hi] using (show ∀ᶠ z in 𝓝 x, u z = v z from he)
    exact hc.eventually he'
  rw [crossField_chart p A hA hu hw i hi, crossField_chart p A hA hv hw i hi]
  simp only [CurvedKGFirstVariation.cross, CurvedFluxGreen.kinetic, hg.fderiv_eq (𝕜 := ℝ),
    hg.self_of_nhds]

/-- A test which vanishes near a point has zero mixed density at that point. -/
theorem crossField_zero_germ (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {u v : X → ℂ} (hu : Regular A 2 u) (hv : Regular A 2 v) {x : X}
    (he : u =ᶠ[𝓝 x] (fun _ => 0)) : crossField p A u v x = 0 := by
  rw [crossField_germ_left p A hA hu (regular_zero A) hv he, crossField_zero_left]
  rfl

/-- The support of a mixed variation density lies in the closed support of its first test field. -/
theorem crossField_support (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {u v : X → ℂ} (hu : Regular A 2 u) (hv : Regular A 2 v) :
    Function.support (crossField p A u v) ⊆ tsupport u := by
  intro x hx
  by_contra hn
  exact hx (crossField_zero_germ p A hA hu hv (notMem_tsupport_iff_eventuallyEq.mp hn))

end FoliationQM.CurvedAtlasCross
