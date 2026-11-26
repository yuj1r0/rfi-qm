module
public import FoliationQM.SourcePolarProductQuotient
public import FoliationQM.LocalPolarFields

/-!
# Independent local smooth representatives in the literal source coordinates

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. A source
representative is defined by literal equality of its quotient class:
positive real density, a real angle mapped to the existing four-pi
circle, and an actual determinant-one complex matrix. Local regularity
requires actual real-smooth density, real angle and matrix fields at the
point, with these constraints and quotient equality on a neighborhood.
It is not defined as regularity of the realized spinor.

The genuine forward polar map and the independently constructed two-chart
inverse prove that this local representative condition is equivalent to
real smoothness of the actual realized spinor field. The same criterion
is proved for the literal positive-density times angle-matrix sign
quotient. Open-domain forms and continuity in the existing natural
topologies follow. The recovered density is the actual bilinear invariant.
These are local Ck representative criteria; no global real-angle lift or
bundled smooth-manifold diffeomorphism is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Topology Filter
namespace FoliationQM.SourcePolarSmooth
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin PolarSpinorBilinears
open PolarAmplitudeTopology ChiralAngleCircle SourcePolarDatum SourcePolarRealization
open SourcePolarProductQuotient

/-- Literal source representatives have positive density, actual determinant one, and exactly the stated class with real angle reduced modulo four pi. -/
def Represents (rho beta : ℝ) (A : Mat2) (q : SourcePolarQuotient.SourceQuotient) : Prop :=
  ∃ (hrho : 0 < rho) (hA : A.det = 1),
    Quotient.mk SourcePolarQuotient.signSetoid
      ((⟨rho, hrho⟩ : PositiveDensity), (beta : Angle),
        (⟨A, hA⟩ : SpecialLinearMatrix)) = q

/-- The independently specified literal quotient representative realizes precisely the genuine polar spinor under its positivity and determinant constraints. -/
theorem represents_iff (rho beta : ℝ) (A : Mat2) (q : SourcePolarQuotient.SourceQuotient) :
    Represents rho beta A q ↔ 0 < rho ∧ A.det = 1 ∧
      (SourcePolarQuotient.regularHomeomorph q).val = polarSpinor rho beta (spin A) := by
  constructor
  · rintro ⟨hrho, hA, hq⟩
    refine ⟨hrho, hA, ?_⟩
    rw [← hq, SourcePolarQuotient.regularHomeomorph_apply_mk]
    exact realizeSource_coe ⟨rho, hrho⟩ beta ⟨A, hA⟩
  · rintro ⟨hrho, hA, hq⟩
    refine ⟨hrho, hA, ?_⟩
    apply SourcePolarQuotient.regularHomeomorph.injective
    apply Subtype.ext
    rw [SourcePolarQuotient.regularHomeomorph_apply_mk]
    exact (realizeSource_coe ⟨rho, hrho⟩ beta ⟨A, hA⟩).trans hq.symm

/-- The density of every literal source representative is the actual scalar-pseudoscalar invariant of its realized spinor. -/
theorem represents_density {rho beta : ℝ} {A : Mat2}
    {q : SourcePolarQuotient.SourceQuotient} (h : Represents rho beta A q) :
    invariantDensity (SourcePolarQuotient.regularHomeomorph q).val = rho := by
  obtain ⟨hrho, hA, he⟩ := (represents_iff _ _ _ _).mp h
  rw [he]
  exact PrincipalPolarChart.invariantDensity_polar rho beta A hrho.le hA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Independent local source regularity means actual Ck real density and real angle fields and a Ck matrix field representing the source quotient throughout a neighborhood. -/
def HasSmoothSourceRepresentativeAt (n : WithTop ℕ∞)
    (f : E → SourcePolarQuotient.SourceQuotient) (x : E) : Prop :=
  ∃ (rho beta : E → ℝ) (A : E → Mat2),
    ContDiffAt ℝ n rho x ∧ ContDiffAt ℝ n beta x ∧ ContDiffAt ℝ n A x ∧
      ∀ᶠ y in 𝓝 x, Represents (rho y) (beta y) (A y) (f y)

/-- Actual realized-spinor Ck regularity is equivalent to the independently defined local literal source representative condition. -/
theorem hasSmoothSourceRepresentativeAt_iff (n : WithTop ℕ∞)
    (f : E → SourcePolarQuotient.SourceQuotient) (x : E) :
    HasSmoothSourceRepresentativeAt n f x ↔
      ContDiffAt ℝ n (fun y => (SourcePolarQuotient.regularHomeomorph (f y)).val) x := by
  constructor
  · rintro ⟨rho, beta, A, hrho, hbeta, hA, hrep⟩
    have hx : Represents (rho x) (beta x) (A x) (f x) := hrep.self_of_nhds
    have hpoint := (represents_iff _ _ _ _).mp hx
    apply (PrincipalPolarChart.contDiffAt_polar_fields n hrho hbeta hA hpoint.1).congr_of_eventuallyEq
    filter_upwards [hrep] with y hy
    exact ((represents_iff _ _ _ _).mp hy).2.2
  · intro hpsi
    obtain ⟨beta, A, hrho, hbeta, hA, _, hrep⟩ :=
      LocalPolarFields.exists_local_polar_fields n hpsi
        (SourcePolarQuotient.regularHomeomorph (f x)).property
    refine ⟨fun y => invariantDensity (SourcePolarQuotient.regularHomeomorph (f y)).val,
      beta, A, hrho, hbeta, hA, ?_⟩
    filter_upwards [hrep] with y hy
    exact (represents_iff _ _ _ _).mpr hy

/-- The natural source quotient inverse of every actual Ck regular-spinor field has constructed local Ck real density, angle and determinant-one matrix representatives. -/
theorem hasSmoothSourceRepresentativeAt_inverse (n : WithTop ℕ∞)
    (psi : E → PolarSignQuotient.RegularSpinor) (x : E)
    (hpsi : ContDiffAt ℝ n (fun y => (psi y).val) x) :
    HasSmoothSourceRepresentativeAt n
      (fun y => SourcePolarQuotient.regularHomeomorph.symm (psi y)) x := by
  apply (hasSmoothSourceRepresentativeAt_iff n _ x).mpr
  simpa only [Homeomorph.apply_symm_apply] using hpsi

/-- The independent local source representative condition implies continuity in the already defined natural source quotient topology. -/
theorem hasSmoothSourceRepresentativeAt_continuousAt (n : WithTop ℕ∞)
    {f : E → SourcePolarQuotient.SourceQuotient} {x : E}
    (h : HasSmoothSourceRepresentativeAt n f x) : ContinuousAt f x := by
  have hc : ContinuousAt (fun y => SourcePolarQuotient.regularHomeomorph (f y)) x :=
    IsInducing.subtypeVal.continuousAt_iff.mpr
      ((hasSmoothSourceRepresentativeAt_iff n f x).mp h).continuousAt
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
    SourcePolarQuotient.regularHomeomorph.symm.continuous.continuousAt.comp hc

/-- On an open domain, local literal Ck source representatives at every point are equivalent to actual Ck smoothness of the realized spinor field. -/
theorem hasSmoothSourceRepresentativeAt_on_iff (n : WithTop ℕ∞)
    (f : E → SourcePolarQuotient.SourceQuotient) {U : Set E} (hU : IsOpen U) :
    (∀ x ∈ U, HasSmoothSourceRepresentativeAt n f x) ↔
      ContDiffOn ℝ n (fun y => (SourcePolarQuotient.regularHomeomorph (f y)).val) U := by
  constructor
  · intro h x hx
    exact ((hasSmoothSourceRepresentativeAt_iff n f x).mp (h x hx)).contDiffWithinAt
  · intro h x hx
    exact (hasSmoothSourceRepresentativeAt_iff n f x).mpr (h.contDiffAt (hU.mem_nhds hx))

/-- Literal representatives of the separated-density presentation use positive density and the actual four-pi angle-matrix sign class. -/
def ProductRepresents (rho beta : ℝ) (A : Mat2)
    (q : PositiveDensity × FrameQuotient) : Prop :=
  ∃ (hrho : 0 < rho) (hA : A.det = 1),
    ((⟨rho, hrho⟩ : PositiveDensity), Quotient.mk frameSetoid
      ((beta : Angle), (⟨A, hA⟩ : SpecialLinearMatrix))) = q

/-- Literal separated-density representatives coincide with full source quotient representatives under the independently proved density-product homeomorphism. -/
theorem productRepresents_iff (rho beta : ℝ) (A : Mat2)
    (q : PositiveDensity × FrameQuotient) :
    ProductRepresents rho beta A q ↔
      Represents rho beta A (densityProductHomeomorph.symm q) := by
  constructor
  · rintro ⟨hrho, hA, hq⟩
    refine ⟨hrho, hA, ?_⟩
    apply densityProductHomeomorph.injective
    rw [densityProductHomeomorph.apply_symm_apply, densityProductHomeomorph_mk]
    exact hq
  · rintro ⟨hrho, hA, hq⟩
    refine ⟨hrho, hA, ?_⟩
    have hh := congrArg densityProductHomeomorph hq
    simpa only [densityProductHomeomorph_mk, Homeomorph.apply_symm_apply] using hh

/-- Independent local regularity of the density product uses actual Ck real density and angle and matrix fields with literal product-class equality nearby. -/
def HasSmoothProductRepresentativeAt (n : WithTop ℕ∞)
    (f : E → PositiveDensity × FrameQuotient) (x : E) : Prop :=
  ∃ (rho beta : E → ℝ) (A : E → Mat2),
    ContDiffAt ℝ n rho x ∧ ContDiffAt ℝ n beta x ∧ ContDiffAt ℝ n A x ∧
      ∀ᶠ y in 𝓝 x, ProductRepresents (rho y) (beta y) (A y) (f y)

/-- The independent local representative conditions of the two literal source presentations agree through their actual density-product homeomorphism. -/
theorem hasSmoothProductRepresentativeAt_iff_source (n : WithTop ℕ∞)
    (f : E → PositiveDensity × FrameQuotient) (x : E) :
    HasSmoothProductRepresentativeAt n f x ↔
      HasSmoothSourceRepresentativeAt n (fun y => densityProductHomeomorph.symm (f y)) x := by
  simp only [HasSmoothProductRepresentativeAt, HasSmoothSourceRepresentativeAt, productRepresents_iff]

/-- Actual Ck regularity of the density-product spinor realization is equivalent to its independent literal local source representative condition. -/
theorem hasSmoothProductRepresentativeAt_iff (n : WithTop ℕ∞)
    (f : E → PositiveDensity × FrameQuotient) (x : E) :
    HasSmoothProductRepresentativeAt n f x ↔
      ContDiffAt ℝ n (fun y => (productRegularHomeomorph (f y)).val) x := by
  rw [hasSmoothProductRepresentativeAt_iff_source, hasSmoothSourceRepresentativeAt_iff]
  rfl

/-- The actual density-product inverse of a Ck regular-spinor field has local Ck real-angle and matrix representatives with positive density. -/
theorem hasSmoothProductRepresentativeAt_inverse (n : WithTop ℕ∞)
    (psi : E → PolarSignQuotient.RegularSpinor) (x : E)
    (hpsi : ContDiffAt ℝ n (fun y => (psi y).val) x) :
    HasSmoothProductRepresentativeAt n
      (fun y => productRegularHomeomorph.symm (psi y)) x := by
  apply (hasSmoothProductRepresentativeAt_iff n _ x).mpr
  simpa only [Homeomorph.apply_symm_apply] using hpsi

/-- Independent local product representatives imply continuity in the natural density and angle-matrix quotient product topology. -/
theorem hasSmoothProductRepresentativeAt_continuousAt (n : WithTop ℕ∞)
    {f : E → PositiveDensity × FrameQuotient} {x : E}
    (h : HasSmoothProductRepresentativeAt n f x) : ContinuousAt f x := by
  have hc : ContinuousAt (fun y => productRegularHomeomorph (f y)) x :=
    IsInducing.subtypeVal.continuousAt_iff.mpr
      ((hasSmoothProductRepresentativeAt_iff n f x).mp h).continuousAt
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
    productRegularHomeomorph.symm.continuous.continuousAt.comp hc

/-- On an open domain, the literal local Ck density-product representative condition is exactly actual Ck regularity of its realized spinor field. -/
theorem hasSmoothProductRepresentativeAt_on_iff (n : WithTop ℕ∞)
    (f : E → PositiveDensity × FrameQuotient) {U : Set E} (hU : IsOpen U) :
    (∀ x ∈ U, HasSmoothProductRepresentativeAt n f x) ↔
      ContDiffOn ℝ n (fun y => (productRegularHomeomorph (f y)).val) U := by
  constructor
  · intro h x hx
    exact ((hasSmoothProductRepresentativeAt_iff n f x).mp (h x hx)).contDiffWithinAt
  · intro h x hx
    exact (hasSmoothProductRepresentativeAt_iff n f x).mpr (h.contDiffAt (hU.mem_nhds hx))

end FoliationQM.SourcePolarSmooth
