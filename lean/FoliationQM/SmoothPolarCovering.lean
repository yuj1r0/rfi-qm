module
public import FoliationQM.PolarDatumManifold
public import FoliationQM.PolarQuotientManifold
public import FoliationQM.ContinuousPolarLiftSmooth
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Homeomorph.Lemmas
/-!
# The actual smooth two-sheeted polar covering

Sources: the concrete quotient and regular reconstruction in v13
`prop:takabayasi` and `eq:takabayasi_polar`. The natural datum manifold
uses its independent complex-amplitude and intrinsic determinant-one
matrix coordinates. The natural quotient and regular-spinor manifolds
retain their previously verified realization atlases and topologies.

The genuine topological local inverses of realization are smooth to
every order. In an actual regular-spinor chart, their realized spinor
values agree locally with the identity, and the already proved theorem
for continuous polar lifts supplies actual coordinate regularity.
Together with forward smoothness, this constructs genuine local
diffeomorphisms, rather than asserting only smoothness of a topological
covering. Composition with the existing regular-spinor diffeomorphism
proves the same result for the actual sign-quotient projection.

The established covering maps and exact two-point fibers are retained.
The natural quotient is also Hausdorff and second-countable by its
actual homeomorphism with regular spinors. No global representative,
abstract Spin-group identification, or Spin-to-Lorentz covering is
asserted; differential invertibility is not needed for these proofs.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Set Filter Topology
namespace FoliationQM.SmoothPolarCovering
open DiracMatrices PolarSignQuotient PolarSignCovering RegularPolarHomeomorph

/-- The existing natural sign quotient is Hausdorff through its actual regular-spinor homeomorphism. -/
instance instT2SpacePolarQuotient : T2Space PolarQuotient :=
  regularHomeomorph.isEmbedding.t2Space

/-- The existing natural sign quotient is second-countable through its actual regular-spinor homeomorphism. -/
instance instSecondCountableTopologyPolarQuotient : SecondCountableTopology PolarQuotient :=
  regularHomeomorph.secondCountableTopology

private theorem coordinateContDiffAt_localInverse_chart (n : WithTop ℕ∞) (d : Datum)
    (q : RegularSpinor) (hq : q ∈ (realize_isLocalHomeomorph.localInverseAt d).source) :
    PolarDatumSmooth.CoordinateContDiffAt n
      ((realize_isLocalHomeomorph.localInverseAt d) ∘
        (extChartAt 𝓘(ℝ, Spinor) q).symm) (extChartAt 𝓘(ℝ, Spinor) q q) := by
  let e := realize_isLocalHomeomorph.localInverseAt d
  let C := extChartAt 𝓘(ℝ, Spinor) q
  have hC : C.symm (C q) = q := extChartAt_to_inv q
  have hc : ContinuousAt C.symm (C q) := continuousAt_extChartAt_symm q
  have he : ContinuousAt e q := e.continuousOn.continuousAt (e.open_source.mem_nhds hq)
  have hcomp : ContinuousAt (e ∘ C.symm) (C q) := by
    apply he.comp_of_eq hc
    exact hC
  apply ContinuousPolarLiftSmooth.coordinateContDiffAt_of_continuousAt n hcomp
  have hnear : ∀ᶠ z in 𝓝 (C q), C.symm z ∈ e.source :=
    hc.tendsto.eventually (hC.symm ▸ e.open_source.mem_nhds hq)
  have heq : (fun z => (realize (e (C.symm z))).val) =ᶠ[𝓝 (C q)] id := by
    filter_upwards [hnear, extChartAt_target_mem_nhds (I := 𝓘(ℝ, Spinor)) q] with z hz ht
    rw [realize_isLocalHomeomorph.apply_localInverseAt_of_mem hz]
    change C (C.symm z) = z
    exact C.right_inv ht
  exact contDiffAt_id.congr_of_eventuallyEq heq

/-- Every genuine topological local inverse of realization is smooth to every order on its actual open source for the intrinsic datum manifold. -/
theorem contMDiffOn_realize_localInverse (n : WithTop ℕ∞) (d : Datum) :
    ContMDiffOn 𝓘(ℝ, Spinor) PolarDatumManifold.model n
      (realize_isLocalHomeomorph.localInverseAt d)
      (realize_isLocalHomeomorph.localInverseAt d).source := by
  intro q hq
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_source.mpr
  have h := PolarDatumManifold.contMDiffAt_iff_coordinateContDiffAt.mpr
    (coordinateContDiffAt_localInverse_chart n d q hq)
  simpa only [modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ] using h

/-- The actual datum realization is a genuine local diffeomorphism to every order, with smooth inverses derived from their actual local realization identities. -/
theorem realize_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph PolarDatumManifold.model 𝓘(ℝ, Spinor) n realize := by
  intro d
  let e := realize_isLocalHomeomorph.localInverseAt d
  let p : PartialDiffeomorph PolarDatumManifold.model 𝓘(ℝ, Spinor) Datum RegularSpinor n := {
    toPartialEquiv := e.symm.toPartialEquiv
    open_source := e.open_target
    open_target := e.open_source
    contMDiffOn_toFun := by
      change ContMDiffOn PolarDatumManifold.model 𝓘(ℝ, Spinor) n
        (e.symm : Datum → RegularSpinor) e.target
      rw [show (e.symm : Datum → RegularSpinor) = realize from
        realize_isLocalHomeomorph.localInverseAt_symm d]
      exact (PolarDatumManifold.contMDiff_realize n).contMDiffOn
    contMDiffOn_invFun := contMDiffOn_realize_localInverse n d }
  have hp : IsLocalDiffeomorphAt PolarDatumManifold.model 𝓘(ℝ, Spinor) n
      (p : Datum → RegularSpinor) d :=
    p.isLocalDiffeomorphAt PolarDatumManifold.model 𝓘(ℝ, Spinor) n
      (realize_isLocalHomeomorph.self_mem_localInverseAt_target (x := d))
  have heq : (p : Datum → RegularSpinor) = realize :=
    realize_isLocalHomeomorph.localInverseAt_symm d
  rw [heq] at hp
  exact hp

/-- The actual sign-quotient projection is a local diffeomorphism to every order for the independently verified datum and quotient manifolds. -/
theorem quotient_mk_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph PolarDatumManifold.model 𝓘(ℝ, Spinor) n
      (Quotient.mk signSetoid : Datum → PolarQuotient) := by
  have heq : (PolarQuotientManifold.regularDiffeomorph n).symm ∘ realize =
      (Quotient.mk signSetoid : Datum → PolarQuotient) := by
    funext d
    exact ofRegular_toRegular (Quotient.mk signSetoid d)
  intro d
  simpa only [heq] using (realize_isLocalDiffeomorph n d).comp
    𝓘(ℝ, Spinor) PolarQuotient
    ((PolarQuotientManifold.regularDiffeomorph n).symm.isLocalDiffeomorph (realize d))

/-- The actual natural sign-quotient projection is manifold-smooth to every order. -/
theorem contMDiff_quotient_mk (n : WithTop ℕ∞) :
    ContMDiff PolarDatumManifold.model 𝓘(ℝ, Spinor) n
      (Quotient.mk signSetoid : Datum → PolarQuotient) :=
  (quotient_mk_isLocalDiffeomorph n).contMDiff

/-- Actual realization simultaneously retains its genuine covering-map property, is a local diffeomorphism to the stated order, and has exactly two points in every fiber. -/
theorem realize_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap realize ∧
      IsLocalDiffeomorph PolarDatumManifold.model 𝓘(ℝ, Spinor) n realize ∧
      ∀ q : RegularSpinor, Nat.card (realize ⁻¹' {q}) = 2 :=
  ⟨realize_isCoveringMap, realize_isLocalDiffeomorph n, realize_fiber_card⟩

/-- The actual sign projection simultaneously retains its genuine covering-map property, is a local diffeomorphism to the stated order, and has exactly two points in every fiber. -/
theorem quotient_mk_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap (Quotient.mk signSetoid : Datum → PolarQuotient) ∧
      IsLocalDiffeomorph PolarDatumManifold.model 𝓘(ℝ, Spinor) n
        (Quotient.mk signSetoid : Datum → PolarQuotient) ∧
      ∀ q : PolarQuotient,
        Nat.card ((Quotient.mk signSetoid : Datum → PolarQuotient) ⁻¹' {q}) = 2 :=
  ⟨quotient_mk_isCoveringMap, quotient_mk_isLocalDiffeomorph n, quotient_fiber_card⟩

end FoliationQM.SmoothPolarCovering
