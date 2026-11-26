module
public import FoliationQM.IntrinsicPathGauge

/-!
# Comparing path presentations on the same open domains

For the geometric part of v13 `prop:takabayasi`, principal transitions
have total representatives whose values on a true overlap are intrinsic.
This comparison uses only those values, so two actual atlases can be
compared after restricting to common domains and constructing chart gauges.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntrinsicAtlasComparison
open PathTransitionData BasedPathGroup IntrinsicPathGauge GlobalIntrinsicPathObstruction

variable {G B ι : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace B] [LocallyPathConnectedSpace B]
  {D E : Data G B ι}
  (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))

/-- Agreement of actual transitions on their true overlaps gives equality of
the global classes computed from independently chosen joint path families. -/
theorem obstruction_eqOn (P : Family D) (Q : Family E) (hd : D.domain = E.domain)
    (ht : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      D.transition i j x = E.transition i j x) : obstruction e P = obstruction e Q := by
  obtain ⟨U, hU, t, hc, hi, hm⟩ := D
  obtain ⟨V, hV, s, kc, ki, km⟩ := E
  change U = V at hd
  subst V
  let Q' : Family (Data.mk U hU t hc hi hm) :=
    { homotopy := Q.homotopy
      source := Q.source
      target := fun i j x => (Q.target i j x).trans (ht i j x x.property.1 x.property.2).symm
      diagonal := Q.diagonal }
  exact (independent e P Q').trans (show obstruction e Q' = obstruction e Q from rfl)

/-- A gauge relation solely on true pairs, with actual joint paths for its
chart gauges, suffices to compare two families on the same domains. -/
theorem obstruction_of_gaugePaths (P : Family D) (Q : Family E) (A : Gauge D)
    (H : GaugePaths A) (hd : D.domain = E.domain)
    (ht : ∀ i j x, x ∈ D.domain i → x ∈ D.domain j →
      A.value j x * D.transition i j x * (A.value i x)⁻¹ = E.transition i j x) :
    obstruction e P = obstruction e Q :=
  (obstruction_gauged e P H).symm.trans
    (obstruction_eqOn e (gaugedFamily P H) Q hd ht)

end FoliationQM.IntrinsicAtlasComparison
