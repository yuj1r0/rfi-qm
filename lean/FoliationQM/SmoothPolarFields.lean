module
public import FoliationQM.SourceDatumManifold
public import FoliationQM.SourceQuotientManifold
public import FoliationQM.SmoothPolarCovering
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Smooth quotient-valued fields and anchored local representatives

Sources: the concrete fixed-representation smooth-field content of v13
`prop:takabayasi` and `eq:takabayasi_polar`. The actual source-quotient
regular-spinor diffeomorphism induces an equivalence of bundled smooth
fields from any supplied real charted base, at every differentiability
order. Its pointwise maps are exactly the earlier realization and inverse,
and each smooth regular-spinor field has a unique smooth quotient field.

Individual amplitude/matrix or literal density/four-pi-angle/matrix data
are provided locally through any prescribed point in the actual fiber.
The domains are explicit preimages of the source of an actual local
inverse of realization; they are open, contain the chosen base point,
and support the exact smoothness, anchor and realization identities.
These statements concern the concrete target fiber and maps into it.
They do not assert a global individual representative, a global real
angle, or an identification of arbitrary twisted spinor bundles.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Set Topology Function
namespace FoliationQM.SmoothPolarFields
open DiracMatrices PolarSignQuotient SourcePolarDatum SourcePolarRealization

section Fields
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual source-quotient diffeomorphism induces an equivalence between bundled smooth source-quotient fields and bundled smooth regular-spinor fields on any supplied real charted base. -/
def quotientFieldEquiv (n : WithTop ℕ∞) :
    C^n⟮I, M; 𝓘(ℝ, Spinor), SourcePolarQuotient.SourceQuotient⟯ ≃
      C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯ where
  toFun f := (SourceQuotientManifold.regularDiffeomorph n).toContMDiffMap.comp f
  invFun psi := (SourceQuotientManifold.regularDiffeomorph n).symm.toContMDiffMap.comp psi
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact (SourceQuotientManifold.regularDiffeomorph n).symm_apply_apply (f x)
  right_inv psi := by
    apply ContMDiffMap.ext
    intro x
    exact (SourceQuotientManifold.regularDiffeomorph n).apply_symm_apply (psi x)

/-- The forward bundled-field correspondence evaluates pointwise to the existing actual source-quotient realization. -/
theorem quotientFieldEquiv_apply (n : WithTop ℕ∞)
    (f : C^n⟮I, M; 𝓘(ℝ, Spinor), SourcePolarQuotient.SourceQuotient⟯) (x : M) :
    quotientFieldEquiv n f x = SourcePolarQuotient.regularHomeomorph (f x) := rfl

/-- The inverse bundled-field correspondence evaluates pointwise to the existing actual regular-spinor reconstruction in the quotient. -/
theorem quotientFieldEquiv_symm_apply (n : WithTop ℕ∞)
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) :
    (quotientFieldEquiv n).symm psi x =
      SourcePolarQuotient.regularHomeomorph.symm (psi x) := rfl

/-- Reconstruction after realization returns the original bundled smooth source-quotient field. -/
theorem quotientField_roundtrip (n : WithTop ℕ∞)
    (f : C^n⟮I, M; 𝓘(ℝ, Spinor), SourcePolarQuotient.SourceQuotient⟯) :
    (quotientFieldEquiv n).symm (quotientFieldEquiv n f) = f :=
  (quotientFieldEquiv n).symm_apply_apply f

/-- Realization after reconstruction returns the original bundled smooth regular-spinor field. -/
theorem regularField_roundtrip (n : WithTop ℕ∞)
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) :
    quotientFieldEquiv n ((quotientFieldEquiv n).symm psi) = psi :=
  (quotientFieldEquiv n).apply_symm_apply psi

/-- Every bundled smooth regular-spinor field has exactly one bundled smooth source-quotient field with the same actual pointwise realization. -/
theorem existsUnique_quotientField (n : WithTop ℕ∞)
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) :
    ∃! f : C^n⟮I, M; 𝓘(ℝ, Spinor), SourcePolarQuotient.SourceQuotient⟯,
      ∀ x, SourcePolarQuotient.regularHomeomorph (f x) = psi x := by
  refine ⟨(quotientFieldEquiv n).symm psi, ?_, ?_⟩
  · intro x
    exact SourcePolarQuotient.regularHomeomorph.apply_symm_apply (psi x)
  · intro f hf
    apply (quotientFieldEquiv n).injective
    apply ContMDiffMap.ext
    intro x
    exact (hf x).trans (congrArg (fun g => g x) (regularField_roundtrip n psi)).symm

end Fields

variable {X : Type*}

/-- The anchored datum-lift domain is the actual preimage of the source of the covering local inverse at the prescribed datum. -/
def datumLiftDomain (psi : X → RegularSpinor) (d : Datum) : Set X :=
  psi ⁻¹' (PolarSignCovering.realize_isLocalHomeomorph.localInverseAt d).source

/-- The anchored datum lift is the actual local inverse of realization composed with the supplied regular-spinor field. -/
def datumLift (psi : X → RegularSpinor) (d : Datum) : X → Datum :=
  (PolarSignCovering.realize_isLocalHomeomorph.localInverseAt d) ∘ psi

/-- A continuous regular-spinor field makes the explicit anchored datum-lift domain open. -/
theorem datumLiftDomain_isOpen [TopologicalSpace X]
    {psi : X → RegularSpinor} (hpsi : Continuous psi) (d : Datum) :
    IsOpen (datumLiftDomain psi d) :=
  (PolarSignCovering.realize_isLocalHomeomorph.localInverseAt d).open_source.preimage hpsi

/-- The base point belongs to the actual datum-lift domain whenever its spinor value is the realization of the prescribed datum. -/
theorem mem_datumLiftDomain {psi : X → RegularSpinor} {x : X} {d : Datum}
    (hx : psi x = realize d) : x ∈ datumLiftDomain psi d := by
  change psi x ∈ (PolarSignCovering.realize_isLocalHomeomorph.localInverseAt d).source
  rw [hx]
  exact PolarSignCovering.realize_isLocalHomeomorph.apply_self_mem_localInverseAt_source

/-- The actual local datum lift takes the prescribed value at the anchored base point. -/
theorem datumLift_at {psi : X → RegularSpinor} {x : X} {d : Datum}
    (hx : psi x = realize d) : datumLift psi d x = d := by
  change PolarSignCovering.realize_isLocalHomeomorph.localInverseAt d (psi x) = d
  rw [hx]
  exact PolarSignCovering.realize_isLocalHomeomorph.localInverseAt_apply_self

/-- On its explicit domain, the actual datum lift realizes exactly the supplied regular-spinor field. -/
theorem realize_datumLift {psi : X → RegularSpinor} {d : Datum} {x : X}
    (hx : x ∈ datumLiftDomain psi d) : realize (datumLift psi d x) = psi x :=
  PolarSignCovering.realize_isLocalHomeomorph.apply_localInverseAt_of_mem hx

/-- The literal source-lift domain is the datum-lift domain at the actual converted density-angle-matrix datum. -/
def sourceLiftDomain (psi : X → RegularSpinor) (a : SourceDatum) : Set X :=
  datumLiftDomain psi (toDatum a)

/-- The literal source lift converts the actual anchored datum lift back to positive density, four-pi angle and determinant-one matrix data. -/
def sourceLift (psi : X → RegularSpinor) (a : SourceDatum) : X → SourceDatum :=
  ofDatum ∘ datumLift psi (toDatum a)

/-- A continuous regular-spinor field makes the explicit literal source-lift domain open. -/
theorem sourceLiftDomain_isOpen [TopologicalSpace X]
    {psi : X → RegularSpinor} (hpsi : Continuous psi) (a : SourceDatum) :
    IsOpen (sourceLiftDomain psi a) := datumLiftDomain_isOpen hpsi (toDatum a)

/-- A prescribed literal source datum realizing the base value places the base point in the explicit source-lift domain. -/
theorem mem_sourceLiftDomain {psi : X → RegularSpinor} {x : X} {a : SourceDatum}
    (hx : psi x = realizeSource a) : x ∈ sourceLiftDomain psi a :=
  mem_datumLiftDomain hx

/-- The literal source lift agrees with the prescribed density-angle-matrix datum at the anchored base point. -/
theorem sourceLift_at {psi : X → RegularSpinor} {x : X} {a : SourceDatum}
    (hx : psi x = realizeSource a) : sourceLift psi a x = a := by
  change ofDatum (datumLift psi (toDatum a) x) = a
  rw [datumLift_at hx, ofDatum_toDatum]

/-- On the explicit source-lift domain, literal source realization of the lift is exactly the supplied regular-spinor field. -/
theorem realize_sourceLift {psi : X → RegularSpinor} {a : SourceDatum} {x : X}
    (hx : x ∈ sourceLiftDomain psi a) : realizeSource (sourceLift psi a x) = psi x := by
  change realize (toDatum (ofDatum (datumLift psi (toDatum a) x))) = psi x
  rw [toDatum_ofDatum]
  exact realize_datumLift hx

section SmoothLifts
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {psi : M → RegularSpinor}

/-- A manifold-smooth regular-spinor field has a manifold-smooth anchored datum lift on the actual preimage domain. -/
theorem contMDiffOn_datumLift (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi) (d : Datum) :
    ContMDiffOn I PolarDatumManifold.model n (datumLift psi d) (datumLiftDomain psi d) :=
  (SmoothPolarCovering.contMDiffOn_realize_localInverse n d).comp hpsi.contMDiffOn
    (fun _ hx => hx)

/-- A manifold-smooth regular-spinor field has a manifold-smooth literal source lift on the actual preimage domain. -/
theorem contMDiffOn_sourceLift (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi) (a : SourceDatum) :
    ContMDiffOn I SourceDatumManifold.model n (sourceLift psi a) (sourceLiftDomain psi a) :=
  (SourceDatumManifold.contMDiff_ofDatum n).comp_contMDiffOn (contMDiffOn_datumLift hpsi (toDatum a))

/-- The explicit datum lift has an open neighborhood domain, the prescribed anchor, full stated manifold smoothness and exact local realization. -/
theorem anchored_datum_lift (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi)
    (x : M) (d : Datum) (hx : psi x = realize d) :
    IsOpen (datumLiftDomain psi d) ∧ x ∈ datumLiftDomain psi d ∧
      ContMDiffOn I PolarDatumManifold.model n (datumLift psi d) (datumLiftDomain psi d) ∧
      datumLift psi d x = d ∧ ∀ y ∈ datumLiftDomain psi d, realize (datumLift psi d y) = psi y :=
  ⟨datumLiftDomain_isOpen hpsi.continuous d, mem_datumLiftDomain hx,
    contMDiffOn_datumLift hpsi d, datumLift_at hx, fun _ hy => realize_datumLift hy⟩

/-- The explicit literal source lift has an open neighborhood domain, the prescribed anchor, full stated manifold smoothness and exact local realization. -/
theorem anchored_source_lift (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi)
    (x : M) (a : SourceDatum) (hx : psi x = realizeSource a) :
    IsOpen (sourceLiftDomain psi a) ∧ x ∈ sourceLiftDomain psi a ∧
      ContMDiffOn I SourceDatumManifold.model n (sourceLift psi a) (sourceLiftDomain psi a) ∧
      sourceLift psi a x = a ∧
      ∀ y ∈ sourceLiftDomain psi a, realizeSource (sourceLift psi a y) = psi y :=
  ⟨sourceLiftDomain_isOpen hpsi.continuous a, mem_sourceLiftDomain hx,
    contMDiffOn_sourceLift hpsi a, sourceLift_at hx, fun _ hy => realize_sourceLift hy⟩

/-- Every bundled smooth regular-spinor field has an open local smooth individual datum lift through any prescribed point of its actual fiber. -/
theorem exists_smooth_local_datum_lift
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) (d : Datum)
    (hx : psi x = realize d) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → Datum,
      ContMDiffOn I PolarDatumManifold.model n g U ∧ g x = d ∧
        ∀ y ∈ U, realize (g y) = psi y := by
  obtain ⟨hU, hxU, hg, hd, hreal⟩ := anchored_datum_lift psi.contMDiff x d hx
  exact ⟨datumLiftDomain psi d, hU, hxU, datumLift psi d, hg, hd, hreal⟩

/-- Every bundled smooth regular-spinor field has an open local smooth literal source lift through any prescribed density-angle-matrix point of its actual fiber. -/
theorem exists_smooth_local_source_lift
    (psi : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) (a : SourceDatum)
    (hx : psi x = realizeSource a) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → SourceDatum,
      ContMDiffOn I SourceDatumManifold.model n g U ∧ g x = a ∧
        ∀ y ∈ U, realizeSource (g y) = psi y := by
  obtain ⟨hU, hxU, hg, ha, hreal⟩ := anchored_source_lift psi.contMDiff x a hx
  exact ⟨sourceLiftDomain psi a, hU, hxU, sourceLift psi a, hg, ha, hreal⟩

end SmoothLifts
end FoliationQM.SmoothPolarFields
