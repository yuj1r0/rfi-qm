module
public import FoliationQM.CliffordSpinPolarRealization
public import FoliationQM.SourcePolarCovering

/-!
# Smooth two-sheeted polar realization with genuine Clifford Spin data

Source scope: the regular polar reconstruction in v13 `prop:takabayasi`
and `eq:takabayasi_polar`. The source is the literal product of positive
density, the four-pi angle circle, and the actual generated Clifford Spin
group, with its previously specified topology and factor-product atlas.
Its proved source-coordinate homeomorphism and diffeomorphism transfer
the existing actual source realization covering and local inverses.

Every regular spinor has exactly two actual source representatives;
every point has an evenly covered neighborhood with discrete fiber Fin 2.
The realization is a local diffeomorphism to every order. Its genuine
smooth local inverses give exact anchored local representatives for every
smooth regular-spinor field on an arbitrary charted base. The local
inverse domain is explicit and the anchor may be any point in the fiber.
No global individual representative, global real angle, universal-cover
claim, Lorentz target atlas, or spacetime bundle identification is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Set Topology Function
namespace FoliationQM.CliffordSpinPolarCovering
open CliffordSpinPolarDatum CliffordSpinPolarRealization PolarSignQuotient DiracMatrices

/-- Actual density/four-pi-angle/Clifford-Spin realization is a covering in its existing natural product topology. -/
theorem realizeSource_isCoveringMap : IsCoveringMap realizeSource := by
  exact SourcePolarCovering.realizeSource_isCoveringMap.comp_homeomorph sourceHomeomorph

/-- Actual Clifford polar realization is a local homeomorphism at every source datum. -/
theorem realizeSource_isLocalHomeomorph : IsLocalHomeomorph realizeSource :=
  realizeSource_isCoveringMap.isLocalHomeomorph

/-- The actual source-coordinate homeomorphism identifies each genuine Clifford polar fiber with its corresponding concrete matrix polar fiber. -/
def realizeFiberHomeomorph (q : RegularSpinor) :
    (realizeSource ⁻¹' {q}) ≃ₜ (SourcePolarRealization.realizeSource ⁻¹' {q}) :=
  sourceHomeomorph.subtype (fun _ => Iff.rfl)

/-- Each genuine Clifford polar fiber is explicitly equivalent to Fin 2 through its actual matrix polar fiber. -/
def realizeFiberEquiv (q : RegularSpinor) : (realizeSource ⁻¹' {q}) ≃ Fin 2 :=
  (realizeFiberHomeomorph q).toEquiv.trans (SourcePolarCovering.realizeFiberEquiv q)

/-- Every regular spinor has exactly two positive-density/four-pi-angle/actual-Spin representatives. -/
theorem realize_fiber_card (q : RegularSpinor) : Nat.card (realizeSource ⁻¹' {q}) = 2 := by
  simpa using Nat.card_congr (realizeFiberEquiv q)

/-- Every regular spinor has an actual evenly covered neighborhood with the discrete two-point fiber Fin 2. -/
theorem realizeSource_isEvenlyCovered_two (q : RegularSpinor) :
    IsEvenlyCovered realizeSource q (Fin 2) := by
  let := (realizeSource_isCoveringMap q).discreteTopology_fiber
  exact (realizeSource_isCoveringMap q).of_fiber_homeomorph
    (realizeFiberEquiv q).toHomeomorphOfDiscrete

/-- Actual Clifford polar realization is a local diffeomorphism between the intrinsic product atlas and regular spinors to every order. -/
theorem realizeSource_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph sourceModel 𝓘(ℝ, Spinor) n realizeSource := by
  intro d
  have h := ((sourceDiffeomorph n).isLocalDiffeomorph d).comp
    𝓘(ℝ, Spinor) RegularSpinor
    (SourceDatumManifold.realizeSource_isLocalDiffeomorph n (sourceDiffeomorph n d))
  have heq : SourcePolarRealization.realizeSource ∘ sourceDiffeomorph n = realizeSource := by
    funext x
    rfl
  rw [heq] at h
  exact h

/-- Actual Clifford polar realization is smooth for the intrinsic density, angle, and Spin product atlas to every order. -/
theorem contMDiff_realizeSource (n : WithTop ℕ∞) :
    ContMDiff sourceModel 𝓘(ℝ, Spinor) n realizeSource :=
  (realizeSource_isLocalDiffeomorph n).contMDiff

/-- Genuine Clifford polar realization simultaneously has its natural covering property, all-order local smooth inverses, and exactly two points in every fiber. -/
theorem realizeSource_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap realizeSource ∧
      IsLocalDiffeomorph sourceModel 𝓘(ℝ, Spinor) n realizeSource ∧
      ∀ q : RegularSpinor, Nat.card (realizeSource ⁻¹' {q}) = 2 :=
  ⟨realizeSource_isCoveringMap, realizeSource_isLocalDiffeomorph n, realize_fiber_card⟩

/-- An actual smooth partial inverse to genuine Clifford polar realization through any prescribed source representative. -/
def localInverse (n : WithTop ℕ∞) (d : SourceDatum) :
    PartialDiffeomorph 𝓘(ℝ, Spinor) sourceModel RegularSpinor SourceDatum n :=
  (realizeSource_isLocalDiffeomorph n d).localInverse

/-- The realized spinor of the chosen source representative belongs to the genuine open local-inverse domain. -/
theorem realize_mem_localInverse_source (n : WithTop ℕ∞) (d : SourceDatum) :
    realizeSource d ∈ (localInverse n d).source :=
  (realizeSource_isLocalDiffeomorph n d).localInverse_mem_source

/-- The chosen actual smooth local inverse returns precisely its prescribed density, angle, and Clifford Spin representative. -/
theorem localInverse_realize (n : WithTop ℕ∞) (d : SourceDatum) :
    localInverse n d (realizeSource d) = d :=
  (realizeSource_isLocalDiffeomorph n d).localInverse_left_inv
    (realizeSource_isLocalDiffeomorph n d).localInverse_mem_target

/-- Every spinor in the actual open local-inverse domain is realized exactly by that inverse. -/
theorem realize_localInverse {n : WithTop ℕ∞} {d : SourceDatum} {q : RegularSpinor}
    (hq : q ∈ (localInverse n d).source) : realizeSource (localInverse n d q) = q :=
  (realizeSource_isLocalDiffeomorph n d).localInverse_right_inv hq

/-- The actual chosen Clifford polar inverse is smooth on its genuine open domain. -/
theorem contMDiffOn_localInverse (n : WithTop ℕ∞) (d : SourceDatum) :
    ContMDiffOn 𝓘(ℝ, Spinor) sourceModel n (localInverse n d) (localInverse n d).source :=
  (realizeSource_isLocalDiffeomorph n d).contMDiffOn_localInverse

/-- Every prescribed actual Clifford polar representative extends to a smooth local section near its regular spinor. -/
theorem exists_smooth_local_section (n : WithTop ℕ∞) (d : SourceDatum) :
    ∃ U : Set RegularSpinor, IsOpen U ∧ realizeSource d ∈ U ∧
      ∃ f : RegularSpinor → SourceDatum, ContMDiffOn 𝓘(ℝ, Spinor) sourceModel n f U ∧
        f (realizeSource d) = d ∧ ∀ q ∈ U, realizeSource (f q) = q := by
  refine ⟨(localInverse n d).source, (localInverse n d).open_source,
    realize_mem_localInverse_source n d, localInverse n d,
    contMDiffOn_localInverse n d, localInverse_realize n d, ?_⟩
  intro q hq
  exact realize_localInverse hq

variable {X : Type*}

/-- The actual anchored lift domain is the preimage of the smooth inverse's genuine open source. -/
def liftDomain (n : WithTop ℕ∞) (psi : X → RegularSpinor) (d : SourceDatum) : Set X :=
  psi ⁻¹' (localInverse n d).source

/-- The actual anchored lift composes the specified regular-spinor field with a genuine smooth Clifford polar inverse. -/
def lift (n : WithTop ℕ∞) (psi : X → RegularSpinor) (d : SourceDatum) : X → SourceDatum :=
  localInverse n d ∘ psi

/-- A continuous regular-spinor field makes the actual anchored Clifford polar lift domain open. -/
theorem liftDomain_isOpen [TopologicalSpace X] {psi : X → RegularSpinor}
    (hpsi : Continuous psi) (n : WithTop ℕ∞) (d : SourceDatum) :
    IsOpen (liftDomain n psi d) :=
  (localInverse n d).open_source.preimage hpsi

/-- A prescribed actual Clifford representative of the base spinor places that point in the anchored lift domain. -/
theorem mem_liftDomain {n : WithTop ℕ∞} {psi : X → RegularSpinor} {x : X} {d : SourceDatum}
    (hx : psi x = realizeSource d) : x ∈ liftDomain n psi d := by
  change psi x ∈ (localInverse n d).source
  rw [hx]
  exact realize_mem_localInverse_source n d

/-- The actual local field lift agrees with the prescribed Clifford polar representative at its anchor. -/
theorem lift_at {n : WithTop ℕ∞} {psi : X → RegularSpinor} {x : X} {d : SourceDatum}
    (hx : psi x = realizeSource d) : lift n psi d x = d := by
  change localInverse n d (psi x) = d
  rw [hx, localInverse_realize]

/-- On its actual domain, the anchored local Clifford polar lift realizes exactly the supplied regular-spinor field. -/
theorem realize_lift {n : WithTop ℕ∞} {psi : X → RegularSpinor} {d : SourceDatum} {x : X}
    (hx : x ∈ liftDomain n psi d) : realizeSource (lift n psi d x) = psi x :=
  realize_localInverse hx

section SmoothFields
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {psi : M → RegularSpinor}

/-- Every smooth regular-spinor field has a smooth actual Clifford polar lift on the explicit local inverse preimage domain. -/
theorem contMDiffOn_lift (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi) (d : SourceDatum) :
    ContMDiffOn I sourceModel n (lift n psi d) (liftDomain n psi d) :=
  (contMDiffOn_localInverse n d).comp hpsi.contMDiffOn (fun _ hx => hx)

/-- Any specified point in a regular-spinor field's actual Clifford polar fiber extends to an anchored smooth local lift with its exact open domain and realization. -/
theorem anchored_lift (hpsi : ContMDiff I 𝓘(ℝ, Spinor) n psi)
    (x : M) (d : SourceDatum) (hx : psi x = realizeSource d) :
    IsOpen (liftDomain n psi d) ∧ x ∈ liftDomain n psi d ∧
      ContMDiffOn I sourceModel n (lift n psi d) (liftDomain n psi d) ∧
      lift n psi d x = d ∧ ∀ y ∈ liftDomain n psi d, realizeSource (lift n psi d y) = psi y :=
  ⟨liftDomain_isOpen hpsi.continuous n d, mem_liftDomain hx,
    contMDiffOn_lift hpsi d, lift_at hx, fun _ hy => realize_lift hy⟩

end SmoothFields

/-- Two continuous actual Clifford polar lifts on a preconnected base coincide if their realized spinors and one anchor agree. -/
theorem continuous_lift_unique [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → SourceDatum} (hf : Continuous f) (hg : Continuous g)
    (he : realizeSource ∘ f = realizeSource ∘ g) (x : X) (hx : f x = g x) : f = g :=
  realizeSource_isCoveringMap.eq_of_comp_eq hf hg he x hx

end FoliationQM.CliffordSpinPolarCovering
