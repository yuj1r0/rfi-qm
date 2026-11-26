module
public import FoliationQM.GeometricSpinObstruction
public import FoliationQM.SpinLiftHOneTorsor

/-!
# Isomorphisms of geometric Spin lifts over a fixed Lorentz map

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
The comparison is a diffeomorphism of total spaces commuting with their
actual Spin actions and physical projections. Adapted principal charts
extract genuine transition lifts of the specified Lorentz data.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinLiftIsomorphism
open CliffordSpinMap CliffordSpinLorentzSmooth LorentzMatrixGroup

section Physical
variable {E V H J Q T P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace J]
  [TopologicalSpace Q] [ChartedSpace H Q] [TopologicalSpace T] [ChartedSpace J T]

/-- A diffeomorphism intertwining the actual principal Spin actions and both physical maps to the same Lorentz space. -/
structure PhysicalIso (K : ModelWithCorners ℝ E H) (K' : ModelWithCorners ℝ V J)
    (n : WithTop ℕ∞) (F : Q → P) (G : T → P) (r : Q → Spin → Q) (s : T → Spin → T) where
  /-- The smooth equivalence of the original source total spaces. -/
  diffeo : Q ≃ₘ^n⟮K, K'⟯ T
  /-- It preserves the principal right Spin action. -/
  equivariant : ∀ q g, diffeo (r q g) = s (diffeo q) g
  /-- It commutes with the two physical Spin-to-Lorentz maps. -/
  over : ∀ q, G (diffeo q) = F q

end Physical

universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] {proj : P → B}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι} {n : WithTop ℕ∞}

/-- Physical isomorphisms between two genuine lifts adapted to the same specified Lorentz atlas. -/
abbrev Between (A T : GeometricSpinStructure.Lift I L n) :=
  PhysicalIso (I.prod spinModel) (I.prod spinModel) n A.map T.map A.atlas.right T.atlas.right

/-- Commutation with the physical Lorentz maps implies that the diffeomorphism preserves the original base point. -/
theorem base_eq {A T : GeometricSpinStructure.Lift I L n} (e : Between A T) (q : A.Carrier) :
    T.proj (e.diffeo q) = A.proj q := by
  rw [← T.map.proj, e.over, A.map.proj]

variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- The adapted Spin atlas yields normalized, genuine lifts of the actual target transitions on their exact domains. -/
def transitions (A : GeometricSpinStructure.Lift I L n) :
    SpinLiftSignDifference.Lift (AdaptedGeometricSpinLift.lorentzData LM) :=
  SpinLiftSignDifference.ofSpinData (AdaptedGeometricSpinLift.spinData A.smoothAtlas)
    (A.adapted.extracted_domain_eq A.smoothAtlas LM) A.adapted.transition_projection

/-- The extracted representative is exactly the coordinate of the first canonical Spin section in the second Spin chart. -/
theorem transitions_apply (A : GeometricSpinStructure.Lift I L n) (i j : ι) (x : B) :
    (transitions LM A).transition i j x = A.atlas.transition i j x := rfl

variable [IsManifold I n B]

/-- A genuine lift of the extracted Lorentz transitions gives an adapted geometric Spin structure on the original target. -/
def realize (S : SpinLiftSignDifference.Lift (AdaptedGeometricSpinLift.lorentzData LM)) :
    GeometricSpinStructure.Lift I L n :=
  GeometricSpinStructure.ofCompatible LM (S := SpinLiftSignDifference.spinData S)
    { domain_eq := rfl, transition := S.projection }

/-- Extracting the realized geometric structure recovers the supplied Spin transition on each actual overlap. -/
theorem transitions_realize (S : SpinLiftSignDifference.Lift (AdaptedGeometricSpinLift.lorentzData LM)) :
    SpinLiftOverlapTorsor.Agree (transitions LM (realize LM S)) S := by
  intro i j x hi hj
  exact PrincipalCocycleBundle.geometricData_transition
    (CliffordSpinPrincipalBundle.spinData (SpinLiftSignDifference.spinData S)) i j x hi hj

end FoliationQM.SpinLiftIsomorphism
