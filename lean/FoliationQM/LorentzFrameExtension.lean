module
public import FoliationQM.FrameSquareExtension
public import FoliationQM.LorentzTriangleMonodromy

/-!
# Spin monodromy detects local Lorentz frame filling

For the geometric Spin-frame component of v13 `prop:takabayasi`, a frame
field over a specified continuous base square fills its prescribed
boundary exactly when its Lorentz loop coefficient is zero. The entire
square must lie in the stated original bundle chart. The filling takes
values in the original frame total space; it is a continuous section of
the pulled-back bundle, not a claimed smooth filling or a section on the
image of a possibly noninjective square. These are local extension tests,
not a global cellular characteristic-class construction.
-/

@[expose] public section
noncomputable section
open scoped Topology
namespace FoliationQM.LorentzFrameExtension
open LorentzMatrixGroup CliffordSpinLoopMonodromy LorentzFundamentalGroup
open FrameSquareExtension

/-- The normalized mod-two homotopy coefficient of an actual based Lorentz loop. -/
def coefficient (γ : Path (1 : ProperFutureLorentz) 1) : ZMod 2 :=
  Multiplicative.toAdd (fundamentalGroupEquiv (loopClass γ))

/-- This coefficient is zero precisely for a nullhomotopic based Lorentz loop. -/
theorem coefficient_zero_iff (γ : Path (1 : ProperFutureLorentz) 1) :
    coefficient γ = 0 ↔ γ.Homotopic (Path.refl 1) := by
  change fundamentalGroupEquiv (loopClass γ) = 1 ↔ _
  rw [fundamentalGroupEquiv.map_eq_one_iff, loopClass_eq_one_iff]

/-- The genuine projected unit-to-negative-unit Spin path has nonzero coefficient. -/
theorem coefficient_generator : coefficient generatorLoop = 1 :=
  congrArg Multiplicative.toAdd generatorLoop_class

/-- For the actual concatenated triangle this is exactly the coefficient used in the transition cocycle. -/
theorem coefficient_triangle {a b c : ProperFutureLorentz}
    (p : Path (1 : ProperFutureLorentz) a) (q : Path (1 : ProperFutureLorentz) b)
    (r : Path (1 : ProperFutureLorentz) c) (h : b * a = c) :
    coefficient (LorentzTriangleMonodromy.triangle p q r h) =
      LorentzTriangleMonodromy.coefficient p q r h := rfl

variable {B P ι : Type*} [TopologicalSpace B] [TopologicalSpace P] {proj : P → B}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι) (i : ι)
  (σ : C(unitInterval × unitInterval, B))

/-- A genuine frame filling exists exactly when the actual Spin lift of its boundary loop closes. -/
theorem nonempty_iff_lift_closes (γ : Path (1 : ProperFutureLorentz) 1)
    (hσ : ∀ z, σ z ∈ (A.triv i).baseSet) :
    Nonempty (Filling A i σ γ) ↔ liftLoop γ 1 = 1 :=
  (FrameSquareExtension.nonempty_iff A i σ γ hσ).trans
    (loop_nullhomotopic_iff_lift_closes γ)

/-- Existence of a filling in the original Lorentz frame space is detected by zero of the independently defined loop coefficient. -/
theorem nonempty_iff_coefficient_zero (γ : Path (1 : ProperFutureLorentz) 1)
    (hσ : ∀ z, σ z ∈ (A.triv i).baseSet) :
    Nonempty (Filling A i σ γ) ↔ coefficient γ = 0 :=
  (FrameSquareExtension.nonempty_iff A i σ γ hσ).trans (coefficient_zero_iff γ).symm

/-- The constant boundary loop admits an actual continuous filling over every contained base square. -/
theorem refl_filling (hσ : ∀ z, σ z ∈ (A.triv i).baseSet) :
    Nonempty (Filling A i σ (Path.refl 1)) :=
  ⟨FrameSquareExtension.ofHomotopy A i σ (Path.refl 1) hσ (Path.Homotopy.refl _)⟩

/-- The actual nontrivial Lorentz generator cannot be filled over any such base square. -/
theorem generator_no_filling (hσ : ∀ z, σ z ∈ (A.triv i).baseSet) :
    ¬ Nonempty (Filling A i σ generatorLoop) :=
  fun h => generatorLoop_not_nullhomotopic ((FrameSquareExtension.nonempty_iff A i σ _ hσ).mp h)

/-- Traversing any based Lorentz boundary twice admits an actual frame filling. -/
theorem doubled_filling (γ : Path (1 : ProperFutureLorentz) 1)
    (hσ : ∀ z, σ z ∈ (A.triv i).baseSet) :
    Nonempty (Filling A i σ (γ.trans γ)) :=
  (FrameSquareExtension.nonempty_iff A i σ _ hσ).mpr (doubled_loop_nullhomotopic γ)

/-- The actual triangular transition boundary fills exactly when its monodromy coefficient is zero. -/
theorem triangle_nonempty_iff {a b c : ProperFutureLorentz}
    (p : Path (1 : ProperFutureLorentz) a) (q : Path (1 : ProperFutureLorentz) b)
    (r : Path (1 : ProperFutureLorentz) c) (h : b * a = c)
    (hσ : ∀ z, σ z ∈ (A.triv i).baseSet) :
    Nonempty (Filling A i σ (LorentzTriangleMonodromy.triangle p q r h)) ↔
      LorentzTriangleMonodromy.coefficient p q r h = 0 :=
  nonempty_iff_coefficient_zero A i σ _ hσ

/-- Equivalently, the triangular boundary fills precisely when the actual ordered Spin endpoint defect is the identity. -/
theorem triangle_nonempty_iff_defect {a b c : ProperFutureLorentz}
    (p : Path (1 : ProperFutureLorentz) a) (q : Path (1 : ProperFutureLorentz) b)
    (r : Path (1 : ProperFutureLorentz) c) (h : b * a = c)
    (hσ : ∀ z, σ z ∈ (A.triv i).baseSet) :
    Nonempty (Filling A i σ (LorentzTriangleMonodromy.triangle p q r h)) ↔
      (LorentzTriangleMonodromy.defect p q r h).val = 1 := by
  rw [nonempty_iff_lift_closes A i σ _ hσ, LorentzTriangleMonodromy.triangle_lift_endpoint]

end FoliationQM.LorentzFrameExtension
