module
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# An intrinsic homotopy for conjugating a based loop by a based path

For the geometric frame obstruction associated with v13 `prop:takabayasi`,
this is a topological-group statement independent of Clifford or Spin data.
Moving the conjugating path parameter from zero to its actual time gives
an explicit homotopy relative to both loop endpoints. It is the geometric
reason that the endpoint kernel of the intrinsic path group is central.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.PathConjugationHomotopy

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Conjugating a based loop pointwise by an identity-based path is homotopic
to the original loop through the actual formula `g(s*t) * l(t) * g(s*t)⁻¹`. -/
def homotopy (g l : C(unitInterval, G)) (hg : g 0 = 1)
    (hl₀ : l 0 = 1) (hl₁ : l 1 = 1) : l.HomotopyRel (g * l * g⁻¹) {0, 1} where
  toFun z := g (z.1 * z.2) * l z.2 * (g (z.1 * z.2))⁻¹
  continuous_toFun := by
    have ht : Continuous (fun z : unitInterval × unitInterval => z.1 * z.2) :=
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    exact ((g.continuous.comp ht).mul (l.continuous.comp continuous_snd)).mul
      (g.continuous.comp ht).inv
  map_zero_left t := by simp [hg]
  map_one_left t := by simp
  prop' s t ht := by
    rcases ht with ht | ht
    · subst t
      simp [hl₀, hg]
    · rw [Set.mem_singleton_iff] at ht
      subst t
      simp [hl₁]

/-- Every value of the homotopy is the displayed actual group conjugation. -/
theorem homotopy_apply (g l : C(unitInterval, G)) (hg : g 0 = 1)
    (hl₀ : l 0 = 1) (hl₁ : l 1 = 1) (s t : unitInterval) :
    homotopy g l hg hl₀ hl₁ (s, t) = g (s * t) * l t * (g (s * t))⁻¹ := rfl

/-- Pointwise conjugation by any identity-based path preserves the relative-endpoint homotopy class of a loop. -/
theorem homotopicRel (g l : C(unitInterval, G)) (hg : g 0 = 1)
    (hl₀ : l 0 = 1) (hl₁ : l 1 = 1) : l.HomotopicRel (g * l * g⁻¹) {0, 1} :=
  ⟨homotopy g l hg hl₀ hl₁⟩

end FoliationQM.PathConjugationHomotopy
