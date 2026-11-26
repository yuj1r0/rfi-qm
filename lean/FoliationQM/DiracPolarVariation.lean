module
public import FoliationQM.CliffordSpinPolarReconstruction
public import FoliationQM.DiracInteriorVariation

/-!
# Admissible families in the physical Clifford polar quotient

For v13 `prop:takabayasi` and `thm:dirac_lift`, these compact variations
use the quotient manifold and its own smoothness predicate. The
spacetime domain can be any open set. The field outside the common
compact carrier stays fixed throughout the parameter neighborhood.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff Manifold
namespace FoliationQM.DiracPolarVariation
open CliffordSpinPolarQuotient CliffordSpinPolarReconstruction

/-- A compact interior variation of an actual quotient field. -/
structure PolarVariation (U : Set Covector) (q : Covector → SourceQuotient) where
  family : ℝ × Covector → SourceQuotient
  params : Set ℝ
  params_open : IsOpen params
  zero_mem : 0 ∈ params
  carrier : Set Covector
  compact : IsCompact carrier
  interior : carrier ⊆ U
  initial : ∀ x, family (0, x) = q x
  smooth : ∀ t ∈ params, ∀ x ∈ U, ContMDiffAt 𝓘(ℝ, ℝ × Covector) model ∞ family (t, x)
  fixed : ∀ t ∈ params, ∀ x ∉ carrier, family (t, x) = q x

variable {U : Set Covector} {q : Covector → SourceQuotient}

/-- Fixing the real parameter gives the physical polar field at that parameter. -/
def slice (P : PolarVariation U q) (t : ℝ) (x : Covector) : SourceQuotient := P.family (t, x)

/-- The zero slice is the original polar field everywhere. -/
theorem slice_zero (P : PolarVariation U q) : slice P 0 = q := funext P.initial

/-- Every admissible slice is smooth at each point of the spacetime domain. -/
theorem smooth_slice (P : PolarVariation U q) {t : ℝ} (ht : t ∈ P.params)
    {x : Covector} (hx : x ∈ U) : ContMDiffAt 𝓘(ℝ, Covector) model ∞ (slice P t) x :=
  (P.smooth t ht x hx).comp x (contMDiffAt_iff_contDiffAt.mpr
    (contDiffAt_const.prodMk contDiffAt_id))

/-- Existence of an admissible variation implies smoothness of its background on the domain. -/
theorem smooth_background (P : PolarVariation U q) {x : Covector} (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℝ, Covector) model ∞ q x :=
  (slice_zero P) ▸ smooth_slice P P.zero_mem hx

/-- A locally smooth polar field admits a stationary-in-parameter test with empty carrier. -/
def constantVariation (hq : ∀ x ∈ U, ContMDiffAt 𝓘(ℝ, Covector) model ∞ q x) :
    PolarVariation U q where
  family y := q y.2
  params := Set.univ
  params_open := isOpen_univ
  zero_mem := Set.mem_univ _
  carrier := ∅
  compact := isCompact_empty
  interior := Set.empty_subset _
  initial _ := rfl
  smooth t _ x hx := (hq x hx).comp (t,x) (contMDiffAt_iff_contDiffAt.mpr contDiffAt_snd)
  fixed _ _ _ _ := rfl

/-- The independent manifold family predicate is inhabited exactly on locally smooth backgrounds. -/
theorem nonempty_iff_smooth : Nonempty (PolarVariation U q) ↔
    ∀ x ∈ U, ContMDiffAt 𝓘(ℝ, Covector) model ∞ q x :=
  ⟨fun ⟨P⟩ _ hx => smooth_background P hx, fun hq => ⟨constantVariation hq⟩⟩

end FoliationQM.DiracPolarVariation
