module
public import FoliationQM.GeometricLorentzFrameRecognition
public import FoliationQM.SignedMetricProjection
public import FoliationQM.LorentzGramSchmidt
public import FoliationQM.LorentzGramSchmidtBasis

/-!
# Signed normalization and actual geometric future Lorentz frames

Source scope: the metric-tetrad component of v13 `prop:takabayasi`.
The actual geometric future cone is identified through an independently
supplied pointwise Lorentz frame. Positive scalar multiplication preserves
that cone, so the positive signed normalization factor preserves the future
zeroth vector. The genuinely constructed Gram–Schmidt basis therefore gives
an actual oriented future Lorentz frame on its computed positive-pivot
domain, and fixes every already geometric frame. These are pointwise facts;
no smooth local frame, global metric normalization or Spin lift is assumed
or asserted here.
-/

@[expose] public section
noncomputable section
open Matrix Module
namespace FoliationQM.GeometricLorentzNormalization
open GeometricLorentzFrame GeometricLorentzFrameRecognition LorentzMatrixGroup
open SignedMetricProjection

/-- The explicit model Minkowski form scales bilinearly under arbitrary real scalar multiplication. -/
theorem minkowski_smul_smul (a b : ℝ) (v w : Covector) :
    minkowski (a • v) (b • w) = a * b * minkowski v w := by
  simp only [minkowski, Pi.smul_apply, smul_eq_mul]
  ring

/-- Positive real scaling preserves exactly the actual model future timelike cone, including both its temporal and metric inequalities. -/
theorem futureCone_smul_iff {a : ℝ} (ha : 0 < a) (v : Covector) :
    futureCone (a • v) ↔ futureCone v := by
  change (0 < a * v 0 ∧ 0 < minkowski (a • v) (a • v)) ↔ _
  rw [minkowski_smul_smul]
  exact and_congr (mul_pos_iff_of_pos_left ha)
    (mul_pos_iff_of_pos_left (mul_pos ha ha))

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {g : LinearMap.BilinForm ℝ V} {orientation : Orientation ℝ V (Fin 4)}
  {future : Set V} (e : Frame g orientation future)

include e

/-- Positive real scaling preserves exactly the specified geometric future cone in the original vector space. -/
theorem mem_future_smul_iff {a : ℝ} (ha : 0 < a) (v : V) :
    a • v ∈ future ↔ v ∈ future := by
  rw [mem_future_iff_coordinates e, mem_future_iff_coordinates e, map_smul]
  exact futureCone_smul_iff ha _

/-- Signed normalization preserves geometric future membership when its actual signed metric square is positive. -/
theorem normalize_mem_future_iff {ε : ℝ} {v : V} (hv : 0 < ε * g v v) :
    normalize g ε v ∈ future ↔ v ∈ future :=
  mem_future_smul_iff e (scale_pos g hv) v

/-- The zeroth vector of an actual geometric Lorentz frame belongs to its specified future cone. -/
theorem basis_zero_mem_future : e.basis 0 ∈ future := by
  rw [mem_future_iff_coordinates e]
  simp [futureCone, minkowski]

/-- The explicit four-step normalization preserves exactly future membership of the original zeroth seed on its genuine positive-pivot domain. -/
theorem gramSchmidt_zero_future_iff (s : Fin 4 → V) (h : LorentzGramSchmidt.Good g s) :
    LorentzGramSchmidt.frame g s 0 ∈ future ↔ s 0 ∈ future :=
  normalize_mem_future_iff e h.1

variable (seed : Basis (Fin 4) ℝ V) (h : LorentzGramSchmidt.Good g seed)
  (ho : seed.orientation = orientation) (hf : seed 0 ∈ future)

/-- The explicit Gram–Schmidt algorithm constructs an actual geometric Lorentz frame from an oriented seed basis with future zeroth vector on the computed positive-pivot domain; full cone compatibility is derived. -/
def normalizedFrame : Frame g orientation future :=
  GeometricLorentzFrameRecognition.ofBasis e
    (LorentzGramSchmidtBasis.normalizedBasis g seed (metric_symm e) h)
    (LorentzGramSchmidtBasis.normalizedBasis_gram g seed (metric_symm e) h)
    ((LorentzGramSchmidtBasis.orientation g seed (metric_symm e) h).trans ho)
    (by
      rw [LorentzGramSchmidtBasis.normalizedBasis_apply]
      exact (gramSchmidt_zero_future_iff e seed h).mpr hf)

/-- The geometric normalized frame has precisely the four actually computed Gram–Schmidt vectors. -/
theorem normalizedFrame_vectors (i : Fin 4) :
    (normalizedFrame e seed h ho hf).basis i = LorentzGramSchmidt.frame g seed i :=
  LorentzGramSchmidtBasis.normalizedBasis_apply g seed (metric_symm e) h i

/-- When the seed already has eta Gram matrix, the constructed geometric frame retains its original actual basis. -/
theorem normalizedFrame_basis_of_gram
    (hs : ∀ i j : Fin 4, g (seed i) (seed j) = eta i j) :
    (normalizedFrame e seed (LorentzGramSchmidt.good_of_gram g seed hs) ho hf).basis = seed := by
  apply DFunLike.ext
  intro i
  rw [normalizedFrame_vectors, LorentzGramSchmidt.frame_eq_of_gram g seed hs]

/-- Actual geometric Lorentz frames are exact fixed points of the full signed normalization and geometric recognition construction. -/
theorem normalizedFrame_at :
    normalizedFrame e e.basis
      (LorentzGramSchmidt.good_of_gram g e.basis (metric_basis e))
      e.oriented (basis_zero_mem_future e) = e := by
  apply frame_ext
  exact normalizedFrame_basis_of_gram e e.basis e.oriented
    (basis_zero_mem_future e) (metric_basis e)

end FoliationQM.GeometricLorentzNormalization
