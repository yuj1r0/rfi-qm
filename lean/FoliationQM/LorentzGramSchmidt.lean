module
public import FoliationQM.SignedMetricProjection
public import FoliationQM.LorentzMatrixGroup

/-!
# Explicit four-step Lorentz Gram–Schmidt algebra

Source scope: the actual geometric tetrad construction underlying v13
`prop:takabayasi`. The algorithm below performs one positive and three
negative signed normalizations, removing the earlier directions in their
actual order. Its domain consists only of four strict signed-square
inequalities. For a symmetric original bilinear metric these inequalities
imply the exact (+---) Gram matrix; no output orthogonality is assumed.

An independently eta-normalized seed is fixed at every raw and normalized
stage and lies in the genuine domain. The vector space is arbitrary: no
spanning, full basis, orientation, or smoothness is inferred here. Those
require separate premises and constructions.
-/

@[expose] public section
noncomputable section
open Matrix
namespace FoliationQM.LorentzGramSchmidt
open SignedMetricProjection LorentzMatrixGroup RealLorentzFrame

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (g : LinearMap.BilinForm ℝ V) (s : Fin 4 → V)

/-- The first raw vector is the originally supplied zeroth seed vector. -/
def u0 (_g : LinearMap.BilinForm ℝ V) (s : Fin 4 → V) : V := s 0

/-- The first actual output vector is the positive signed normalization of the zeroth seed. -/
def e0 : V := SignedMetricProjection.normalize g 1 (u0 g s)

/-- The first negative raw vector removes the actual positive direction from the first seed. -/
def u1 : V := SignedMetricProjection.residual g 1 (e0 g s) (s 1)

/-- The first negative output is the actual negative signed normalization of its residual. -/
def e1 : V := SignedMetricProjection.normalize g (-1) (u1 g s)

/-- The second negative raw vector successively removes the actual positive direction and first negative direction. -/
def u2 : V := SignedMetricProjection.residual g (-1) (e1 g s) (SignedMetricProjection.residual g 1 (e0 g s) (s 2))

/-- The second negative output is the actual negative signed normalization of the twice-projected seed. -/
def e2 : V := SignedMetricProjection.normalize g (-1) (u2 g s)

/-- The third negative raw vector successively removes all three previously constructed actual directions. -/
def u3 : V := SignedMetricProjection.residual g (-1) (e2 g s)
  (SignedMetricProjection.residual g (-1) (e1 g s) (SignedMetricProjection.residual g 1 (e0 g s) (s 3)))

/-- The last output vector is the actual negative signed normalization of the final residual. -/
def e3 : V := SignedMetricProjection.normalize g (-1) (u3 g s)

/-- The four ordered actual output vectors, with the original time-first (+---) convention. -/
def frame : Fin 4 → V := ![e0 g s, e1 g s, e2 g s, e3 g s]

/-- The actual algebraic domain: precisely the four strict signed-square inequalities needed by the explicit normalizations. -/
def Good : Prop :=
  0 < (1 : ℝ) * g (u0 g s) (u0 g s) ∧
  0 < (-1 : ℝ) * g (u1 g s) (u1 g s) ∧
  0 < (-1 : ℝ) * g (u2 g s) (u2 g s) ∧
  0 < (-1 : ℝ) * g (u3 g s) (u3 g s)

/-- The four actual diagonal normalization factors; these are computed from the metric residuals rather than supplied as positive parameters. -/
def factor : Fin 4 → ℝ :=
  ![scale g 1 (u0 g s), scale g (-1) (u1 g s),
    scale g (-1) (u2 g s), scale g (-1) (u3 g s)]

/-- Every actual normalization factor is strictly positive on the genuine four-step domain. -/
theorem factor_pos (h : Good g s) (i : Fin 4) : 0 < factor g s i := by
  fin_cases i
  · exact scale_pos g h.1
  · exact scale_pos g h.2.1
  · exact scale_pos g h.2.2.1
  · exact scale_pos g h.2.2.2

/-- None of the actual normalization factors vanishes on the genuine algorithm domain. -/
theorem factor_ne_zero (h : Good g s) (i : Fin 4) : factor g s i ≠ 0 :=
  ne_of_gt (factor_pos g s h i)

/-- The explicit four-step algorithm has exact Gram matrix (+---) on its actual positive-denominator domain, derived solely from symmetry and the supplied bilinear metric. -/
theorem gram (hg : g.IsSymm) (h : Good g s) (i j : Fin 4) :
    g (frame g s i) (frame g s j) = eta i j := by
  have hp : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hn : (-1 : ℝ) ^ 2 = 1 := by norm_num
  have h00 : g (e0 g s) (e0 g s) = 1 := metric_normalize g hp h.1
  have h11 : g (e1 g s) (e1 g s) = -1 := metric_normalize g hn h.2.1
  have h22 : g (e2 g s) (e2 g s) = -1 := metric_normalize g hn h.2.2.1
  have h33 : g (e3 g s) (e3 g s) = -1 := metric_normalize g hn h.2.2.2
  have h01 : g (e0 g s) (e1 g s) = 0 :=
    normalize_orthogonal_right g (-1) (e0 g s) (u1 g s)
      (metric_residual g hp h00 (s 1))
  have h02raw : g (e0 g s) (u2 g s) = 0 :=
    residual_orthogonal_left g (-1) (e1 g s) (SignedMetricProjection.residual g 1 (e0 g s) (s 2))
      (e0 g s) (metric_residual g hp h00 (s 2)) h01
  have h02 : g (e0 g s) (e2 g s) = 0 :=
    normalize_orthogonal_right g (-1) (e0 g s) (u2 g s) h02raw
  have h12 : g (e1 g s) (e2 g s) = 0 :=
    normalize_orthogonal_right g (-1) (e1 g s) (u2 g s)
      (metric_residual g hn h11 (SignedMetricProjection.residual g 1 (e0 g s) (s 2)))
  have h03raw : g (e0 g s) (u3 g s) = 0 :=
    residual_orthogonal_left g (-1) (e2 g s)
      (SignedMetricProjection.residual g (-1) (e1 g s) (SignedMetricProjection.residual g 1 (e0 g s) (s 3))) (e0 g s)
      (residual_orthogonal_left g (-1) (e1 g s) (SignedMetricProjection.residual g 1 (e0 g s) (s 3))
        (e0 g s) (metric_residual g hp h00 (s 3)) h01) h02
  have h03 : g (e0 g s) (e3 g s) = 0 :=
    normalize_orthogonal_right g (-1) (e0 g s) (u3 g s) h03raw
  have h13raw : g (e1 g s) (u3 g s) = 0 :=
    residual_orthogonal_left g (-1) (e2 g s)
      (SignedMetricProjection.residual g (-1) (e1 g s) (SignedMetricProjection.residual g 1 (e0 g s) (s 3))) (e1 g s)
      (metric_residual g hn h11 (SignedMetricProjection.residual g 1 (e0 g s) (s 3))) h12
  have h13 : g (e1 g s) (e3 g s) = 0 :=
    normalize_orthogonal_right g (-1) (e1 g s) (u3 g s) h13raw
  have h23 : g (e2 g s) (e3 g s) = 0 :=
    normalize_orthogonal_right g (-1) (e2 g s) (u3 g s)
      (metric_residual g hn h22
        (SignedMetricProjection.residual g (-1) (e1 g s) (SignedMetricProjection.residual g 1 (e0 g s) (s 3))))
  have h10 : g (e1 g s) (e0 g s) = 0 := (hg.eq _ _).trans h01
  have h20 : g (e2 g s) (e0 g s) = 0 := (hg.eq _ _).trans h02
  have h30 : g (e3 g s) (e0 g s) = 0 := (hg.eq _ _).trans h03
  have h21 : g (e2 g s) (e1 g s) = 0 := (hg.eq _ _).trans h12
  have h31 : g (e3 g s) (e1 g s) = 0 := (hg.eq _ _).trans h13
  have h32 : g (e3 g s) (e2 g s) = 0 := (hg.eq _ _).trans h23
  fin_cases i <;> fin_cases j <;>
    simp [frame, eta, sign, h00, h11, h22, h33, h01, h02, h03, h12, h13, h23,
      h10, h20, h30, h21, h31, h32]

/-- Every raw and normalized stage is fixed by an independently eta-normalized seed; this conclusion uses no symmetry or basis hypothesis beyond the stated pairings. -/
theorem stages_eq_of_gram (hs : ∀ i j : Fin 4, g (s i) (s j) = eta i j) :
    u0 g s = s 0 ∧ e0 g s = s 0 ∧ u1 g s = s 1 ∧ e1 g s = s 1 ∧
      u2 g s = s 2 ∧ e2 g s = s 2 ∧ u3 g s = s 3 ∧ e3 g s = s 3 := by
  have hp : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hn : (-1 : ℝ) ^ 2 = 1 := by norm_num
  have h00 : g (s 0) (s 0) = 1 := by simpa [eta, sign] using hs 0 0
  have h11 : g (s 1) (s 1) = -1 := by simpa [eta, sign] using hs 1 1
  have h22 : g (s 2) (s 2) = -1 := by simpa [eta, sign] using hs 2 2
  have h33 : g (s 3) (s 3) = -1 := by simpa [eta, sign] using hs 3 3
  have h01 : g (s 0) (s 1) = 0 := by simpa [eta] using hs 0 1
  have h02 : g (s 0) (s 2) = 0 := by simpa [eta] using hs 0 2
  have h03 : g (s 0) (s 3) = 0 := by simpa [eta] using hs 0 3
  have h12 : g (s 1) (s 2) = 0 := by simpa [eta] using hs 1 2
  have h13 : g (s 1) (s 3) = 0 := by simpa [eta] using hs 1 3
  have h23 : g (s 2) (s 3) = 0 := by simpa [eta] using hs 2 3
  have he0 : e0 g s = s 0 := normalize_of_metric g hp h00
  have hu1 : u1 g s = s 1 := by
    rw [u1, he0, residual_of_orthogonal g 1 _ _ h01]
  have he1 : e1 g s = s 1 := by
    rw [e1, hu1, normalize_of_metric g hn h11]
  have hu2 : u2 g s = s 2 := by
    rw [u2, he0, he1, residual_of_orthogonal g 1 _ _ h02,
      residual_of_orthogonal g (-1) _ _ h12]
  have he2 : e2 g s = s 2 := by
    rw [e2, hu2, normalize_of_metric g hn h22]
  have hu3 : u3 g s = s 3 := by
    rw [u3, he0, he1, he2, residual_of_orthogonal g 1 _ _ h03,
      residual_of_orthogonal g (-1) _ _ h13, residual_of_orthogonal g (-1) _ _ h23]
  have he3 : e3 g s = s 3 := by
    rw [e3, hu3, normalize_of_metric g hn h33]
  exact ⟨rfl, he0, hu1, he1, hu2, he2, hu3, he3⟩

/-- An independently eta-normalized seed lies in the genuine four strict signed-square domains of the actual algorithm. -/
theorem good_of_gram (hs : ∀ i j : Fin 4, g (s i) (s j) = eta i j) : Good g s := by
  obtain ⟨hu0, _, hu1, _, hu2, _, hu3, _⟩ := stages_eq_of_gram g s hs
  simp only [Good, hu0, hu1, hu2, hu3, hs]
  norm_num [eta, sign]

/-- The entire actual ordered frame is unchanged when the input already has the source eta Gram matrix. -/
theorem frame_eq_of_gram (hs : ∀ i j : Fin 4, g (s i) (s j) = eta i j) : frame g s = s := by
  obtain ⟨_, he0, _, he1, _, he2, _, he3⟩ := stages_eq_of_gram g s hs
  funext i
  fin_cases i <;> simp [frame, he0, he1, he2, he3]

/-- Every actual normalization factor equals one at an independently eta-normalized seed. -/
theorem factor_eq_one_of_gram (hs : ∀ i j : Fin 4, g (s i) (s j) = eta i j)
    (i : Fin 4) : factor g s i = 1 := by
  obtain ⟨hu0, _, hu1, _, hu2, _, hu3, _⟩ := stages_eq_of_gram g s hs
  fin_cases i <;> simp [factor, hu0, hu1, hu2, hu3, scale, hs, eta, sign]

end FoliationQM.LorentzGramSchmidt
