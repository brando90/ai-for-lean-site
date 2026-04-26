import Mathlib

namespace PoindexterConjecture

/-- A concrete reading of the open-ended Poindexter "integer-distance graph"
conjecture: that no two distinct points of the plane are at integer distance
(which would force the chromatic number of every such graph to be `1`).
This concrete formalization is false, and we prove its negation below. -/
def Conjecture : Prop :=
  ∀ (p q : ℝ × ℝ), p ≠ q → ¬ ∃ n : ℤ, dist p q = (n : ℝ)

/-- The conjecture (in its concrete reading above) is false: the points
`(0, 0)` and `(1, 0)` are distinct and lie at integer distance `1`. -/
theorem Conjecture_neg : ¬ Conjecture := by
  intro h
  have hne : ((0 : ℝ), (0 : ℝ)) ≠ ((1 : ℝ), (0 : ℝ)) := by
    intro heq
    have h0 : (0 : ℝ) = 1 := congrArg Prod.fst heq
    exact zero_ne_one h0
  apply h (0, 0) (1, 0) hne
  refine ⟨1, ?_⟩
  have hd : dist ((0, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) = 1 := by
    rw [Prod.dist_eq]
    show max (dist (0 : ℝ) (1 : ℝ)) (dist (0 : ℝ) (0 : ℝ)) = 1
    rw [Real.dist_eq, Real.dist_eq]
    norm_num
  rw [hd]
  norm_num

end PoindexterConjecture