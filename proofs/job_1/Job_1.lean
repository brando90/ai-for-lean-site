import Mathlib

open EuclideanGeometry Real

/--
Pythagoras' theorem: for a Euclidean right triangle with vertices `A`, `B`, `C`
and right angle at `C`, the squares of the legs `AC` and `BC` sum to the square
of the hypotenuse `AB`.
-/
theorem pythagoras {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (A B C : P) (h : ∠ A C B = π / 2) :
    dist A C ^ 2 + dist B C ^ 2 = dist A B ^ 2 := by
  have key :=
    (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
      (p₁ := A) (p₂ := C) (p₃ := B)).mpr h
  linarith