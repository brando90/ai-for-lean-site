import Mathlib

theorem riemannZeta_at_neg_one : riemannZeta (-1) = -1/12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  have hb : bernoulli 2 = 1/6 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
    exact bernoulli'_two
  simp only [Nat.cast_one, pow_one, Nat.reduceAdd] at h
  rw [h, hb]
  push_cast
  ring