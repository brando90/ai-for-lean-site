import Mathlib

theorem n_pow_five_sub_n_dvd_thirty (n : ℤ) : (30 : ℤ) ∣ n^5 - n := by
  have h : ∀ m : ZMod 30, m^5 - m = 0 := by decide
  have h2 : ((n^5 - n : ℤ) : ZMod 30) = 0 := by
    push_cast
    exact h _
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n^5 - n) 30).mp h2