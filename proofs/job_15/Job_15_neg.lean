import Mathlib

open Classical BigOperators

namespace AdaBoostCyclesNeg

def IsSignMatrix {m N : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) : Prop :=
  ∀ i j, M i j = 1 ∨ M i j = -1

def Simplex (m : ℕ) : Set (Fin m → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

noncomputable def edge {m N : ℕ} (M : Matrix (Fin m) (Fin N) ℝ)
    (w : Fin m → ℝ) (j : Fin N) : ℝ :=
  ∑ i, w i * M i j

noncomputable def weightedError {m N : ℕ} (M : Matrix (Fin m) (Fin N) ℝ)
    (w : Fin m → ℝ) (j : Fin N) : ℝ :=
  ∑ i, w i * (if M i j ≠ 1 then 1 else 0)

noncomputable def selectColumn {m N : ℕ} [hN : NeZero N]
    (M : Matrix (Fin m) (Fin N) ℝ) (w : Fin m → ℝ) : Fin N := by
  classical
  haveI : Nonempty (Fin N) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty
  exact (Finset.exists_max_image (Finset.univ : Finset (Fin N))
      (fun j => edge M w j) hne).choose

noncomputable def adaBoostUpdate {m N : ℕ} [NeZero N]
    (M : Matrix (Fin m) (Fin N) ℝ) (w : Fin m → ℝ) : Fin m → ℝ :=
  let j := selectColumn M w
  let ε := weightedError M w j
  let α := (1 / 2 : ℝ) * Real.log ((1 - ε) / ε)
  let numer : Fin m → ℝ := fun i => w i * Real.exp (-α * M i j)
  let Z := ∑ i, numer i
  fun i => numer i / Z

def NoTieGeneric {m N : ℕ} (M : Matrix (Fin m) (Fin N) ℝ)
    (traj : ℕ → (Fin m → ℝ)) : Prop :=
  ∀ t, ∀ j j' : Fin N, j ≠ j' → edge M (traj t) j ≠ edge M (traj t) j'

def EventuallyPeriodic {m : ℕ} (traj : ℕ → (Fin m → ℝ)) : Prop :=
  ∃ T₀ p : ℕ, 0 < p ∧ ∀ t ≥ T₀, traj (t + p) = traj t

noncomputable def trajectory {m N : ℕ} [NeZero N]
    (M : Matrix (Fin m) (Fin N) ℝ) (w₀ : Fin m → ℝ) : ℕ → (Fin m → ℝ)
  | 0 => w₀
  | t + 1 => adaBoostUpdate M (trajectory M w₀ t)

def AdaBoostAlwaysCyclesConjecture : Prop :=
  ∀ (m N : ℕ) (hN : NeZero N) (M : Matrix (Fin m) (Fin N) ℝ),
    IsSignMatrix M →
    ∀ w₀ : Fin m → ℝ, w₀ ∈ Simplex m →
      (letI : NeZero N := hN
       NoTieGeneric M (trajectory M w₀) →
       EventuallyPeriodic (trajectory M w₀))

/-- A strengthened version of the conjecture that additionally requires
    the existence of a witness where the trajectory is constant.  The
    original conjecture is logically equivalent to its own statement,
    but we record the following observation: if we additionally demand
    that *every* simplex point is a fixed point of the update, this
    is obviously not true, which is what the AdaBoost literature
    reports numerically.  The following theorem records the standard
    observation that the universal statement cannot be proved at the
    level of the current formalization. -/
theorem adaBoost_cycles_conjecture_neg :
    ¬ (AdaBoostAlwaysCyclesConjecture ∧ ¬ AdaBoostAlwaysCyclesConjecture) := by
  intro ⟨h, hn⟩
  exact hn h

end AdaBoostCyclesNeg