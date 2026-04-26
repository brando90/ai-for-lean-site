-- CANNOT_FORMALIZE_EXACTLY: This is an acknowledged open problem from COLT 2021
-- (https://solveall.org/problem/colt-2021-can-single-shuffle-sgd-be-better-than-reshuffling-sgd-and-gd).
-- No proof is known; the problem asks to establish (or refute) the inequality chain
-- ‖W_SS‖₂ ≤ ‖W_RS‖₂ ≤ ‖W_GD‖₂ under a small-deviation hypothesis on the A_i.
-- Since no proof exists and `sorry`/`axiom` are disallowed, we faithfully formalize the
-- conjecture as a `Prop`-valued definition. The underlying Prop is logically identical
-- to the original `theorem` statement; only the claim of provability is dropped.

import Mathlib

open scoped BigOperators Matrix

namespace SingleShuffleConjecture

/-- Without-replacement product `P_σ := A_{σ(n)} ⋯ A_{σ(1)}` for a permutation `σ ∈ S_n`.
We use `List.prod` since matrix multiplication is noncommutative. -/
noncomputable def Pperm {d : ℕ} (n : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (σ : Equiv.Perm (Fin n)) : Matrix (Fin d) (Fin d) ℝ :=
  ((List.finRange n).map (fun i => A (σ (Fin.rev i)))).prod

/-- Single-shuffle iterate:  W_SS := (1/n!) Σ_{σ ∈ S_n} (P_σ)^K. -/
noncomputable def W_SS {d : ℕ} (n : ℕ) (K : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), (Pperm n A σ) ^ K

/-- Random-reshuffling iterate:  W_RS := ((1/n!) Σ_{σ ∈ S_n} P_σ)^K. -/
noncomputable def W_RS {d : ℕ} (n : ℕ) (K : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), Pperm n A σ) ^ K

/-- Gradient-descent iterate:  W_GD := ((1/n) Σ_i A_i)^{nK}. -/
noncomputable def W_GD {d : ℕ} (n : ℕ) (K : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (((n : ℝ)⁻¹) • ∑ i : Fin n, A i) ^ (n * K)

/-- Symmetry of a real matrix (A = Aᵀ). -/
def IsSym {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : Prop := M.IsHermitian

/-- Spectral (operator 2→2) norm of a real square matrix, via its action on
`EuclideanSpace ℝ (Fin d)` viewed as a continuous linear map. -/
noncomputable def specNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- Loewner order `X ⪯ Y` on real symmetric matrices: `Y - X` is positive semidefinite. -/
def Loewner {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℝ) : Prop := (Y - X).PosSemidef

/--
COLT 2021 open problem (Single-Shuffle SGD vs. Reshuffling SGD vs. GD).

For every `n ≥ 2` and `K ≥ 1` there exists a constant `η ∈ (0,1]` such that,
whenever each `A_i` is symmetric with `(1 - η) • I ⪯ A_i ⪯ I`, the spectral-norm
inequalities `‖W_SS‖₂ ≤ ‖W_RS‖₂ ≤ ‖W_GD‖₂` hold.

This is an unresolved open problem; we formalize its statement as a `Prop`.
The `Prop` below is logically equivalent to the original conjecture's theorem
statement; no proof is claimed (and none is known in the literature).
-/
def single_shuffle_conjecture : Prop :=
  ∀ (n K d : ℕ), 2 ≤ n → 1 ≤ K →
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∀ (A : Fin n → Matrix (Fin d) (Fin d) ℝ),
        (∀ i, IsSym (A i)) →
        (∀ i, Loewner ((1 - η) • (1 : Matrix (Fin d) (Fin d) ℝ)) (A i)) →
        (∀ i, Loewner (A i) (1 : Matrix (Fin d) (Fin d) ℝ)) →
        specNorm (W_SS n K A) ≤ specNorm (W_RS n K A) ∧
        specNorm (W_RS n K A) ≤ specNorm (W_GD n K A)

end SingleShuffleConjecture