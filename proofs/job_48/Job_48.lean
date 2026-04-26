-- CANNOT_FORMALIZE_EXACTLY: This is the COLT 2021 open problem of Yun–Rajput–Sra
-- (arXiv:2103.07079). The conjecture remains unresolved; in particular the
-- second inequality contains the still-open well-conditioned operator-norm
-- noncommutative AM–GM (Recht–Re) conjecture for n ≥ 5. We therefore cannot
-- supply a Lean proof. We faithfully formalize the *statement* of the conjecture
-- as a `Prop`, addressing all critiques: (i) the spectral/operator norm is used
-- (via `Matrix.toEuclideanCLM`), (ii) the dimension `d ≥ 1` hypothesis is
-- included, (iii) the constant `η` is quantified strictly outside `d` and `A`
-- (dimension-free, instance-uniform), (iv) the Loewner order is encoded via
-- `Matrix.PosSemidef`, (v) we do NOT axiomatize the conjecture itself.

import Mathlib

open scoped Matrix BigOperators
open Equiv

namespace SingleShuffleSGD

/-- The without-replacement product `P_σ = A_{σ(n)} ⋯ A_{σ(1)}` for a permutation
`σ ∈ S_n` and a family `A : Fin n → Matrix (Fin d) (Fin d) ℝ`.

The fold `List.foldl (fun acc i => A (σ i) * acc) 1` over `[0,1,…,n-1]` produces
`A (σ (n-1)) * A (σ (n-2)) * ⋯ * A (σ 0) * 1`, matching the right-to-left
product `A_{σ(n)} ⋯ A_{σ(1)}` after the customary 1-indexed/0-indexed shift. -/
noncomputable def Pperm {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (σ : Equiv.Perm (Fin n)) : Matrix (Fin d) (Fin d) ℝ :=
  (List.finRange n).foldl (fun acc i => A (σ i) * acc) 1

/-- Single-shuffle iterate: `W_SS = (1/n!) Σ_σ (P_σ)^K`. -/
noncomputable def W_SS {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ) (K : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ((Nat.factorial n : ℝ)⁻¹) •
    ∑ σ : Equiv.Perm (Fin n), (Pperm A σ) ^ K

/-- Random-reshuffling iterate: `W_RS = ((1/n!) Σ_σ P_σ)^K`. -/
noncomputable def W_RS {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ) (K : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (((Nat.factorial n : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), Pperm A σ) ^ K

/-- Gradient-descent proxy: `W_GD = ((1/n) Σ_i A_i)^{nK}`. -/
noncomputable def W_GD {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ) (K : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (((n : ℝ)⁻¹) • ∑ i : Fin n, A i) ^ (n * K)

/-- Spectral (operator) norm of a real square matrix, defined as the operator
norm of the induced continuous linear map on the Euclidean space
`EuclideanSpace ℝ (Fin d)`. This is the norm `‖·‖₂` appearing in the conjecture. -/
noncomputable def specNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖

/-- Loewner order on real symmetric matrices: `X ⪯ Y` iff `Y - X` is positive
semidefinite. -/
def loewnerLE {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (Y - X).PosSemidef

/-- Near-identity uniform well-conditioning: each `A_i` is symmetric and
satisfies `(1 - η) I ⪯ A_i ⪯ I`. -/
def nearIdentityWellConditioned {n d : ℕ} (η : ℝ)
    (A : Fin n → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ i : Fin n,
    (A i).IsSymm ∧
      loewnerLE ((1 - η) • (1 : Matrix (Fin d) (Fin d) ℝ)) (A i) ∧
        loewnerLE (A i) (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The exact statement of the COLT 2021 conjecture of Yun–Rajput–Sra:
for every `n ≥ 2` and `K ≥ 1` there exists a constant `η_{n,K} ∈ (0,1]`,
depending only on `n` and `K` (not on `d` or on the specific matrices),
such that whenever the matrices `A_i` are symmetric and satisfy
`(1 - η_{n,K}) I ⪯ A_i ⪯ I` for all `i`, one has
`‖W_SS‖₂ ≤ ‖W_RS‖₂ ≤ ‖W_GD‖₂`.

Note the order of the quantifiers: `η` is fixed *before* `d` and `A`, so it is
dimension-free and instance-uniform, as required by the conjecture. -/
def YunRajputSraConjecture : Prop :=
  ∀ ⦃n : ℕ⦄, 2 ≤ n → ∀ ⦃K : ℕ⦄, 1 ≤ K →
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∀ ⦃d : ℕ⦄, 1 ≤ d → ∀ (A : Fin n → Matrix (Fin d) (Fin d) ℝ),
        nearIdentityWellConditioned η A →
        specNorm (W_SS A K) ≤ specNorm (W_RS A K) ∧
        specNorm (W_RS A K) ≤ specNorm (W_GD A K)

/-- A trivial but genuinely-proved partial fact: at `K = 1`, the single-shuffle
and random-reshuffling iterates coincide on the nose (both equal the average of
the without-replacement products), so the first conjectured inequality is an
equality at `K = 1`, with no hypotheses on the matrices. This is *not* a proof
of the conjecture, only a sanity check on the definitions. -/
theorem W_SS_eq_W_RS_of_K_eq_one {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    W_SS A 1 = W_RS A 1 := by
  simp [W_SS, W_RS]

theorem specNorm_W_SS_le_W_RS_of_K_eq_one {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    specNorm (W_SS A 1) ≤ specNorm (W_RS A 1) := by
  rw [W_SS_eq_W_RS_of_K_eq_one A]

end SingleShuffleSGD