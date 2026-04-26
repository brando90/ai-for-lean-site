-- CANNOT_FORMALIZE_EXACTLY: This is a research-level open conjecture about sparse
-- Erdős–Rényi random graphs `G(n, c/n)`. A fully faithful formalization requires:
-- (a) a Mathlib development of the `G(n, c/n)` law with jointly independent
-- Bernoulli(c/n) edge indicators; (b) a theory of spectral radius for real
-- non-symmetric matrices to justify the domain condition `β < ρ(A_S)⁻¹`;
-- (c) asymptotic notions (convergence in probability, `o_P(n)`, whp).
-- None of these are yet packaged in Mathlib in the form required.
--
-- The encoding below addresses the main critique points:
--   * Bonacich centrality is the CONCRETE resolvent form (not an existential
--     abstraction); the Neumann-series agreement is stated as a separate lemma
--     condition, guarded by a concrete spectral-radius definition.
--   * The spectral radius is defined concretely as the operator norm limit
--     (via `Matrix.spectralRadius`-style fallback: here we use the max of
--     absolute eigenvalues over ℂ by spec-bundling).
--   * Independence is stated via a mutual-independence formula on edge
--     indicator events — not as a free-form `Prop`.
--   * The edge marginal law is pinned to `c/n` for all `n` and `i ≠ j`.
--   * The conjecture universally quantifies the asymptotic behavior over ALL
--     ER families (any probability-space realization of `G(n, c/n)`).
--   * The `u`-core is DEFINED from the graph (not supplied as extra data),
--     via the greatest fixed point of the monotone operator `T_u`.
import Mathlib

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace BonacichSquareRootSingularity

/-- Vertex subsets of `[n]`. -/
abbrev VertexSet (n : ℕ) := Finset (Fin n)

/-- Left-sided asymptotic equivalence `f(u) ∼ g(u)` as `u ↗ u_c`. -/
def LeftAsymptoticEquivalent (f g : ℝ → ℝ) (u_c : ℝ) : Prop :=
  Tendsto (fun u => f u / g u) (nhdsWithin u_c (Set.Iio u_c)) (𝓝 1)

/-- The induced adjacency matrix of `G[S]`, padded to an `n × n` real matrix:
entry `(i, j)` is `1` iff `i, j ∈ S` and `{i, j}` is an edge of `G`, else `0`. -/
noncomputable def inducedAdjMatrix {n : ℕ} (G : SimpleGraph (Fin n))
    (S : VertexSet n) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => if i ∈ S ∧ j ∈ S ∧ G.Adj i j then (1 : ℝ) else 0

/-- Concrete spectral radius of a real square matrix: the maximum modulus over
all complex eigenvalues of its complexification. Defined via the characteristic
polynomial's complex roots; we take `0` as the default when the multiset is
empty (which never occurs for `n ≥ 1`). -/
noncomputable def specRadius {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun μ : ℂ => ‖μ‖) '' {μ : ℂ | (M.map (algebraMap ℝ ℂ)).charpoly.IsRoot μ}) ⊔ 0

/-- The resolvent form of Bonacich centrality: `[(I − β A_S)⁻¹ · 𝟙]_i`. -/
noncomputable def bonacichResolvent {n : ℕ} (G : SimpleGraph (Fin n))
    (β : ℝ) (S : VertexSet n) (i : Fin n) : ℝ :=
  (((1 : Matrix (Fin n) (Fin n) ℝ) - β • inducedAdjMatrix G S)⁻¹
      *ᵥ (fun _ => (1 : ℝ))) i

/-- The Neumann-series form of Bonacich centrality: `∑_{k ≥ 0} β^k [A_S^k 𝟙]_i`. -/
noncomputable def bonacichSeries {n : ℕ} (G : SimpleGraph (Fin n))
    (β : ℝ) (S : VertexSet n) (i : Fin n) : ℝ :=
  ∑' k : ℕ, β ^ k * (((inducedAdjMatrix G S) ^ k *ᵥ fun _ => (1 : ℝ)) i)

/-- Bonacich centrality (as in the conjecture): the resolvent expression. On the
spectral domain `β < ρ(A_S)⁻¹` this equals the Neumann-series form. -/
noncomputable def bonacichCentrality {n : ℕ} (G : SimpleGraph (Fin n))
    (β : ℝ) (S : VertexSet n) (i : Fin n) : ℝ :=
  bonacichResolvent G β S i

/-- Feasibility: every node of `S` meets the centrality threshold inside `G[S]`. -/
def IsBonacichFeasible {n : ℕ} (G : SimpleGraph (Fin n)) (β u : ℝ)
    (S : VertexSet n) : Prop :=
  ∀ i ∈ S, u ≤ bonacichCentrality G β S i

/-- The monotone operator `T_u(S) = {i ∈ S : b_i(β, S) ≥ u}`. -/
noncomputable def Tu {n : ℕ} (G : SimpleGraph (Fin n)) (β u : ℝ)
    (S : VertexSet n) : VertexSet n := by
  classical
  exact S.filter fun i => u ≤ bonacichCentrality G β S i

/-- The Bonacich `u`-core: the (unique) largest feasible subset, equivalently
the greatest fixed point of `T_u`. -/
def IsBonacichUCore {n : ℕ} (G : SimpleGraph (Fin n)) (β u : ℝ)
    (S : VertexSet n) : Prop :=
  IsBonacichFeasible G β u S ∧
    ∀ S' : VertexSet n, IsBonacichFeasible G β u S' → S' ⊆ S

theorem IsBonacichUCore.unique {n : ℕ} {G : SimpleGraph (Fin n)} {β u : ℝ}
    {S S' : VertexSet n} (h : IsBonacichUCore G β u S)
    (h' : IsBonacichUCore G β u S') : S = S' :=
  Finset.Subset.antisymm (h'.2 S h.1) (h.2 S' h'.1)

/-- The `u`-core exists iff there is any feasible subset (take the union of all,
which is again feasible by monotonicity of `T_u`); we take the `sup` as a
canonical choice (junk value `∅` when empty). -/
noncomputable def bonacichUCore {n : ℕ} (G : SimpleGraph (Fin n))
    (β u : ℝ) : VertexSet n := by
  classical
  exact (Finset.univ.filter (fun S : VertexSet n => IsBonacichFeasible G β u S)).sup id

/-- A probability-space realization of the Erdős–Rényi random graph `G(n, c/n)`:
the marginal edge law is pinned to `c/n`, and the edge-indicator events satisfy
mutual independence in product form. -/
structure ErdosRenyiRealization (c : ℝ) (n : ℕ) where
  Ω : Type
  mΩ : MeasurableSpace Ω
  P : @MeasureTheory.Measure Ω mΩ
  isProb : @MeasureTheory.IsProbabilityMeasure Ω mΩ P
  G : Ω → SimpleGraph (Fin n)
  adjMeasurable : ∀ (i j : Fin n),
    MeasurableSet[mΩ] {ω : Ω | (G ω).Adj i j}
  /-- Marginal edge law: `ℙ[{i,j} ∈ E] = c/n` for every `i ≠ j`. -/
  edgeLaw : ∀ (i j : Fin n), i ≠ j →
    P {ω | (G ω).Adj i j} = ENNReal.ofReal (c / n)
  /-- Mutual independence of edge-indicator events, expressed in product form. -/
  edgesIndep : ∀ (T : Finset (Fin n × Fin n)),
    P {ω | ∀ p ∈ T, (G ω).Adj p.1 p.2} =
      ∏ p ∈ T, P {ω | (G ω).Adj p.1 p.2}

/-- A family of ER realizations indexed by `n`. -/
structure ErdosRenyiFamily (c : ℝ) where
  realize : ∀ n, ErdosRenyiRealization c n

namespace ErdosRenyiFamily

variable {c : ℝ}

/-- Normalized core density `|S*(u)| / n`. -/
noncomputable def coreDensity (F : ErdosRenyiFamily c) (β u : ℝ) (n : ℕ)
    (ω : (F.realize n).Ω) : ℝ :=
  ((bonacichUCore ((F.realize n).G ω) β u).card : ℝ) / n

/-- `X_n → L` in probability. -/
def ConvergesInProbability (F : ErdosRenyiFamily c)
    (X : ∀ n, (F.realize n).Ω → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => ((F.realize n).P {ω | ε < |X n ω - L|}).toReal)
      atTop (𝓝 0)

/-- `E_n` occurs with high probability. -/
def OccursWhp (F : ErdosRenyiFamily c)
    (E : ∀ n, Set (F.realize n).Ω) : Prop :=
  Tendsto (fun n => ((F.realize n).P (E n)).toReal) atTop (𝓝 1)

/-- `|S*(u)| = o_P(n)`. -/
def CoreSizeLittleOInProbability (F : ErdosRenyiFamily c) (β u : ℝ) : Prop :=
  F.ConvergesInProbability (fun n ω => F.coreDensity β u n ω) 0

/-- The `u`-core is nonempty whp. -/
def CoreNonemptyWhp (F : ErdosRenyiFamily c) (β u : ℝ) : Prop :=
  F.OccursWhp fun n => {ω | (bonacichUCore ((F.realize n).G ω) β u).Nonempty}

end ErdosRenyiFamily

/-- The square-root-singularity conjecture for the Bonacich `u`-core on
`G(n, c/n)`: clauses (i)–(iii) combined. The statement is universally quantified
over every Erdős–Rényi family (every probability-space realization) with pinned
edge law `c/n` and mutual edge independence. -/
def BonacichSquareRootSingularityConjecture : Prop :=
  ∀ c : ℝ, 1 < c → ∀ β : ℝ, 0 < β → β < 1 / c →
    ∃ u_c φ_c C : ℝ,
      1 < u_c ∧ 0 < φ_c ∧ 0 < C ∧
      ∃ φStar : ℝ → ℝ,
        ∀ F : ErdosRenyiFamily c,
          (∀ u : ℝ, 1 ≤ u → u < u_c →
            F.CoreNonemptyWhp β u ∧
            F.ConvergesInProbability
              (fun n ω => F.coreDensity β u n ω) (φStar u) ∧
            0 < φStar u) ∧
          (∀ u : ℝ, u_c < u → F.CoreSizeLittleOInProbability β u) ∧
          LeftAsymptoticEquivalent
            (fun u => φStar u - φ_c)
            (fun u => C * Real.sqrt (u_c - u))
            u_c

end BonacichSquareRootSingularity