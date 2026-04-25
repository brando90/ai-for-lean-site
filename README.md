# Conjecture Prover

Submit a mathematical conjecture in plain language and receive a machine-verified [Lean 4](https://lean-lang.org/) proof.

**Live site:** https://brando90.github.io/conjecture-prover/

## What it does

An automated pipeline takes your conjecture and attempts to:

- **Prove** it with a formal Lean 4 + Mathlib proof (you get the `.lean` file, LaTeX paper, and PDF)
- **Disprove** it with a formal counterexample or negation proof
- **Analyze** it with numerical experiments if the conjecture remains open

You receive results by email regardless of outcome.

## How the pipeline works

```
Your conjecture
  → NL proof sketch
  → Multi-model debate
  → Lean 4 formalization
  → Verification & repair (up to 5 attempts)
  → Semantic alignment check
  → Negation guard
  → Results emailed to you
```

## Submit

Visit https://brando90.github.io/conjecture-prover/ and fill out the form. You can use plain text, LaTeX notation, or a mix.

## Built by

[Brando Miranda](https://brando90.github.io) at Stanford University.

Questions? Email brando.science@gmail.com
