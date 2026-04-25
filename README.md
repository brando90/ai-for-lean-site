# Conjecture Prover

Submit a mathematical conjecture in plain language and receive a machine-verified [Lean 4](https://lean-lang.org/) proof.

**Live site:** https://brando90.github.io/conjecture-prover/

> **Note:** The pipeline details below reflect the system as of April 2026 and may become outdated as the prover evolves. The live site and email results are always authoritative.

## What it does

An automated pipeline takes your conjecture and attempts to:

- **Prove** it with a formal Lean 4 + [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) proof (you get the `.lean` file, LaTeX paper, and PDF)
- **Disprove** it with a formal counterexample or negation proof
- **Analyze** it with numerical experiments if the conjecture remains open

You receive results by email regardless of outcome.

## Pipeline overview

```
                         +-----------+
                         |   Your    |
                         |conjecture |
                         +-----+-----+
                               |
                               v
                      +--------+--------+
                      |  NL proof sketch|
                      |  (natural lang) |
                      +--------+--------+
                               |
                               v
                    +----------+----------+
                    | Multi-model debate  |
                    | (cross-critique &   |
                    |  synthesize best)   |
                    +----------+----------+
                               |
                               v
                   +-----------+-----------+
                   | Lean 4 formalization  |
                   | (with Mathlib)        |
                   +-----------+-----------+
                               |
                               v
                    +----------+----------+
                    |  Verify & repair    |
                    |  (up to N attempts) |
                    +----------+----------+
                               |
                     +---------+---------+
                     |                   |
                     v                   v
            +--------+------+   +-------+--------+
            |   Semantic    |   |   Negation     |
            |   alignment   |   |   guard        |
            |   check       |   |   (anti-       |
            |               |   |    strawman)   |
            +--------+------+   +-------+--------+
                     |                   |
                     +---------+---------+
                               |
                               v
                    +----------+----------+
                    |  Results emailed    |
                    |  (.lean, .tex, PDF) |
                    +---------------------+
```

## How to submit

Two options — both feed the same prover:

1. **Website form** (recommended): https://brando90.github.io/conjecture-prover/
2. **Google Form** (legacy, still active): https://forms.gle/8admh8evFKrmnbw49

The website form submits via [FormSubmit](https://formsubmit.co/) and is scraped into the pipeline database. The Google Form feeds a Google Sheet that the pipeline also reads from. Both paths are deduplicated, so submitting to both won't create duplicate jobs.

You can use plain text, LaTeX notation, or a mix. The more precise your statement, the better the result.

## Built by

[Brando Miranda](https://brando90.github.io)

Questions? Email brando.science@gmail.com
