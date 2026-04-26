/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h1
  change True → False at h1
  apply h1
  trivial

example : False → ¬True := by
  intro h1
  change True → False
  intro h2
  assumption

example : ¬False → True := by
  intro h1
  trivial

example : True → ¬False := by
  intro h1
  change False → False
  intro h2
  assumption

example : False → ¬P := by
  intro h1
  exfalso
  assumption

example : P → ¬P → False := by
  intro h1 h2
  change P→ False at h2
  apply h2 at h1
  exact h1

example : P → ¬¬P := by
  intro h1
  by_contra h2
  change P → False at h2
  apply h2 at h1
  exact h1

example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2
  change P→ False
  intro h3
  change Q→ False at h2
  exact h2 (h1 (h3))

example : ¬¬False → False := by
  intro h1
  by_contra h2
  apply h1
  assumption

example : ¬¬P → P := by
  intro h1
  by_contra h2
  apply h1
  assumption

example : (¬Q → ¬P) → P → Q := by
  intro h1 h2
  by_contra h3
  apply h1 h3 at h2
  exact h2
