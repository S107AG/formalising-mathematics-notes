/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro h1
  right
  assumption

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl h => intro h1 h2;exact h1 h
  | inr h => intro h1 h2;exact h2 h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  obtain h | h := hPoQ
  · intro h1 h2
    exact h1 h
  · intro h1 h2
    exact h2 h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h)
  · intro h1 h2
    exact h1 h
  · intro h1 h2
    exact h2 h

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  rintro (h|h)
  · right ; assumption
  · left  ; assumption

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · rintro ((h|h)|h)
    left;assumption
    right;left;assumption
    right;right;assumption
  · rintro (h|(h|h))
    left;left;assumption
    left;right;assumption
    right;assumption

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  obtain h|h :=h3
  · left;exact h1 h
  · right;exact h2 h

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  obtain h|h :=h2
  · left;exact h1 h
  · right;exact h

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  rw[h1,h2]

/-My Solution
  intro h1 h2
  constructor<;>intro h
  · rw[h1,h2] at h;assumption
  · rw[← h1,← h2] at h;assumption
-/

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor<;>intro h
  · constructor
    · intro h1
      apply h
      left
      assumption
    · intro h1
      apply h
      right
      assumption
  intro h1
  obtain hP|hQ:=h1
  · apply h.1;assumption
  · apply h.2;assumption

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor <;> intro h
  · by_cases hP : P
    · right
      intro hQ
      apply h
      exact ⟨hP,hQ⟩
    · left
      assumption
  intro h1
  obtain hnP|hnQ := h
  · apply hnP
    exact h1.1
  · apply hnQ
    exact h1.2


/-My Solution1 Needs more understands
  constructor<;> intro h
  · by_contra h1
    apply h
    constructor
    · by_contra h2
      apply h1
      left;assumption
    · by_contra h2
      apply h1
      right;assumption
  intro h1
  obtain h2|h2 := h
  · apply  h2
    exact h1.1
  · apply h2
    exact h1.2
-/
