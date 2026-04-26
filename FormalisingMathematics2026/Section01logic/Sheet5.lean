/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro h1
  rw[h1]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  all_goals intro; apply symm ; assumption

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rwa[h1]
  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  all_goals
    rintro ⟨r,l⟩
    constructor
  all_goals
    assumption

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · rintro ⟨⟨l1,l2⟩,r⟩
    exact ⟨l1,⟨l2,r⟩⟩
  · rintro ⟨l,⟨r1,r2⟩⟩
    exact ⟨⟨l,r1⟩,r2⟩


/-my solution:

  constructor <;> rintro ⟨r,l⟩
  obtain ⟨r1,r2⟩ := r
  constructor ;assumption;constructor<;> assumption
  obtain ⟨l1,l2⟩ := l
  constructor ;constructor
  all_goals assumption
  看看solution
-/



example : P ↔ P ∧ True := by
  constructor<;>intro h1
  constructor ;assumption;trivial
  exact h1.1

example : False ↔ P ∧ False := by
  constructor
  rintro ⟨⟩
  rintro ⟨-,⟨⟩⟩
/-my solution :

  constructor<;>intro h1
  constructor<;>exfalso<;>assumption
  exact h1.2
-/
example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  rw[h1,h2]

example : ¬(P ↔ ¬P) := by
  intro h
  obtain⟨l,r⟩:=h
  by_cases h:P
  apply l at h ;
  all_goals apply h;apply r at h ;assumption
