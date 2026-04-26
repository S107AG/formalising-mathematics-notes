/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all of the tactics in Lean's maths library


/-!

# Logic in Lean, example sheet 1 : "implies" (`→`)

A *proposition* is a true-false statement, like `2+2=4` or `2+2=5`
or the Riemann hypothesis. In algebra we manipulate
numbers whilst not knowing what the numbers actually are; the trick is
that we call the numbers `x` and `y` and so on. In this sheet we
will learn how to manipulate propositions without saying what the
propositions are -- we'll just call them things like `P` and `Q`.

The purpose of these first few sheets is to teach you some very basic
*tactics*. In particular we will learn how to manipulate statements
such as "P implies Q", which is itself a true-false statement (e.g.
it is false when P is true and Q is false). In Lean we use the
notation `P → Q` for "P implies Q". You can get
this arrow by typing `\to` or `\r`. Mathematicians usually write the
implication arrow as `P ⇒ Q` but Lean prefers a single arrow.

## The absolute basics

`P : Prop` means that `P` is a true-false statement. `h : P` means
that `h` is a proof that `P` is true. You can also regard `h` as the
hypothesis that `P` is true; logically these are the same. Stuff above
the `⊢` symbol is your assumptions. The statement to the right of it is
the goal. Your job is to prove the goal from the assumptions.

## Tactics you will need

To solve the levels on this sheet you will need to know how to use the
following three tactics:

* `intro`
* `exact`
* `apply`

You can read the descriptions of these tactics in Part 2 of the online course
notes here https://b-mehta.github.io/formalising-mathematics-notes/
In this course we'll be learning about 30 tactics in total; the goal of this
first logic section is to get you up to speed with ten very basic ones.

## Worked examples

Click around in the proofs to see the tactic state (on the right) change.
The tactic is implemented and the state changes just before the newline or semicolon (`;`).
I will use the following conventions: variables with capital
letters like `P`, `Q`, `R` denote propositions
(i.e. true/false statements) and variables whose names begin
with `h` like `h1` or `hP` are proofs or hypotheses.

-/

set_option linter.unusedVariables false

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

-- Here are some examples of `intro`, `exact` and `apply` being used.
-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.
example (hP : P) (hQ : Q) (hR : R) : P := by
  -- note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.
  exact hP

-- Same example: assume that `P` and `Q` and `R` are true, but this time
-- give the assumptions silly names. Deduce that `P` is true.
example (fish : P) (giraffe : Q) (dodecahedron : R) : P := by
-- `fish` is the name of the assumption that `P` is true (but `hP` is a better name)
  exact fish

-- Assume `Q` is true. Prove that `P → Q`.
example (hQ : Q) : P → Q := by
  -- The goal is of the form `X → Y` so we can use `intro`
  intro (fish : P)
  -- now `h` is the hypothesis that `P` is true.
  -- Our goal is now the same as a hypothesis so we can use `exact`
  exact hQ
  -- note `exact Q` doesn't work: `exact` takes the *term*, not the type.

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q := by
  -- `hP` says that `P` is true, and `h` says that `P` implies `Q`, so `apply h at hP` will change
  -- `hP` to a proof of `Q`.
  apply h at hP
  -- now `hP` is a proof of `Q` so that's exactly what we want.
  exact hP

-- The `apply` tactic always needs a hypothesis of the form `P → Q`. But instead of applying
-- it to a hypothesis `h : P` (which changes the hypothesis to a proof of `Q`), you can instead
-- just use a bare `apply h` and it will apply it to the *goal*, changing it from `Q` to `P`.
-- Here we are "arguing backwards" -- if we know that P implies Q, then to prove Q it suffices to
-- prove P.

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q := by
  -- `h` says that `P` implies `Q`, so to prove `Q` (our goal) it suffices to prove `P`.
  apply h
  -- Our goal is now `⊢ P`.
  exact hP

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, this means that to deduce `R` you will need to prove both `P`
and `Q`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and then you have to prove `Pn`.

So the next level is asking you to prove that `P → (Q → P)`.

-/
example : P → Q → P := by
  intro hP hQ
  -- the `assumption` tactic will close a goal if
  -- it's exactly equal to one of the hypotheses.
  assumption

/-

## Examples for you to try

Delete the `sorry`s and replace them with tactic proofs using `intro`,
`exact` and `apply`, separating them with newlines or semicolons (`;`).

-/
/-- Every proposition implies itself. -/
example : P → P := by
  intro h
  exact h

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q := by
  intro h1 h2
  apply h2 at h1
  exact h1

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/
example : (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR hP  --一次intro多个中间以空格分隔
  exact hQR (hPQ (hP))  --对于定理的使用，中间也是以空格分隔，定理需要多个条件的，以括号划清嵌套关系

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
-- two goals! Note that tactics operate on only the first goal.
example : (P → Q → R) → (P → Q) → P → R := by
  intro hPQR hPQ hP
  exact hPQR hP (hPQ hP)--hPQ有两个条件，后一个括号里实际上就是hQ的证明，用括号来表示为一个整体

/-

Here are some harder puzzles. They won't teach you anything new about
Lean, they're just trickier. If you're not into logic puzzles
and you feel like you understand `intro`, `exact` and `apply`
then you can just skip these and move onto the next sheet
in this section, where you'll learn some more tactics.

-/
variable (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro hPR hSQ hRT hQR hS
  apply (hRT ∘ hQR ∘ hSQ) at hS--∘ 是函数复合，注意顺序为从右到左
  exact hS

example : (P → Q) → ((P → Q) → P) → Q := by
  intro hPQ hPQtoP
  apply hPQ∘ hPQtoP at hPQ
  exact hPQ

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro hPQtoR QRtoP RPtoQ
  apply QRtoP
  intro hQ
  apply hPQtoR
  intro hP
  exact hQ


example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro hQPP hQR hRP
  apply hQPP
  exact hRP ∘ hQR

example : (((P → Q) → Q) → Q) → P → Q := by
  intro hPQQQ hP
  apply hPQQQ
  intro hPQ
  exact hPQ (hP)

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  intro h1 h2 h3
  apply h2
  intro hPPQ hP1 hP2
  apply hPPQ
  intro hP
  exact hP1
