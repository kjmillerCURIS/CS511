import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


theorem DeMorgan2 {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro hnotpandnotq 
  obtain ⟨hnotp, hnotq⟩ := hnotpandnotq
  intro hporq
  cases hporq
  {
    --assume p is true
    --this contradicts with hnotp
    contradiction
  }
  {
    --assume q is true
    --this contradicts with hnotq
    contradiction
  }
  --and now the leprechauns apply vee-elimination to get contradiction from hporq
  --and then they apply neg-introduction to get ¬(p ∨ q)
  --and then they close the box to get (¬p ∧ ¬q) → ¬(p ∨ q)
  --thanks leprechauns!


theorem DeMorgan3 {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) := by
  intro hnotpornotq
  intro hpandq
  obtain ⟨hp, hq⟩ := hpandq
  cases hnotpornotq
  {
    --assume notp is true
    --contradicts with hp
    contradiction
  }
  {
    --assume notq is true
    --contradicts with hq
    contradiction
  }
  --now the leprechauns apply vee-elimination, and then neg-introduction, and then close the box
  --thanks leprechauns!


example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := 
  calc
    x = (x + 3) - 3 := by ring --add +3 and -3 to x so we get an "x + 3"
    _ ≥ 2 * y - 3 := by rel [h1] --now we substitute h1 into "x + 3"
    _ ≥ 2 * 1 - 3 := by rel [h2] --and substitute h2 into "1" (apparently the leprechauns know that "1 ≤ y" is the same as "y ≥ 1")
    _ = -1 := by ring --now do some arithmetic to finish it up


example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (2 * a + 2 * b) / 2 := by ring --expand "a + b" to something that will eventually contain "a + 2 * b"
    _ = (a + (a + 2 * b)) / 2 := by ring --finish expanding it to explicitly contain "a + 2 * b"
    _ ≥ (a + 4) / 2 := by rel [h2] --now we can substitute h2
    _ ≥ (3 + 4) / 2 := by rel [h1] --and then substitute h1 (thanks leprechauns for not making me prove directionality stuff!)
    _ ≥ 3 := by numbers --just arithmetic. Interestingly, the leprechauns don't like it if you say "ring" here...


example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    --time to do the factor-out-the-powers trick from Macbeth
    --because for some reason the leprechauns "can't" reason about powers
    --but they "can" reason about products
    --go figure...
    x ^ 3 - 8 * x ^ 2 + 2 * x = (x - 8) * x ^ 2 + 2 * x := by ring --factor x^2 out of first two terms
    _ ≥ (9 - 8) * x ^ 2 + 2 * x := by rel [hx] --subtitute 9 for x
    _ = (x + 2) * x := by ring --do some arithmetic/algebra, and factor x out of remaining two terms
    _ ≥ (9 + 2) * x := by rel [hx] --substitute 9 for x again
    _ ≥ (9 + 2) * 9 := by rel [hx] --and for the other x
    _ ≥ 3 := by numbers --do arithmetic