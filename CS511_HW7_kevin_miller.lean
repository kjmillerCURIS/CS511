import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


--Macbeth 5.3.5
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt --assume n ≤ 1
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers --and here I thought "numbers" could only do equalities, silly me...
  · apply ne_of_gt --assume 2 ≤ n -- apparently you can apply ne_of_gt "in reverse" to a goal? that's cool :)
    calc
      2 < 2 + 2 := by extra --ok I guess this time "numbers" can't do it, maybe it got tired, totally understandable...
      _ = 2 ^ 2 := by ring
      _ ≤ n ^ 2 := by rel [hn]


--Macbeth 5.3.6.2
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro hnotimp --assume ¬ (P → Q), prove (P ∧ ¬ Q)
    by_cases hmeow : (P ∧ ¬ Q)
    · apply hmeow --we assumed the thing we want to prove :)
    · have himp : P → Q --try to contradict hnotimp by proving P → Q
      · intro hP --assume P, try to prove Q
        by_cases hpurr : Q
        · apply hpurr --we have Q, which is what we wanted to prove
        · have hand : P ∧ ¬ Q --we have ¬ Q, so we can contradict hmeow by proving P ∧ ¬ Q, and then that contradiction proves Q
          · constructor
            · apply hP
            · apply hpurr
          contradiction --hand contradicts with hmeow
      contradiction --himp contradicts with hnotimp
  · intro hand -- assume (P ∧ ¬ Q), prove ¬ (P → Q)
    by_cases hmeow : P → Q
    · have hpurr : ¬ (P ∧ ¬ Q) --try to contradict hand by proving ¬ (P ∧ ¬ Q)
      · by_cases hekekek : P ∧ ¬ Q
        · obtain ⟨hP, hnotQ⟩ := hekekek --now we have P ∧ ¬ Q and want to make a contradiction from it
          have hQ : Q := by apply hmeow hP
          contradiction --hQ contradicts hnotQ
        · apply hekekek --we have ¬ (P ∧ ¬ Q) as we wanted
      contradiction --hpurr contradicts hand
    · apply hmeow --this is the easy one, we have the case ¬ (P → Q) which is what we wanted to prove