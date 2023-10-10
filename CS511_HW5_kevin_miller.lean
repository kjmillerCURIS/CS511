import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use
import Library.Tactic.Induction
namespace Nat


--Macbeth 4.2.10.2
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro hleft --assume 63 is factor, prove 7 and 9
    obtain ⟨a, ha⟩ := hleft
    constructor
    · use 9 * a
      calc
        n = 63 * a := by rw[ha]
        _ = 7 * (9 * a) := by ring
    · use 7 * a
      calc
        n = 63 * a := by rw[ha]
        _ = 9 * (7 * a) := by ring
  · intro hright --assume 7 and 9 are factors, prove 63
    obtain ⟨h7, h9⟩ := hright
    obtain ⟨b, hb⟩ := h7
    obtain ⟨c, hc⟩ := h9
    use 4 * c - 3 * b
    calc
      n = 4 * 7 * n - 3 * 9 * n := by ring
      _ = 4 * 7 * n - 3 * 9 * (7 * b) := by rw[hb]
      _ = 4 * 7 * (9 * c) - 3 * 9 * (7 * b) := by rw[hc]
      _ = 63 * (4 * c - 3 * b) := by ring


--Macbeth 4.2.10.5
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro hleft --assume inequality, prove {0,1,2}
    have hleft : k ^ 2 < 3 ^ 2 := by
      calc
        k ^ 2 ≤ 6 := by rel[hleft]
        _ < 6 + 3 := by extra
        _ = 3 ^ 2 := by numbers
    cancel 2 at hleft --k < 3
    interval_cases k
    · left
      numbers
    · right
      left
      numbers
    · right
      right
      numbers
  · intro hright --assume {0,1,2}, prove inequality
    obtain h0 | h12 := hright
    · calc
        k ^ 2 = 0 ^ 2 := by rw[h0]
        _ = 0 := by ring
        _ ≤ 6 := by extra
    · obtain h1 | h2 := h12
      · calc
          k ^ 2 = 1 ^ 2 := by rw[h1]
          _ = 1 := by ring
          _ ≤ 1 + 5 := by extra
          _ = 6 := by ring --(didn't need this line for some reason? since when did lean do math on its own?)
      · calc
          k ^ 2 = 2 ^ 2 := by rw[h2]
          _ = 4 := by ring
          _ ≤ 4 + 2 := by extra
          _ = 6 := by ring --(didn't need this line for some reason? since when did lean do math on its own?)


--Macbeth 4.3.2
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  --first part, show that 1 works
  have hgoal : ∀ a : ℚ, a ≥ 1 → a ≤ 3 → (a - 2) ^ 2 ≤ 1 := by
    intro a ha haa
    have ha : -1 ≤ a - 2 := by
      calc
        -1 = 1 - 2 := by ring
        _ ≤ a - 2 := by addarith[ha]
    have haa : a - 2 ≤ 1 := by
      calc
        a - 2 ≤ 3 - 2 := by addarith[haa]
        _ = 1 := by ring 
    have halmost : (a - 2) ^ 2 ≤ 1 ^ 2 := by apply sq_le_sq' ha haa
    calc
      (a - 2) ^ 2 ≤ 1 ^ 2 := by rel[halmost]
      _ = 1 := by ring
  use 2
  dsimp
  constructor
  · apply hgoal
  --second part, show that a thing that works must be 1
  intro y hy
  have h1' : 1 ≥ 1 → 1 ≤ 3 → (1 - y) ^ 2 ≤ 1 := hy 1
  have h1 : (1 - y) ^ 2 ≤ 1 := by
    apply h1'
    simp
    simp
  have h3' : 3 ≥ 1 → 3 ≤ 3 → (3 - y) ^ 2 ≤ 1 := hy 3
  have h3 : (3 - y) ^ 2 ≤ 1 := by
    apply h3'
    simp
    simp
  have hsquaresqueeze : (y - 2) ^ 2 ≤ 0 ^ 2 := by
    calc
      (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
      _ ≤ (1 + (3 - y) ^ 2 - 2) / 2 := by rel[h1]
      _ ≤ (1 + 1 - 2) / 2 := by rel[h3]
      _ = 0 ^ 2 := by ring
  have hpos : (0 : ℚ) ≤ (0 : ℚ) := by addarith
  have hsqueeze : 0 ≤ y - 2 ∧ y - 2 ≤ 0 := by apply abs_le_of_sq_le_sq' hsquaresqueeze hpos
  addarith[hsqueeze] --that's right, lean can understand squeeze! it's a Christmas freakin' miracle!


--Macbeth 4.3.5.1
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (4 * y - 3 + 3) / 4 := by ring
    _ = (9 + 3) / 4 := by rw[hy]
    _ = 3 := by numbers


--Macbeth 4.3.5.2
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  have hgoal : ∀ a : ℕ, 0 ≤ a := by
    intro a
    extra
  use 0
  dsimp
  constructor
  · apply hgoal
  intro y hy
  have h0 : y ≤ 0 := hy 0
  interval_cases y
  · numbers


--Macbeth 4.4.4
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    have h_m_le_p : m ≤ p := by apply Nat.le_of_dvd hp' hmp
    obtain h_eq | h_lt : m = p ∨ m < p := eq_or_lt_of_le h_m_le_p
    · -- the case `m = p`
      right
      addarith [h_eq]
    · -- the case `m < p`
      have hsimp : 1 < m → m < p → ¬m ∣ p := H m
      have hmeow : ¬m ∣ p := by
        apply hsimp hm_left h_lt
      contradiction


--Macbeth 4.4.5
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  have Ha := le_or_gt 3 a
  obtain htrivial_a | hinteresting_a := Ha
  · addarith[htrivial_a]
  · have hinteresting_a : a ≤ 2 := by addarith[hinteresting_a]
    have Hb := le_or_gt b 1
    obtain hcases_b | hcontra_b := Hb
    · have hc3 : c ^ 2 < 3 ^ 2 := by --hcases_b part (the one with lots of cases)
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw[h_pyth]
          _     ≤ 2 ^ 2 + b ^ 2 := by rel[hinteresting_a]
          _     ≤ 2 ^ 2 + 1 ^ 2 := by rel[hcases_b]
          _     = 5 := by numbers
          _     < 5 + 4 := by extra
          _     = 3 ^ 2 := by numbers
      cancel 2 at hc3
      interval_cases a
      · interval_cases b --a = 1
        · interval_cases c --a = 1, b = 1
          · contradiction --a = 1, b = 1, c = 1
          · contradiction --a = 1, b = 1, c = 2
      · interval_cases b --a = 2
        · interval_cases c --a = 2, b = 1
          · contradiction --a = 2, b = 1, c = 1
          · contradiction --a = 2, b = 1, c = 2
    · have hcontra_b : b ≥ 2 := by addarith[hcontra_b] --hcontra_b part (the one with one big contradiction)
      have hasqpos : 0 < a ^ 2 := by
        calc
          0 = 0 * 0 := by ring
          _ ≤ a * 0 := by rel[ha]
          _ < a * a := by rel[ha]
          _ = a ^ 2 := by ring
      have hbc : b ^ 2 < c ^ 2 := by
        calc
          b ^ 2 = 0 + b ^ 2 := by ring
          _     < a ^ 2 + b ^ 2 := by rel[hasqpos]
          _     = c ^ 2 := by rw[h_pyth]
      cancel 2 at hbc
      have hbc : c ≥ b + 1 := by addarith[hbc]
      have hcb : c ^ 2 < (b + 1) ^ 2 := by
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw[h_pyth]
          _     ≤ 2 ^ 2 + b ^ 2 := by rel[hinteresting_a]
          _     = b ^ 2 + 2 * 2 := by ring
          _     ≤ b ^ 2 + 2 * b := by rel[hcontra_b]
          _     < b ^ 2 + 2 * b + 1 := by extra
          _     = (b + 1) ^ 2 := by ring
      cancel 2 at hcb
      have : ¬(c ≥ b + 1) := by addarith[hcb]
      contradiction
      

--Macbeth 4.4.6.1
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  obtain htrivial | hinteresting := le_or_gt y x
  · rel[htrivial]
  · have hbad : y ^ n > x ^ n := by rel[hinteresting] --holy cow, it actually worked!
    have hbad : ¬(y ^ n ≤ x ^ n) := not_le_of_lt hbad
    contradiction


--Macbeth 4.4.6.5
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain p_even | p_odd := Nat.even_or_odd p
  · left --harder case - if it's even and prime, then it's 2
    obtain ⟨hmisc, hgoat⟩ := h
    have hgoat : 2 ∣ p → 2 = 1 ∨ 2 = p := hgoat 2
    obtain ⟨a, ha⟩ := p_even
    have h2p : (2 ∣ p) := by
      use a
      apply ha
    have halmost : 2 = 1 ∨ 2 = p := by apply hgoat h2p
    obtain hsilly | hfinally := halmost
    · contradiction
    · rw[hfinally]
  · right --easier case - it's already odd
    obtain ⟨x, hx⟩ := p_odd
    use x
    calc
      p = 2 * x + 1 := by rw[hx] --there, we proved Odd p from Odd p! thanks lean!