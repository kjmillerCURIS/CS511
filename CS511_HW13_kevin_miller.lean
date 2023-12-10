import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Library.Theory.Comparison
import Library.Theory.InjectiveSurjective
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Define
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Extra
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Product
import Library.Tactic.Rel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Set

notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

/- 3 points -/
theorem problem4a : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp[Set.subset_def]
  dsimp[(.∣.)] at *
  push_neg
  use 5
  constructor
  · use 1
    numbers
  · intro c
    obtain hzero | hpos := le_or_gt c 0
    · have H : 5 > 20 * c := by
        calc
          5 > 0 := by extra
          _ = 20 * 0 := by ring
          _ ≥ 20 * c := by rel[hzero]
      apply ne_of_gt H
    · have hpos : c ≥ 1 := by extra
      have H : 5 < 20 * c := by
        calc
          5 < 5 + 15 := by extra
          _ = 20 * 1 := by ring
          _ ≤ 20 * c := by rel[hpos]
      apply ne_of_lt H

/- 3 points -/
theorem problem4b : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  dsimp
  dsimp[(.∣.)] at *
  intro x
  constructor
  · intro hleft
    obtain ⟨cleft, hleft⟩ := hleft
    use 4 * x - 3 * cleft
    calc
      x = 7 * 4 * x - 3 * (9 * x) := by ring
      _ = 7 * 4 * x - 3 * (7 * cleft) := by rw[hleft]
      _ = 7 * (4 * x - 3 * cleft) := by ring
  · intro hleft
    obtain ⟨cleft, hleft⟩ := hleft
    use 9 * cleft
    rw[hleft]
    ring

/- 4 points -/
--my solution inspired by example 9.1.8 from macbeth
theorem problem4c : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x + 2) = x ^ 2 + 3 * x + 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc x ^ 2 + 3 * x + 2 = (-1) ^ 2 + 3 * (-1) + 2 := by rw [h]
        _ = 0 := by numbers
    · calc x ^ 2 + 3 * x + 2 = (-2) ^ 2 + 3 * (-2) + 2 := by rw [h]
        _ = 0 := by numbers

/- 3 points -/
theorem problem5a : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
    dsimp[Set.subset_def]
    dsimp[Int.ModEq] at *
    dsimp[(.∣.)] at *
    intro x
    intro h710
    obtain ⟨b, h710⟩ := h710
    constructor
    · use 5 * b + 3
      calc
        x - 1 = x - 7 + 6 := by ring
        _ = 10 * b + 6 := by rw[h710]
        _ = 2 * (5 * b + 3) := by ring
    · use 2 * b + 1
      calc
        x - 2 = x - 7 + 5 := by ring
        _ = 10 * b + 5 := by rw[h710]
        _ = 5 * (2 * b + 1) := by ring

/- 3 points -/
theorem problem5b : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp[Set.subset_def]
  dsimp[(.∣.)] at *
  intro x
  intro h
  obtain ⟨hleft, hright⟩ := h
  obtain ⟨a, hleft⟩ := hleft
  obtain ⟨b, hright⟩ := hright
  use 2 * a - 3 * b
  have hleft : 16 * x = 40 * 2 * a := by
    rw[hleft]
    ring
  have hright : 15 * x = 40 * 3 * b := by
    rw[hright]
    ring
  calc
    x = 16 * x - 15 * x := by ring
    _ = 40 * 2 * a - 15 * x := by rw[hleft]
    _ = 40 * 2 * a - 40 * 3 * b := by rw[hright]
    _ = 40 * (2 * a - 3 * b) := by ring

--"helper" theorem for problem5c
theorem problem5chelper (x b c multiplier other_multiplier : ℤ) (h0 : multiplier > 1) (h1 : x = multiplier * b) : ¬(x ^ 2 - 1 = multiplier * other_multiplier * c) := by
  intro hcont
  have hcont : multiplier * (multiplier * b ^ 2 - other_multiplier * c) = 1 := by
    calc
      multiplier * (multiplier * b ^ 2 - other_multiplier * c) = (multiplier * b) ^ 2 - multiplier * other_multiplier * c := by ring
      _ = x ^ 2 - multiplier * other_multiplier * c := by rw[h1]
      _ = x ^ 2 - 1 - multiplier * other_multiplier * c + 1 := by ring
      _ = multiplier * other_multiplier * c - multiplier * other_multiplier * c + 1 := by rw[hcont]
      _ = 1 := by ring
  obtain hlo | hhi := le_or_gt (multiplier * b ^ 2 - other_multiplier * c) 0
  · have hcont : multiplier * (multiplier * b ^ 2 - other_multiplier * c) < 1 := by
      calc
        multiplier * (multiplier * b ^ 2 - other_multiplier * c) ≤ multiplier * 0 := by rel[hlo]
        _ = 0 := by ring
        _ < 1 := by extra
    have hcont : multiplier * (multiplier * b ^ 2 - other_multiplier * c) ≠ 1 := by apply ne_of_lt hcont
    contradiction
  · have hcont : multiplier * (multiplier * b ^ 2 - other_multiplier * c) > 1 := by
      have hhi : multiplier * b ^ 2 - other_multiplier * c ≥ 1 := by extra
      calc
        multiplier * (multiplier * b ^ 2 - other_multiplier * c) ≥ multiplier * 1 := by rel[hhi]
        _ > 1 * 1 := by rel[h0]
        _ = 1 := by ring
    have hcont : multiplier * (multiplier * b ^ 2 - other_multiplier * c) ≠ 1 := by apply ne_of_gt hcont
    contradiction

/- 4 points -/
theorem problem5c :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp[Set.subset_def]
  dsimp[Int.ModEq] at *
  dsimp[(.∣.)] at *
  push_neg
  intro x
  intro h
  obtain h3 | h2 := h
  · obtain ⟨b, h3⟩ := h3
    intro c
    intro hcont
    have h0 : (3 : ℤ) > 1 := by numbers
    have hcont : x ^ 2 - 1 = 3 * 2 * c := by
      calc
        x ^ 2 - 1 = 6 * c := by rw[hcont]
        _ = 3 * 2 * c := by ring
    have hmeow := problem5chelper x b c 3 2 h0 h3
    contradiction
  · obtain ⟨b, h2⟩ := h2
    intro c
    intro hcont
    have h0 : (2 : ℤ) > 1 := by numbers
    have hcont : x ^ 2 - 1 = 2 * 3 * c := by
      calc
        x ^ 2 - 1 = 6 * c := by rw[hcont]
        _ = 2 * 3 * c := by ring
    have hmeow := problem5chelper x b c 2 3 h0 h2
    contradiction
