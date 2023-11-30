import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Theory.InjectiveSurjective
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use
import Library.Tactic.Product
set_option push_neg.use_distrib true
open Function


theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by rfl
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rfl
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rfl
      _ = id x2 := by rw [hgf]
      _ = x2 := by rfl
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rfl
      _ = id y := by rw [hfg]
      _ = y := by rfl


--Macbeth 8.3.10.4
theorem problem4a {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) : Surjective (g ∘ f) := by
  dsimp[Surjective]
  intro b
  have hg' := hg b
  obtain ⟨c, hc⟩ := hg'
  have hf' := hf c
  obtain ⟨a, ha⟩ := hf'
  use a
  rw[ha]
  apply hc


--Macbeth 8.3.10.5
theorem problem4b {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp[Surjective] at hf
  choose g hg using hf
  use g
  ext b
  dsimp[id]
  apply hg


--Macbeth 8.3.10.6
theorem problem4c {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp[Inverse] at *
  obtain ⟨me, ow⟩ := h
  constructor
  · apply ow
  · apply me


--Macbeth 8.3.10.7
theorem problem4d {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) : g1 = g2 := by
  dsimp[Inverse] at *
  --dsimp[id] at *
  --dsimp[(.∘.)] at *
  ext x
  have hfbij := bijective_of_inverse h1
  dsimp[Bijective] at hfbij
  obtain ⟨_, hfsurj⟩ := hfbij
  dsimp[Surjective] at hfsurj
  obtain ⟨z, hz⟩ := hfsurj x
  have hz : x = f z := by rw[hz]
  rw[hz]
  obtain ⟨h1id, _⟩ := h1
  obtain ⟨h2id, _⟩ := h2
  calc
    g1 (f z) = (g1 ∘ f) z := by rfl
    _ = id z := by rw[h1id]
    _ = (g2 ∘ f) z := by rw[h2id]
    _ = g2 (f z) := by rfl


--Macbeth 8.4.10.2
theorem problem5a1 : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp[Injective]
  push_neg
  use (3, 1), (1, 0)
  constructor
  · ring
  · ring

theorem problem5a2 : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp[Surjective]
  intro b
  use (b + 1, 0)
  ring


--Macbeth 8.4.10.3
theorem problem5b : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp[Surjective]
  push_neg
  use -1
  intro a
  have hmeow : a.fst ^ 2 + a.snd ^ 2 > -1 := by
    calc
      a.fst ^ 2 + a.snd ^ 2 ≥ a.fst ^ 2 + 0 := by extra
      _ ≥ 0 + 0 := by extra
      _ > -1 := by ring
  apply ne_of_gt hmeow


--Macbeth 8.4.10.6
theorem problem5c : ¬ Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp[Injective]
  push_neg
  use (0,0,0), (-1,2,-1)
  constructor
  · ring
  · numbers


--Macbeth 8.4.10.7
theorem problem5d : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  dsimp[Injective]
  intro a1 a2
  intro houteq
  obtain ⟨houteq1, houteq2, _⟩ := houteq
  --(a1.fst + a1.snd, a1.fst + 2 * a1.snd, a1.fst + 3 * a1.snd)
  calc
    a1 = (2 * (a1.fst + a1.snd) - (a1.fst + 2 * a1.snd), (a1.fst + 2 * a1.snd) - (a1.fst + a1.snd)) := by ring
    _ = (2 * (a2.fst + a2.snd) - (a2.fst + 2 * a2.snd), (a2.fst + 2 * a2.snd) - (a2.fst + a2.snd)) := by rw[houteq1, houteq2]
    _ = a2 := by ring
