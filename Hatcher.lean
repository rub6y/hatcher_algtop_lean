import Mathlib.Topology.Path

open unitInterval

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

-- Definition 1 (Homotopy of maps)
-- Main structure of homotopy
structure Homotopy (f g : X → Y) where
  (H : X × I → Y)
  (contH : Continuous H)
  (leftH : ∀ x, H (x, 0) = f x)
  (rightH : ∀ x, H (x, 1) = g x)

def Homotopic (f g : X → Y) :=
  Nonempty (Homotopy f g)

notation:50 f "≃" g => Homotopic f g

-- Example of usage
def ex_f : ℝ → ℝ := fun x => x
def ex_g : ℝ → ℝ := fun _ => 0

example : ex_f ≃ ex_g := by
  let exH : ℝ × I → ℝ := fun (x, t) => (1 - (t : ℝ)) * x

  have excontH : Continuous exH := by
    unfold exH
    continuity

  have exleftH : ∀ x, exH (x, 0) = ex_f x := by
    intro x
    simp [exH, ex_f]

  have exrightH : ∀ x, exH (x, 1) = ex_g x := by
    intro x
    simp [exH, ex_g]

  refine ⟨{
    H := exH
    contH := excontH
    leftH := exleftH
    rightH := exrightH
  }⟩

-- Definition 2 (Path)
-- We can take it from mathlib! (We also could use the definition of homotopy from Mathlib)

-- Definition 3 (Loop)
structure Loop (x : X) extends Path x x

-- Definition 4 (Homotopy of paths)
structure PathHomotopy (x y : X) (γ₁ γ₂ : Path x y) extends Homotopy γ₁ γ₂ where
  (statH : ∀ (t : I), H (0, t) = x ∧ H (1,t) = y)

def PathHomotopic (x y : X) (γ₁ γ₂ : Path x y) :=
  Nonempty (PathHomotopy x y γ₁ γ₂)

notation:50 f "≃ₚ" g => Homotopic f g

-- Lemma 5 (All paths from to in are Homotopic)
lemma Rn_allpathHomotopic (n : ℕ) :  ∀ (x y : Fin n → ℝ) (γ₁ γ₂ : Path x y), γ₁ ≃ₚ γ₂ := by
  sorry
