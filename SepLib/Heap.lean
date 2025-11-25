import Mathlib.Data.Finmap

abbrev Loc := Nat

abbrev Val := Nat

abbrev Heap := Finmap (fun _ : Loc => Val)

namespace Heap

def empty : Heap := ∅

def union (h1 h2 : Heap) : Heap :=
  Finmap.union h1 h2

infixr:60 " ⊔ " => union

@[simp]
theorem union_empty {h : Heap} :
    h ⊔ ∅ = h := by
  unfold union
  apply Finmap.union_empty

@[simp]
theorem empty_union {h : Heap} :
    ∅ ⊔ h = h := by
  unfold union
  apply Finmap.empty_union

def Disjoint (h1 h2 : Heap) : Prop :=
  Finmap.Disjoint h1 h2

infix:60 " ⊥ " => Disjoint

@[symm]
theorem disjoint_symm {h1 h2 : Heap} :
    h1 ⊥ h2 → h2 ⊥ h1 := by
  intros
  unfold Disjoint at *
  symm
  assumption

theorem disjoint_empty (h : Heap) :
    ∅ ⊥ h := by
  exact Finmap.disjoint_empty h

theorem union_comm {h1 h2 : Heap} (d : h1 ⊥ h2) :
    h1 ⊔ h2 = h2 ⊔ h1 := by
  apply_rules [Finmap.union_comm_of_disjoint]

theorem union_assoc (h1 h2 h3 : Heap) :
    (h1 ⊔ h2) ⊔ h3 = h1 ⊔ (h2 ⊔ h3) := by
  exact Finmap.union_assoc

instance : Std.Associative union := ⟨union_assoc⟩

theorem disjoint_union_left {h1 h2 h3 : Heap} :
    (h1 ⊔ h2) ⊥ h3 ↔ h1 ⊥ h3 ∧ h2 ⊥ h3 := by
  exact Finmap.disjoint_union_left h1 h2 h3

theorem disjoint_union_right {h1 h2 h3 : Heap} :
    h1 ⊥ (h2 ⊔ h3) ↔ h1 ⊥ h2 ∧ h1 ⊥ h3 := by
  exact Finmap.disjoint_union_right h1 h2 h3

end Heap
