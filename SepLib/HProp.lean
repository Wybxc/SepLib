import SepLib.Heap

abbrev HProp := Heap → Prop

namespace HProp

def emp : HProp :=
  fun h => h = ∅

notation "⟦⟧" => emp

def points_to (l : Loc) (v : Val) : HProp :=
  fun h => h = Finmap.singleton l v

infix:70 " ↦ " => points_to

def star (P Q : HProp) : HProp :=
  fun h => ∃ (h1 h2 : Heap),
            h = h1 ⊔ h2 ∧
            h1 ⊥ h2 ∧
            P h1 ∧
            Q h2

infixl:60 " ∗* " => star

def hexists {α : Sort*} (J : α → HProp) : HProp :=
  fun h => ∃ (x : α), J x h

notation "∃" v ", " P => hexists (fun v => P)
-- TODO: ∃ v1 v2 ... vn, P

abbrev pure (P : Prop) : HProp := ∃ (_ : P), ⟦⟧

notation (priority:=1001) "⟦ " P " ⟧" => pure P

theorem emp_intro :
    ⟦⟧ ∅ := by
  rfl

theorem points_to_intro (l : Loc) (v : Val) :
    (l ↦ v) (Finmap.singleton l v) := by
  rfl

theorem star_intro (P Q : HProp) (h1 h2 : Heap) :
    P h1 →
    Q h2 →
    h1 ⊥ h2 →
    (P ∗* Q) (h1 ⊔ h2) := by
  intros
  exists h1, h2

theorem exists_intro {α : Sort*} (J : α → HProp) (x : α) (h : Heap) :
    J x h →
    (∃ x, J x) h := by
  intros
  exists x

macro "star_exists" hs:term,+ : tactic =>
  `(tactic| (exists $hs,*;
             and_intros;
             all_goals try simp;
             all_goals try ac_rfl;
             all_goals try (apply_rules [Heap.disjoint_empty]; done);
             all_goals try (symm; apply_rules [Heap.disjoint_empty]; done)))

@[simp]
theorem star_exists {α : Sort*} {J : α → HProp} {H : HProp} :
    (∃ x, J x) ∗* H = ∃ x, (J x ∗* H) := by
  ext
  constructor
  · intro hstar
    rcases hstar with ⟨h1, h2, rfl, d, ⟨x, j⟩, hh⟩
    exists x, h1, h2
  · intro hex
    rcases hex with ⟨x, h1, h2, rfl, d, j, hh⟩
    star_exists h1, h2
    exists x

@[simp]
theorem star_emp_left {P : HProp} :
    ⟦⟧ ∗* P = P := by
  ext h
  constructor
  · rintro ⟨h1, h2, rfl, d, rfl, hp⟩
    rw [Heap.empty_union]
    assumption
  · intros hp
    rw [← Heap.empty_union (h := h)]
    apply star_intro <;> try trivial
    exact Heap.disjoint_empty h

theorem star_comm (P Q : HProp) :
    P ∗* Q = Q ∗* P := by
  ext
  constructor
  all_goals {
    rintro ⟨h1, h2, rfl, d, hP, hQ⟩
    star_exists h2, h1; apply_rules [Heap.union_comm]
  }

instance : Std.Commutative star := ⟨star_comm⟩

theorem star_assoc (P Q R : HProp) :
    (P ∗* Q) ∗* R = P ∗* (Q ∗* R) := by
  ext
  constructor
  · rintro ⟨h1, h2, rfl, d1, ⟨h3, h4, rfl, d2, hP, hQ⟩, hR⟩
    obtain ⟨d3, d4⟩ := Heap.disjoint_union_left.mp d1
    star_exists h3, (h4 ⊔ h2)
    · apply Heap.disjoint_union_right.mpr
      trivial
    · exists h4, h2
  · rintro ⟨h1, h2, rfl, d1, hP, ⟨h3, h4, rfl, d2, hQ, hR⟩⟩
    obtain ⟨d3, d4⟩ := Heap.disjoint_union_right.mp d1
    star_exists (h1 ⊔ h3), h4
    · apply Heap.disjoint_union_left.mpr
      trivial
    · exists h1, h3

instance : Std.Associative star := ⟨star_assoc⟩

@[simp]
theorem star_emp_right {P : HProp} :
    P ∗* ⟦⟧ = P := by
  rw [star_comm]
  apply star_emp_left

theorem star_comm_assoc {P Q R : HProp} :
    P ∗* (Q ∗* R) = R ∗* (Q ∗* P) := by
  ac_rfl

@[simp]
theorem star_pure_left {P : Prop} {H : HProp} {h : Heap} :
    (⟦ P ⟧ ∗* H) h = (P ∧ H h) := by
  apply propext
  constructor
  · rintro ⟨h1, h2, rfl, d, ⟨hP, rfl⟩, hH⟩
    rw [Heap.empty_union]
    trivial
  · rintro ⟨hP, hH⟩
    star_exists ∅, h
    exists hP

@[simp]
theorem pure_true_eq_emp :
    ⟦ True ⟧ = ⟦⟧ := by
  ext
  constructor
  · rintro ⟨hT, rfl⟩
    rfl
  · intros
    exists True.intro

end HProp
