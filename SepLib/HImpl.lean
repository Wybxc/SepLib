import SepLib.HProp

namespace HProp

def entails (P Q : HProp) : Prop :=
  ∀ (h : Heap), P h → Q h

infix:50 " ⊢ " => entails

@[refl]
theorem entails_refl (P : HProp) :
    P ⊢ P := by
  intro h hP
  assumption

instance : IsRefl HProp entails := ⟨entails_refl⟩

theorem entails_trans (P Q R : HProp) :
    P ⊢ Q →
    Q ⊢ R →
    P ⊢ R := by
  intros hPQ hQR h hP
  apply hQR
  apply hPQ
  assumption

instance : IsTrans HProp entails := ⟨entails_trans⟩

theorem entails_antisymm (P Q : HProp) :
    P ⊢ Q →
    Q ⊢ P →
    P = Q := by
  intro hPQ hQP
  ext
  constructor <;> intro
  · apply hPQ
    assumption
  · apply hQP
    assumption

instance : IsAntisymm HProp entails := ⟨entails_antisymm⟩

theorem entails_frame_left {P Q : HProp} (R : HProp) :
    P ⊢ Q →
    (R ∗* P) ⊢ (R ∗* Q) := by
  rintro hPQ h ⟨h1, h2, rfl, d, hR, hP⟩
  star_exists h1, h2

theorem entails_frame_right {P Q : HProp} (R : HProp) :
    P ⊢ Q →
    (P ∗* R) ⊢ (Q ∗* R) := by
  intro
  conv => args; all_goals rw [star_comm]
  apply entails_frame_left
  assumption

theorem entails_star_pure_right {P : Prop} {H1 H2 : HProp} :
    P → (H1 ⊢ H2) →
    H1 ⊢ (H2 ∗* ⟦ P ⟧) := by
  intro hP hentails h hH
  star_exists h, ∅
  exists hP

theorem entails_star_pure_left {P : Prop} {H1 H2 : HProp} :
    (P → H1 ⊢ H2) →
    (⟦ P ⟧ ∗* H1) ⊢ H2 := by
  rintro hentails h ⟨h1, h2, rfl, d, ⟨hP, rfl⟩, hH⟩
  rw [Heap.empty_union]
  apply hentails hP
  assumption

theorem entilas_exists_right {α : Sort*} {x : α} {J : α → HProp} {H : HProp} :
    (H ⊢ J x) →
    H ⊢ (∃ x, J x) := by
  intro hentails h hH
  exists x
  simp
  apply hentails
  assumption

theorem entails_exists_left {α : Sort*} {J : α → HProp} {H : HProp} :
    (∀ x, J x ⊢ H) →
    (∃ x, J x) ⊢ H := by
  intro hentails h ⟨x, hJ⟩
  apply hentails x
  assumption

theorem star_points_to_same_loc {l : Loc} {v1 v2 : Val} :
    (l ↦ v1 ∗* l ↦ v2) ⊢ ⟦ False ⟧ := by
  rintro h ⟨h1, h2, rfl, d, rfl, rfl⟩
  have := Heap.disjoint_singleton.mp d
  contradiction

end HProp
