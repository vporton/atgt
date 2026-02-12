import Mathlib.Data.Ordmap.Ordset
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Order.Hom.Basic

universe u v u2 v2

instance {u} : Coe (SemilatticeInf u) (PartialOrder u) where
    coe s := s.toPartialOrder

/- TODO: Should be in `Ordset`, instead. -/
def is_least {α : Type*} [PartialOrder α] (a: α) := ∀ x, a ≤ x

/- TODO: Should be in `Ordset`, instead. -/
def meet {α : Type*}[PartialOrder α] (a b : α) := ∃ c, c ≤ a ∧ c ≤ b ∧ ¬ (is_least c)

theorem meet_comm {α : Type*} [PartialOrder α] (a b : α) : meet a b ↔ meet b a := by
    simp [meet]
    tauto

theorem meet_mono_left {α : Type*} [PartialOrder α] {a b c : α} (h : a ≤ b) : meet a c → meet b c := by
    intro h_meet
    rcases h_meet with ⟨d, hd_a, hd_c, hd_not_least⟩
    exact ⟨d, le_trans hd_a h, hd_c, hd_not_least⟩

theorem meet_mono_right {α : Type*} [PartialOrder α] {a b c : α} (h : b ≤ c) : meet a b → meet a c := by
    intro h_meet
    rcases h_meet with ⟨d, hd_a, hd_b, hd_not_least⟩
    exact ⟨d, hd_a, le_trans hd_b h, hd_not_least⟩

/- TODO: Should be in `Ordset`, instead. -/
theorem meet_as_inf {α : Type u}
  [s : SemilatticeInf α] (a b : α) :
  meet a b ↔
  ¬ is_least (a ⊓ b) :=
by
  constructor
  · intro h
    rcases h with ⟨c, hc₁, hc₂, hnot⟩
    intro hleast
    apply hnot
    intro x
    have := hleast x
    have hcab : c ≤ a ⊓ b :=
      le_inf hc₁ hc₂
    exact le_trans hcab this
  · intro h
    exact ⟨a ⊓ b, inf_le_left, inf_le_right, h⟩

def separator {α : Type u} [PartialOrder α] (a : α) := { x : α | ¬ meet x a }

prefix:80 "⋆" => separator

def IsSeparable (α : Type u) [PartialOrder α] := ∀ a b : α, separator a = separator b → a = b

def IsStronglySeparable (α : Type u) [PartialOrder α] := ∀ a b : α, separator a ⊆ separator b → a ≤ b

theorem le_imp_separator_superset {α : Type u} [PartialOrder α] {a b : α} (h : a ≤ b) :
    separator b ⊆ separator a := by
  intro x hx
  change ¬ meet x a
  intro hxa
  exact hx (meet_mono_right h hxa)

theorem isStronglySeparable_iff_star_orderEmbedding {α : Type u} [PartialOrder α] :
    IsStronglySeparable α ↔
      ∃ f : α ↪o Set α, (f : α → Set α) = separator := by
  constructor
  · intro h
    have map_rel : ∀ a b : α, separator a ≤ separator b ↔ a ≤ b := by
      intro a b
      constructor
      · intro h_sub
        have h_subset : separator a ⊆ separator b := (Set.le_iff_subset.mpr h_sub)
        exact h a b h_subset
      · intro hab
        have h_sub_ba : separator b ⊆ separator a := le_imp_separator_superset hab
        have hba : b ≤ a := h b a h_sub_ba
        have hab_eq : a = b := le_antisymm hab hba
        simpa [hab_eq]
    let f := OrderEmbedding.ofMapLEIff (fun a => separator a) map_rel
    refine ⟨f, ?_⟩
    rfl
  · intro ⟨f, hf⟩
    intro a b h_sub
    have hle : f a ≤ f b := by
      have h_sub_le : separator a ≤ separator b := h_sub
      have hfa : f a = separator a := congrFun hf a
      have hfb : f b = separator b := congrFun hf b
      simpa [hfa, hfb] using h_sub_le
    exact (OrderEmbedding.le_iff_le f).mp hle
