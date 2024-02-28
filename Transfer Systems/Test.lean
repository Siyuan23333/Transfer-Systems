import Mathlib.Order.Lattice
import Mathlib.Order.Sublattice
import Mathlib.Data.Fintype.Order
import Mathlib.Combinatorics.Catalan

-- Given a lattice (P, ≤),
-- a transfer system on (P,≤) is a sublattice (P,◁) that satisfies
-- 1) refinement: ∀ a, b ∈ P, if a ◁ b, then a ≤ b
-- 2) restrict: ∀ a, b, c ∈ P, if a ◁ b and c ≤ b, then a ∧ c → c
-- Two transfer systems on (P,≤) are equal if they have the same poset structure (I think this is what @[ext] does).
-- QUESTION: are transfer systems sublattices or just sub-posets.

@[ext]
class TransferSystem (P : Type*) [base_struct: Lattice P] extends PartialOrder P where
  refine: ∀ a b : P, le a b → base_struct.le a b
  restrict: ∀ a b c : P, (le a b ∧ base_struct.le c b) → le (base_struct.inf a c) c


-- need to declare that TransferSystem is an instance of PartialOrder

class TransferSystemOnN (n : Nat) extends TransferSystem (Fin (n + 1))
class TransferSystemOnN₁ (n : Nat) [base_struct: Lattice (Fin (n + 1))] extends PartialOrder (Fin (n + 1)) where
  refine: ∀ a b : Fin (n + 1), le a b → base_struct.le a b
  restrict: ∀ a b c : Fin (n + 1), (le a b ∧ base_struct.le c b) → le (base_struct.inf a c) c

-- need to declare that TransferSystemOnN is an instance of TransferSystem

variable (P : Type*) [Lattice P]

-- Example: a transfer system on [n] in the form 0 -> 1 -> ... -> n   n+1
def truncation (n : Nat) : TransferSystemOnN (n := (n + 1)) where
  le := λ x y => (x = y) ∨ (x ≤ y ∧ y ≤ n)
  lt := λ x y => (x < y ∧ y ≤ n)
  le_refl := by
    intro a
    left
    rfl
  le_trans := by
    intro a b c h₁ h₂
    have t₁ : (a = b) ∨ (a ≤ b ∧ b ≤ n) := by exact h₁
    have t₂ : (b = c) ∨ (b ≤ c ∧ c ≤ n) := by exact h₂
    cases t₁ with
    | inr hr =>
      cases t₂ with
      | inr hrr =>
        right
        constructor
        · apply le_trans hr.left hrr.left
        exact hrr.right
      | inl hrl =>
        right
        rw [← hrl]
        exact hr
    | inl hl =>
      cases t₂ with
      | inr hll =>
        right
        rw [hl]
        exact hll
      | inl hlr =>
        left
        rw [hl]
        exact hlr
  lt_iff_le_not_le := by
    intro a b
    constructor
    · intro h
      constructor
      · right
        constructor
        · refine le_of_lt ?mp.left.h.left.a
          exact h.left
        exact h.right
      dsimp
      push_neg
      constructor
      · refine Fin.ne_of_gt ?mp.right.left.h
        exact h.left
      contrapose!
      intro h'
      exact h.left
    simp
    intro h h'
    constructor
    · refine lt_of_not_le ?mpr.left.h
      by_contra h''
      apply h'
      cases h with
      | inr hr =>
        right
        constructor
        · exact h''
        exact le_trans hr.left hr.right
      | inl hl =>
        left
        rw [hl]
    cases h with
    | inr hr =>
      exact hr.right
    | inl hl =>
      push_neg at h'
      by_contra
      apply h'.left
      rw [hl]
  le_antisymm := by
    intro a b
    simp
    intro h h'
    cases h with
    | inr hr =>
      cases h' with
      | inr hrr =>
        apply (LE.le.le_iff_eq hrr.left).mp hr.left
      | inl hrl =>
        rw [hrl]
    | inl hl =>
      exact hl
  refine := by
    intro a b h
    cases h with
    | inr hr =>
      exact hr.left
    | inl hl =>
      exact Eq.le hl
  restrict := by
    intro a b c h
    have t : (a = b) ∨ (a ≤ b ∧ b ≤ n) := by exact h.left
    rw [inf_eq_min]
    cases t with
    | inr tr =>
      right
      constructor
      · exact min_le_right a c
      apply le_trans h.right tr.right
    | inl tl =>
      left
      refine min_eq_right_iff.mpr ?inl.h.a
      rw [tl]
      exact h.right

open TransferSystem
open Nat

theorem lt_n {a b c : Nat} (h₁ : a < b) (h₂ : c ≤ a): a - c < b - c := by
  apply Nat.lt_sub_of_add_lt
  rw [Nat.sub_add_cancel h₂]
  exact h₁

-- Check if a PartialOrder is a TransferSystem
def isTransferSystem {P : Type*} (t : PartialOrder P) [base_struct : Lattice P]: Prop :=
  (∀ a b : P, t.le a b → base_struct.le a b) ∧ (∀ a b c : P, (t.le a b ∧ base_struct.le c b) → t.le (base_struct.inf a c) c)

-- Proposition 18
-- Product of two transfer system
def product {x y : Nat} (X : PartialOrder (Fin (x + 1))) (Y : PartialOrder (Fin (y + 1))) : PartialOrder (Fin (x + y + 3)) where
  le := λ a b =>
    if hX : (a.val < x + 1) ∧ (b.val < x + 1) then
      (X.le {
        val := a.val
        isLt := hX.left
      } {
        val := b.val
        isLt := hX.right
      })
    else if hY : (x + 1 < a.val) ∧ (x + 1 < b.val) then
      (Y.le {
        val := a.val - x - 2
        isLt := by
          have t : y + 1 = (x + y + 3) - (x + 2) := by
            rw [← Nat.sub_sub, Nat.add_comm x y, Nat.add_assoc, Nat.add_comm x 3, ← Nat.add_assoc, Nat.add_sub_self_right]
            exact rfl
          rw [t]
          apply Nat.lt_sub_of_add_lt
          rw [Nat.sub_sub]
          rw [Nat.sub_add_cancel]
          exact a.isLt
          apply Nat.le_of_lt_succ

          linarith
      } {
        val := b.val - x - 2
        isLt := by
          have t : y + 1 = (x + y + 3) - (x + 2) := by
            rw [← Nat.sub_sub, Nat.add_comm x y, Nat.add_assoc, Nat.add_comm x 3, ← Nat.add_assoc, Nat.add_sub_self_right]
            exact rfl
          rw [t]
          apply Nat.lt_sub_of_add_lt
          rw [Nat.sub_sub]
          rw [Nat.sub_add_cancel]
          exact b.isLt
          apply Nat.le_of_lt_succ
          linarith
      })
    else if hO : (a.val = x + 1) then
      (x + 1 < b.val)
    else
      a = b
  lt := λ a b =>
    if hX : (a.val < x + 1) ∧ (b.val < x + 1) then
      (X.lt {
        val := a.val
        isLt := hX.left
      } {
        val := b.val
        isLt := hX.right
      })
    else if hY : (x + 1 < a.val) ∧ (x + 1 < b.val) then
      (Y.lt {
        val := a.val - x - 2
        isLt := by
          have t : y + 1 = (x + y + 3) - (x + 2) := by
            rw [← Nat.sub_sub, Nat.add_comm x y, Nat.add_assoc, Nat.add_comm x 3, ← Nat.add_assoc, Nat.add_sub_self_right]
            exact rfl
          rw [t]
          apply Nat.lt_sub_of_add_lt
          rw [Nat.sub_sub]
          rw [Nat.sub_add_cancel]
          exact a.isLt
          apply Nat.le_of_lt_succ
          linarith
      } {
        val := b.val - x - 2
        isLt := by
          have t : y + 1 = (x + y + 3) - (x + 2) := by
            rw [← Nat.sub_sub, Nat.add_comm x y, Nat.add_assoc, Nat.add_comm x 3, ← Nat.add_assoc, Nat.add_sub_self_right]
            exact rfl
          rw [t]
          apply Nat.lt_sub_of_add_lt
          rw [Nat.sub_sub]
          rw [Nat.sub_add_cancel]
          exact b.isLt
          apply Nat.le_of_lt_succ
          linarith
      })
    else if hO : (a.val = x + 1) then
      (x + 1 < b.val)
    else
      False
  le_refl := by
    intro a
    simp
    have h : (a.val < (x + 1)) ∨ (a.val = (x + 1)) ∨ (a.val < (x + 1)):= by
      apply lt_trichotomy a.val (x + 1)
    refine (ite_prop_iff_or (↑a < x + 1) True).mpr ?_



  le_trans := by
    intro a b c
    simp
    intro h₁ h₂
    rcases h₁ with h₁eq | h₁X | h₁Y | h₁O
    · rw [h₁eq]
      exact h₂
    · rcases h₂ with h₂eq | h₂X | h₂Y | h₂O
      · rw [← h₂eq]
        right
        left
        exact h₁X
      · right
        left
        constructor
        exact h₁X.left
        constructor
        exact h₂X.right.left
        apply X.le_trans a b c h₁X.right.right h₂X.right.right
      · have c : x + 1 < x + 1 := by
          apply LT.lt.trans h₂Y.left h₁X.right.left
        contrapose c
        apply Nat.lt_irrefl
      · have c : x + 1 < x + 1 := by
          nth_rewrite 1 [← h₂O.left]
          exact h₁X.right.left
        contrapose c
        apply Nat.lt_irrefl
    · rcases h₂ with h₂eq | h₂X | h₂Y | h₂O
      · rw [← h₂eq]
        right
        right
        left
        exact h₁Y
      · have c : x + 1 < x + 1 := by
          apply LT.lt.trans h₁Y.right.left h₂X.left
        contrapose c
        apply Nat.lt_irrefl
      · right
        right
        left
        constructor
        exact h₁Y.left
        constructor
        exact h₂Y.right.left
        apply Y.le_trans (a - x - 2) (b - x - 2) (c - x - 2) h₁Y.right.right h₂Y.right.right
      · have c : x + 1 < x + 1 := by
          nth_rewrite 2 [← h₂O.left]
          exact h₁Y.right.left
        contrapose c
        apply Nat.lt_irrefl
    · rcases h₂ with h₂eq | h₂X | h₂Y | h₂O
      · rw [← h₂eq]
        right
        right
        right
        exact h₁O
      · have c : x + 1 < x + 1 := by
          apply LT.lt.trans h₁O.right h₂X.left
        contrapose c
        apply Nat.lt_irrefl
      · right
        right
        right
        constructor
        exact h₁O.left
        exact h₂Y.right.left
      · have c : x + 1 < x + 1 := by
          nth_rewrite 2 [← h₂O.left]
          exact h₁O.right
        contrapose c
        apply Nat.lt_irrefl
  lt_iff_le_not_le := by
    intro a b
    simp
    constructor
    · intro h
      constructor
      · right
        rcases h with hX | hY | hO
        · left
          constructor
          exact hX.left
          constructor
          exact hX.right.left
          apply LT.lt.le hX.right.right
        · right
          left
          constructor
          exact hY.left
          constructor
          exact hY.right.left
          apply LT.lt.le hY.right.right
        · right
          right
          exact hO
      · rcases h with hX | hY | hO
        · push_neg
          constructor
          apply Fin.ne_of_val_ne
          push_neg
          apply (Mathlib.Tactic.Zify.nat_cast_ne b.val a.val).mpr
          apply Ne.symm
          apply LT.lt.ne
          exact hX.right.right
  le_antisymm := sorry


def product₁ {x y : Nat} (X : PartialOrder (Fin (x + 1))) (Y : PartialOrder (Fin (y + 1))) : PartialOrder (Fin (x + y + 3)) where
  le := λ a b => (a = b)
                ∨ ((a.val < x + 1) ∧ (b.val < x + 1) ∧ (X.le a b))
                ∨ ((x + 1 < a.val) ∧ (x + 1 < b.val) ∧ (Y.le (a - x - 2) (b - x - 2)))
                ∨ ((a.val = x + 1) ∧ (x + 1 < b.val))
  lt := λ a b => ((a.val < x + 1) ∧ (b.val < x + 1) ∧ (X.lt a b))
                ∨ ((x + 1 < a.val) ∧ (x + 1 < b.val) ∧ (Y.lt (a - x - 2) (b - x - 2)))
                ∨ ((a.val = x + 1) ∧ (x + 1 < b.val))
  le_refl := by
    intro a
    simp
  le_trans := by
    intro a b c
    simp
    intro h₁ h₂
    rcases h₁ with h₁eq | h₁X | h₁Y | h₁O
    · rw [h₁eq]
      exact h₂
    · rcases h₂ with h₂eq | h₂X | h₂Y | h₂O
      · rw [← h₂eq]
        right
        left
        exact h₁X
      · right
        left
        constructor
        exact h₁X.left
        constructor
        exact h₂X.right.left
        apply X.le_trans a b c h₁X.right.right h₂X.right.right
      · have c : x + 1 < x + 1 := by
          apply LT.lt.trans h₂Y.left h₁X.right.left
        contrapose c
        apply Nat.lt_irrefl
      · have c : x + 1 < x + 1 := by
          nth_rewrite 1 [← h₂O.left]
          exact h₁X.right.left
        contrapose c
        apply Nat.lt_irrefl
    · rcases h₂ with h₂eq | h₂X | h₂Y | h₂O
      · rw [← h₂eq]
        right
        right
        left
        exact h₁Y
      · have c : x + 1 < x + 1 := by
          apply LT.lt.trans h₁Y.right.left h₂X.left
        contrapose c
        apply Nat.lt_irrefl
      · right
        right
        left
        constructor
        exact h₁Y.left
        constructor
        exact h₂Y.right.left
        apply Y.le_trans (a - x - 2) (b - x - 2) (c - x - 2) h₁Y.right.right h₂Y.right.right
      · have c : x + 1 < x + 1 := by
          nth_rewrite 2 [← h₂O.left]
          exact h₁Y.right.left
        contrapose c
        apply Nat.lt_irrefl
    · rcases h₂ with h₂eq | h₂X | h₂Y | h₂O
      · rw [← h₂eq]
        right
        right
        right
        exact h₁O
      · have c : x + 1 < x + 1 := by
          apply LT.lt.trans h₁O.right h₂X.left
        contrapose c
        apply Nat.lt_irrefl
      · right
        right
        right
        constructor
        exact h₁O.left
        exact h₂Y.right.left
      · have c : x + 1 < x + 1 := by
          nth_rewrite 2 [← h₂O.left]
          exact h₁O.right
        contrapose c
        apply Nat.lt_irrefl
  lt_iff_le_not_le := by
    intro a b
    simp
    constructor
    · intro h
      constructor
      · right
        rcases h with hX | hY | hO
        · left
          constructor
          exact hX.left
          constructor
          exact hX.right.left
          apply LT.lt.le hX.right.right
        · right
          left
          constructor
          exact hY.left
          constructor
          exact hY.right.left
          apply LT.lt.le hY.right.right
        · right
          right
          exact hO
      · rcases h with hX | hY | hO
        · push_neg
          constructor
          apply Fin.ne_of_val_ne
          push_neg
          apply (Mathlib.Tactic.Zify.nat_cast_ne b.val a.val).mpr
          apply Ne.symm
          apply LT.lt.ne
          exact hX.right.right
  le_antisymm := sorry

-- For two partialorders, they are transfer systems if and only if their product is a transfer system
theorem product_ts {x y : Nat} (X : PartialOrder (Fin (x + 1))) (Y : PartialOrder (Fin (y + 1))) :
                    (isTransferSystem X) ∧ (isTransferSystem Y) ↔ isTransferSystem (product X Y) := by
  sorry

-- Main theorem
-- theorem: cardinality.(setOfTransferSystems n) = catalan 5± 1

-- Set of all the Transfer System on [n]
def allTSOnN (n : Nat) := Set.univ (α := (TransferSystemOnN n))

#check (Mathlib.Tactic.Zify.nat_cast_ne 1 2).mpr
#check Num.of_nat_cast
