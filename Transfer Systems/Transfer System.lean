import Mathlib.Order.Lattice
import Mathlib.Order.Sublattice
import Mathlib.Data.Fintype.Order
import Mathlib.Combinatorics.Catalan
import Mathlib.Logic.Basic

-- Given a lattice (P, ≤),
-- a transfer system on (P,≤) is a partial order (P,◁) that satisfies
-- 1) refinement: ∀ a, b ∈ P, if a ◁ b, then a ≤ b
-- 2) restrict: ∀ a, b, c ∈ P, if a ◁ b and c ≤ b, then a ∧ c → c
-- Two transfer systems on (P,≤) are equal if they have the same poset structure (I think this is what @[ext] does).
-- QUESTION: are transfer systems sublattices or just sub-posets.

set_option maxHeartbeats 1000000

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

-- Check if a PartialOrder is a TransferSystem
@[simp]
def isTransferSystem {P : Type*} (t : PartialOrder P) [base_struct : Lattice P]: Prop :=
  (∀ {a b : P}, t.le a b → base_struct.le a b) ∧ (∀ {a b c : P}, (t.le a b ∧ base_struct.le c b) → t.le (base_struct.inf a c) c)

-- Check if a PartialOrder on [n] is a TransferSystem on [n]
@[simp]
def isTransferSystemOnN {n : Nat} (t : PartialOrder (Fin n)) : Prop :=
  (∀ {a b : Fin n}, t.le a b → a ≤ b) ∧ (∀ {a b c : Fin n}, (t.le a b ∧ c.val ≤ b.val) → t.le (min a c) c)

-- Proposition 18
-- Product of two transfer system
@[simp]
def product {x y : Nat} (X : PartialOrder (Fin (x + 1))) (Y : PartialOrder (Fin (y + 1))) : PartialOrder (Fin (x + y + 3)) where
  le := λ a b =>
    if hX : (a.val < x + 1) ∧ (b.val < x + 1) then
      have a' := Fin.mk (n := x + 1) (val := a.val) (isLt := hX.left)
      have b' := Fin.mk (n := x + 1) (val := b.val) (isLt := hX.right)
      (X.le a' b')
    else if hY : (x + 1 < a.val) ∧ (x + 1 < b.val) then
      have a' := Fin.mk (n := y + 1) (val := a.val - x - 2) (isLt := by
        have : y + 1 = (x + y + 3) - (x + 2) := by
            rw [← Nat.sub_sub, Nat.add_comm x y, Nat.add_assoc, Nat.add_comm x 3, ← Nat.add_assoc, Nat.add_sub_self_right]
            exact rfl
        rw [this]
        apply Nat.lt_sub_of_add_lt
        rw [Nat.sub_sub]
        rw [Nat.sub_add_cancel]
        exact a.isLt
        apply Nat.le_of_lt_succ
        linarith
        )
      have b' := Fin.mk (n := y + 1) (val := b.val - x - 2) (isLt := by
        have : y + 1 = (x + y + 3) - (x + 2) := by
            rw [← Nat.sub_sub, Nat.add_comm x y, Nat.add_assoc, Nat.add_comm x 3, ← Nat.add_assoc, Nat.add_sub_self_right]
            exact rfl
        rw [this]
        apply Nat.lt_sub_of_add_lt
        rw [Nat.sub_sub]
        rw [Nat.sub_add_cancel]
        exact b.isLt
        apply Nat.le_of_lt_succ
        linarith
        )
      (Y.le a' b')
    else if hO : (a.val = x + 1) then
      (x + 1 ≤ b.val)
    else
      a = b
  lt := λ a b =>
    if hX : (a.val < x + 1) ∧ (b.val < x + 1) then
      have a' := Fin.mk (n := x + 1) (val := a.val) (isLt := hX.left)
      have b' := Fin.mk (n := x + 1) (val := b.val) (isLt := hX.right)
      (X.lt a' b')
    else if hY : (x + 1 < a.val) ∧ (x + 1 < b.val) then
      have a' := Fin.mk (n := y + 1) (val := a.val - x - 2) (isLt := by
        have : y + 1 = (x + y + 3) - (x + 2) := by
            rw [← Nat.sub_sub, Nat.add_comm x y, Nat.add_assoc, Nat.add_comm x 3, ← Nat.add_assoc, Nat.add_sub_self_right]
            exact rfl
        rw [this]
        apply Nat.lt_sub_of_add_lt
        rw [Nat.sub_sub]
        rw [Nat.sub_add_cancel]
        exact a.isLt
        apply Nat.le_of_lt_succ
        linarith
        )
      have b' := Fin.mk (n := y + 1) (val := b.val - x - 2) (isLt := by
        have : y + 1 = (x + y + 3) - (x + 2) := by
            rw [← Nat.sub_sub, Nat.add_comm x y, Nat.add_assoc, Nat.add_comm x 3, ← Nat.add_assoc, Nat.add_sub_self_right]
            exact rfl
        rw [this]
        apply Nat.lt_sub_of_add_lt
        rw [Nat.sub_sub]
        rw [Nat.sub_add_cancel]
        exact b.isLt
        apply Nat.le_of_lt_succ
        linarith
        )
      (Y.lt a' b')
    else if hO : (a.val = x + 1) then
      (x + 1 < b.val)
    else
      False
  le_refl := by
    intro a
    simp
    split
    · exact trivial
    split
    · exact trivial
    split
    · linarith
    · exact trivial
  le_trans := by
    intro a b c
    simp
    intro h₁ h₂
    split
    · split at h₁
      · split at h₂
        · exact X.le_trans {val := a.val, isLt := by linarith : Fin (x + 1)}
            {val := b.val, isLt := by linarith : Fin (x + 1)}
            {val := c.val, isLt := by linarith : Fin (x + 1)}
            h₁ h₂
        split at h₂
        · have : x + 1 < x + 1 := by
            linarith
          by_contra
          exact (lt_self_iff_false (x + 1)).mp this
        split at h₂
        · have : x + 1 < x + 1 := by
            linarith
          by_contra
          exact (lt_self_iff_false (x + 1)).mp this
        · have : {val := b.val, isLt := by linarith : Fin (x + 1)}
            = {val := c.val, isLt := by linarith : Fin (x + 1)} := by
            exact Fin.eq_of_val_eq (Fin.val_eq_of_eq (n := x + y + 3) h₂)
          rw [← this]
          exact h₁
      split at h₁
      · have : x + 1 < x + 1 := by
          linarith
        by_contra
        exact (lt_self_iff_false (x + 1)).mp this
      split at h₁
      · have : x + 1 < x + 1 := by
          linarith
        by_contra
        exact (lt_self_iff_false (x + 1)).mp this
      · sorry
    sorry
  lt_iff_le_not_le := sorry
  le_antisymm := by
    intro a b
    simp
    intro h₁ h₂
    split at h₁
    · split at h₂
      · apply Fin.eq_of_val_eq
        apply Fin.val_eq_of_eq (n:= x + 1) ((LE.le.ge_iff_eq h₁).mp h₂)
      split at h₂
      · linarith
      split at h₂
      · linarith
      · rw [h₂]
    split at h₁
    · split at h₂
      · linarith
      split at h₂
      · have : a.val - x - 2 = b.val - x - 2 := by
          apply Fin.val_eq_of_eq (n:= y + 1) ((LE.le.ge_iff_eq h₁).mp h₂)
        apply Fin.eq_of_val_eq
        sorry
      split at h₂
      · linarith
      · rw [h₂]
    split at h₁
    · split at h₂
      · linarith
      split at h₂
      · linarith
      split at h₂
      · have : b.val = x + 1 := by assumption
        apply Fin.eq_of_val_eq
        rw [this]
        assumption
      · rw [h₂]
    · exact h₁


-- For two partial orders, they are transfer systems if and only if their "product" is a transfer system
theorem product_ts {x y : Nat} (X : PartialOrder (Fin (x + 1))) (Y : PartialOrder (Fin (y + 1))) (Z : PartialOrder (Fin (x + y + 3))) (h : Z = product X Y):
                    (isTransferSystemOnN X) ∧ (isTransferSystemOnN Y) ↔ (isTransferSystemOnN Z) := by
  constructor
  · intro h'
    have hX : isTransferSystemOnN X := by exact h'.left
    have hY : isTransferSystemOnN Y := by exact h'.right
    rw [h]
    constructor
    · intro a b h''
      simp at h''
      split at h''
      · simp [isTransferSystemOnN] at hX
        exact hX.left h''
      split at h''
      · simp [isTransferSystemOnN] at hY
        have : a.val - x - 2 ≤ b.val - x - 2 := by
          exact hY.left h''
        apply Fin.val_fin_le.mp
        sorry
      split at h''
      · have : a.val = x + 1 := by assumption
        apply Fin.val_fin_le.mp
        rw [this]
        assumption
      · apply Fin.val_fin_le.mp
        apply Eq.le
        apply Fin.val_eq_of_eq h''
    · intro a b c h''
      simp only [product] at h''
      have case : (min a c = a ∧ a ≤ c) ∨ (min a c = c ∧ c < a) := by
        exact min_cases a c
      rcases case with ha | hc
      · simp
        have : a.val ≤ c.val := by
          exact Fin.le_iff_val_le_val.mpr ha.right
        split
        · split at h''
          · have : X.le {val := a.val, isLt := by linarith : Fin (x + 1)} {val := b.val, isLt := by linarith : Fin (x + 1)}
              ∧ {val := c.val, isLt := by linarith : Fin (x + 1)}.val ≤ {val := b.val, isLt := by linarith : Fin (x + 1)}.val := by
              exact h''
            exact hX.right this
          split at h''
          · have : x + 1 < c.val := by
              linarith
            have : x + 1 < x + 1 := by
              linarith
            by_contra
            exact (lt_self_iff_false (x + 1)).mp this
          split at h''
          · have : x + 1 ≤ c.val := by
              linarith
            have : x + 1 < x + 1 := by
              linarith
            by_contra
            exact (lt_self_iff_false (x + 1)).mp this
          · have : c.val ≤ a.val := by
              rw [h''.left]
              exact h''.right
            have : c.val = a.val := by
              linarith
            have : min a.val c.val = c.val := by
              rw [this]
              exact Nat.min_self a.val
            have : {val := min a.val c.val, isLt := by linarith : Fin (x + 1)}
              = {val := c.val, isLt := by linarith : Fin (x + 1)} := by
              exact Fin.mk_eq_mk.mpr this
            rw [this]
        split
        · split at h''
          · have : x + 1 < x + 1 := by
              linarith
            by_contra
            exact (lt_self_iff_false (x + 1)).mp this
          split at h''
          · have : {val := (min a.val c.val) - x - 2, isLt := by sorry : Fin (y + 1)}
              = min {val := a.val - x - 2, isLt := by sorry : Fin (y + 1)}
              {val := c.val - x - 2, isLt := by sorry : Fin (y + 1)} := by
              sorry
            rw [this]
            have : Y.le {val := a.val - x - 2, isLt := by sorry : Fin (y + 1)} {val := b.val - x - 2, isLt := by sorry : Fin (y + 1)}
              ∧ {val := c.val - x - 2, isLt := by sorry : Fin (y + 1)}.val ≤ {val := b.val - x - 2, isLt := by sorry : Fin (y + 1)}.val := by
              sorry
            exact hY.right this
          split at h''
          · have : x + 1 < x + 1 := by
              linarith
            by_contra
            exact (lt_self_iff_false (x + 1)).mp this
          · have : c.val ≤ a.val := by
              rw [h''.left]
              exact h''.right
            have : c.val = a.val := by
              linarith
            have : min a.val c.val = c.val := by
              rw [this]
              exact Nat.min_self a.val
            have : {val := min a.val c.val - x - 2, isLt := by sorry : Fin (y + 1)}
              = {val := c.val - x - 2, isLt := by sorry : Fin (y + 1)} := by
              apply Fin.mk_eq_mk.mpr
              rw [this]
            rw [this]
        split
        · have : min a.val c.val = x + 1 := by assumption
          rw [← this]
          exact Nat.min_le_right a.val c.val
        · split at h''
          · sorry
          split at h''
          · sorry
          split at h''
          · sorry
          · rw [h''.left]
            exact h''.right
      · rw [hc.left]
        exact (product X Y).le_refl c
· sorry


-- Main theorem
-- theorem: cardinality.(setOfTransferSystems n) = catalan 5± 1

-- Set of all the Transfer System on [n]
def allTSOnN (n : Nat) := Set.univ (α := (TransferSystemOnN n))
