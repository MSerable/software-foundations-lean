-- Rel: Properties of Relations
--
-- https://softwarefoundations.cis.upenn.edu/lf-current/Rel.html

-- # Relations
def Relation (X : Type) := X → X → Prop

#print Nat.le -- protected inductive Nat.le : Nat → Nat → Prop
#check (Nat.le : Nat → Nat → Prop) -- Nat.le : Nat → Nat → Prop
#check (Nat.le : Relation Nat) -- Nat.le : Relation Nat

-- # Basic Properties
-- ## Partial Functions
def PartialFunction {X : Type} (R : Relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

inductive NextNat : Nat → Nat → Prop where
  | nn (n : Nat) : NextNat n (Nat.succ n)

theorem next_nat_partial_function : PartialFunction NextNat := by
  intro x y1 y2 h1 h2
  cases h1
  cases h2
  rfl

theorem le_not_a_partial_function : ¬(PartialFunction Nat.le) := by
  intro Hc
  have Nonsense : 0 = 1 := by
    apply Hc 0 0 1
    · exact Nat.le.refl
    · exact Nat.le.step Nat.le.refl
  contradiction

-- ### Exercise: 2 stars, standard, optional (total_relation_not_partial_function)
inductive TotalRelation : Nat → Nat → Prop where
  /- FILL IN HERE -/

theorem total_relation_not_partial_function : ¬(PartialFunction TotalRelation) := by
  /- FILL IN HERE -/
  sorry

-- ### Exercise: 2 stars, standard, optional (empty_relation_partial_function)
inductive EmptyRelation : Nat → Nat → Prop where
  /- FILL IN HERE -/

theorem empty_relation_partial_function : PartialFunction EmptyRelation := by
  /- FILL IN HERE -/
  sorry

-- ## Reflexive Relations
def Reflexive {X : Type} (R : Relation X) :=
  ∀ a : X, R a a

theorem le_reflexive : Reflexive Nat.le := by
  intro n
  apply Nat.le_refl

-- ## Transitive Relations
def Transitive {X : Type} (R : Relation X) :=
  ∀ a b c : X, R a b → R b c → R a c

theorem le_trans : Transitive Nat.le := by
  intro n m o Hnm Hmo
  induction Hmo with
  | refl =>
    exact Hnm
  | step _ IHHmo =>
    apply Nat.le_succ_of_le
    exact IHHmo

theorem lt_trans : Transitive Nat.lt := by
  intro n m o Hnm Hmo
  have Hnm := Nat.le_succ_of_le Hnm
  apply le_trans (b := m.succ)
  · exact Hnm
  · exact Hmo

-- ### Exercise: 2 stars, standard, optional (le_trans_hard_way)
theorem lt_trans' : Transitive Nat.lt := by
  unfold Nat.lt
  unfold Transitive
  intro n m o Hnm Hmo
  /- FILL IN HERE -/
  sorry

-- ### Exercise: 2 stars, standard, optional (lt_trans'')
theorem lt_trans'' : Transitive Nat.lt := by
  /- FILL IN HERE -/
  sorry

theorem le_Sn_le : ∀ n m, Nat.succ n ≤ m → n ≤ m := by
  intro n m h
  refine Nat.le_trans ?_ h
  exact Nat.le.step Nat.le.refl

-- ### Exercise: 1 star, standard, optional (le_S_n)
theorem le_S_n : ∀ n m, Nat.succ n ≤ Nat.succ m → n ≤ m := by
  /- FILL IN HERE -/
  sorry

-- Exercise: 2 stars, standard, optional (le_Sn_n_inf)
-- Provide an informal proof of the following theorem:
-- Theorem: For every n, ¬ (S n ≤ n)
/-
Proof:
  FILL IN HERE
-/

-- ### Exercise: 1 star, standard, optional (le_Sn_n)
theorem le_Sn_n : ∀ n, ¬(Nat.succ n ≤ n) := by
  /- FILL IN HERE -/
  sorry

-- ## Symmetric and Antisymmetric Relations
def Symmetric {X : Type} (R : Relation X) :=
  ∀ a b : X, R a b → R b a

-- ### Exercise: 2 stars, standard, optional (le_not_symmetric)
theorem le_not_symmetric : ¬(Symmetric Nat.le) := by
  /- FILL IN HERE -/
  sorry

def Antisymmetric {X : Type} (R : Relation X) :=
  ∀ a b : X, R a b → R b a → a = b

-- ### Exercise: 2 stars, standard, optional (le_antisymmetric)
theorem le_antisymmetric : Antisymmetric Nat.le := by
  /- FILL IN HERE -/
  sorry

-- ### Exercise: 2 stars, standard, optional (le_step)
theorem le_step : ∀ n m p, n < m → m ≤ Nat.succ p → n ≤ p := by
  /- FILL IN HERE -/
  sorry

-- ## Equivalence Relations
-- Equivalence is placed in the Rel namespace to avoid a collision with Lean's built-in `Init.Core.Equivalence`.
namespace Rel

def Equivalence {X : Type} (R : Relation X) :=
  Reflexive R ∧ Symmetric R ∧ Transitive R

end Rel

-- ## Partial Orders and Preorders
def Order {X : Type} (R : Relation X) :=
  Reflexive R ∧ Antisymmetric R ∧ Transitive R

def Preorder {X : Type} (R : Relation X) :=
  Reflexive R ∧ Transitive R

theorem le_order : Order Nat.le := by
  constructor
  · exact Nat.le_refl
  · constructor
    · exact fun _ _ => Nat.le_antisymm
    · exact fun _ _ _ => Nat.le_trans
  
-- # Reflexive, Transitive Closure
inductive ClosReflTrans {X : Type} (R : Relation X) : Relation X where
  | rt_step {x y : X} (H : R x y) : ClosReflTrans R x y
  | rt_refl (x : X) : ClosReflTrans R x x
  | rt_trans {x y z : X} (Hxy : ClosReflTrans R x y) (Hyz : ClosReflTrans R y z) : ClosReflTrans R x z

theorem next_nat_closure_is_le : ∀ n m, n ≤ m ↔ ClosReflTrans NextNat n m := by
  intro n m
  apply Iff.intro
  · intro H
    induction H with
    | refl => apply ClosReflTrans.rt_refl
    | step _ ih =>
      apply ClosReflTrans.rt_trans ih
      apply ClosReflTrans.rt_step
      constructor
  · intro H
    induction H with
    | rt_step H =>
      cases H
      apply Nat.le.step
      apply Nat.le.refl
    | rt_refl =>
      apply Nat.le.refl
    | rt_trans _ _ ih1 ih2 =>
      exact Nat.le_trans ih1 ih2

inductive ClosReflTrans1n {X : Type} (R : Relation X) : X → X → Prop where
  | rt1n_refl : ClosReflTrans1n R x x
  | rt1n_trans {y z : X} (Hxy : R x y) (Hrest : ClosReflTrans1n R y z) : ClosReflTrans1n R x z

theorem rsc_R : ∀ (X : Type) (R : Relation X) (x y : X), R x y → ClosReflTrans1n R x y := by
  intro X R x y H
  apply ClosReflTrans1n.rt1n_trans H
  apply ClosReflTrans1n.rt1n_refl

-- ### Exercise: 2 stars, standard, optional (rsc_trans)
theorem rsc_trans : ∀ (X : Type) (R : Relation X) (x y z : X),
  ClosReflTrans1n R x y → ClosReflTrans1n R y z → ClosReflTrans1n R x z := by
  /- FILL IN HERE -/
  sorry

-- ### Exercise: 3 stars, standard, optional (rtc_rsc_coincide)
theorem rtc_rsc_coincide : ∀ (X : Type) (R : Relation X) (x y : X),
  ClosReflTrans R x y ↔ ClosReflTrans1n R x y := by
  /- FILL IN HERE -/
  sorry
