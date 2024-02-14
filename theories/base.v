Require Export Utf8.
Require Export RelationClasses Equivalence Morphisms Basics Setoid.
Require Export Coq.Init.Logic.
Require Export Coq.Structures.Equalities.
Require Export Coq.Logic.Eqdep_dec Coq.Logic.ChoiceFacts.

Global Set Default Goal Selector "!".
Global Set Default Proof Using "Type".
Global Set Universe Polymorphism.
Global Unset Intuition Negation Unfolding.
Global Unset Universe Minimization ToSet.
Global Unset Transparent Obligations.
Global Obligation Tactic := idtac.

Global Transparent compose.

#[projections(primitive=yes)]
  Record seal {A} (f : A) := { unseal : A; seal_eq : unseal = f }.
Global Arguments unseal {_ _} _ : assert.
Global Arguments seal_eq {_ _} _ : assert.

Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
Global Hint Mode Inhabited ! : typeclass_instances.
Global Arguments populate {_} _ : assert.

Global Instance InhabitedUnit : Inhabited unit.
Proof.
  now constructor.
Qed.

Global Instance InhabitedBool : Inhabited bool.
Proof.
  constructor; apply true.
Qed.

Section Decision.
  Class Decision (P : Prop) := decide : {P} + {¬P}.
  Global Hint Mode Decision ! : typeclass_instances.
  Global Arguments decide _ {_} : simpl never, assert.

  Class RelDecision {A B} (R : A → B → Prop) :=
    decide_rel x y :> Decision (R x y).
  Global Hint Mode RelDecision ! ! ! : typeclass_instances.
  Global Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.

  Notation EqDecision A := (RelDecision (@eq A)).
End Decision.

Notation EqDecision A := (RelDecision (@eq A)).

Global Instance EqDecisionBool : EqDecision bool.
Proof.
  intros [|] [|]; [now left | now right | now right | now left].
Qed.

Variant squash (A : Type) : SProp :=
  | squash_intro: A → squash A.

Definition proj_ex1 {A} {P : A → _} : (exists x : A, P x) → squash A.
Proof.
  destruct 1; now constructor.
Defined.
