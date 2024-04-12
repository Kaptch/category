From category Require Import
  base
  setoid
  category
  sets
  terminal
  functor
  limit
  colimit
  prod
  exp
  pullback
  subobject
  classes.enrichment
  classes.subobject
  classes.limits
  classes.colimits
  classes.exp
  instances.sets
  instances.presheaf
  internal_lang.presheaf.

From stdpp Require Import
  base.

From category Require Import
  ordinals.set_ordinals
  ordinals.ord_stepindex
  ordinals.set_model
  ordinals.set_sets
  ordinals.arithmetic
  ordinals.set_functions.

Section Ord.
  Context (α : Ord).
  Definition idx := { β : Ord | β ≺≺ α }.

  Program Definition OrdCatArrSetoid (A B : idx) : Setoid :=
    {|
      setoid_carrier := (proj1_sig A) ⪯⪯ (proj1_sig B);
      setoid_eq (X Y : (proj1_sig A) ⪯⪯ (proj1_sig B)) := X = Y;
    |}.

  Program Definition OrdCat : Category :=
    {|
      Obj := idx;
      Arr A B := OrdCatArrSetoid A B;
      arrow_id A := reflexivity _;
      arrow_comp A B C := (λₛ f, λₛ g, transitivity g f)%setoid;
    |}.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros ?.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.

End Ord.

Opaque arrow_id.
Opaque arrow_comp.

Section ToposOfTrees.
  Local Open Scope zf_scope.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context (α : Ord).

  Definition tree := PSh ((OrdCat α)).
End ToposOfTrees.
