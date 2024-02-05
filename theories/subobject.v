From category Require Import
                      base
                      setoid
                      category
                      terminal
                      functor
                      limit
                      prod
                      pullback.

Section SubObjectClassifier.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.
  Context {H : @Limit _ C Empty_diagram}.

  Record SubobjectClassifier := {
      subobject_classifier :> C;
      true : EmptyLimit H [⤷] subobject_classifier;
      subobject_classifier_ump1 : ∀ {U X} (f : U [⤷] X),
        Σ! (char : X [~>] subobject_classifier),
        isPullback char true f (projT1 (terminal_proj U));
    }.
End SubObjectClassifier.

Arguments subobject_classifier {_ _ _}.
Notation "'Ω'" := (subobject_classifier) : cat_scope.
