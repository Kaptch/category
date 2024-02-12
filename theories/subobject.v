From category Require Import
                      base
                      setoid
                      category
                      terminal
                      functor
                      limit
                      prod
                      pullback
                      classes.limits.

Section SubObjectClassifier.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.
  Context `{hasTerminal C}.

  Record SubobjectClassifier := {
      subobject_classifier :> C;
      true : 𝟙 @ C [⤷] subobject_classifier;
      subobject_classifier_ump : ∀ {U X} (f : U [⤷] X),
        Σ! (char : X [~>] subobject_classifier),
        isPullback char true f (! @ C);
    }.
End SubObjectClassifier.

Arguments subobject_classifier {_ _ _}.
