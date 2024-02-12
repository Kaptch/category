From category Require Import
                      base
                      setoid
                      category
                      sets
                      terminal
                      functor
                      limit
                      prod
                      classes.limits
                      subobject.

Section SubobjectClassifier.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Class hasSubobjectClassifier (C : Category) `{!hasTerminal C} :=
    {
      has_subobject_classifier : SubobjectClassifier;
    }.

End SubobjectClassifier.

Notation "'Ω' '@' C" := (@has_subobject_classifier C _) (at level 50) : cat_scope.
