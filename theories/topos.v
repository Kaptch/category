From category Require Import
  base
  setoid
  category
  terminal
  functor
  limit
  prod
  pullback
  subobject.

Section Topos.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.

  Record Topos := {
    }.
End Topos.
