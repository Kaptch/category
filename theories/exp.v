From category Require Import
                      base
                      setoid
                      category
                      functor
                      terminal
                      limit
                      prod
                      classes.limits.

Section Exp.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.
  Context {bp : hasBinaryProducts C}.

  Record Exp (X Y : C) :=
    {
      exp_obj :> C;
      eval : (exp_obj ×ₒ Y @ C) [~>] X;
      exp_ump : ∀ (Z' : C) (eval' : (Z' ×ₒ Y @ C) [~>] X),
        Σ! f : (Z' [~>] exp_obj),
        eval' ≡
          eval
          ∘ ⟨ f ×ₐ ı ⟩;
    }.

End Exp.

Arguments eval {_ _ _ _ _}.
