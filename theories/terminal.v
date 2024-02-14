From category Require Import
  base
  setoid
  category.

Section Terminal.
  Local Open Scope cat_scope.

  Context (C : Category).

  Record Terminal :=
    {
      terminal_obj :> C;
      terminal_proj {X : C} : Σ! (_ : (X [~>] terminal_obj)), True;
    }.

  Program Definition TerminalUnique (a b : Terminal) : Isomorphism a b :=
    {|
      iso1 := projT1 (@terminal_proj b a);
      iso2 := projT1 (@terminal_proj a b);
    |}.
  Next Obligation.
    intros.
    rewrite <-(snd (projT2 (@terminal_proj a a)) (projT1 (terminal_proj a)
                                                   ∘ projT1 (terminal_proj b)) I).
    rewrite <-(snd (projT2 (@terminal_proj a a)) ı I).
    reflexivity.
  Qed.
  Next Obligation.
    intros.
    rewrite <-(snd (projT2 (@terminal_proj b b)) (projT1 (terminal_proj b)
                                                   ∘ projT1 (terminal_proj a)) I).
    rewrite <-(snd (projT2 (@terminal_proj b b)) ı I).
    reflexivity.
  Qed.
End Terminal.

Arguments terminal_obj {_}.
Arguments terminal_proj {_ _}.
