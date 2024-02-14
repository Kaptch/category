From category Require Import
  base
  setoid
  category.

Section Initial.
  Local Open Scope cat_scope.

  Context (C : Category).

  Record Initial :=
    {
      initial_obj :> C;
      initial_proj {X : C} : Σ! (_ : (initial_obj [~>] X)), True;
    }.

  Program Definition InitialUnique (a b : Initial) : Isomorphism a b :=
    {|
      iso1 := projT1 (@initial_proj a b);
      iso2 := projT1 (@initial_proj b a);
    |}.
  Next Obligation.
    intros.
    rewrite <-(snd (projT2 (@initial_proj a a)) (projT1 (initial_proj b)
                                                   ∘ projT1 (initial_proj a)) I).
    rewrite <-(snd (projT2 (@initial_proj a a)) ı I).
    reflexivity.
  Qed.
  Next Obligation.
    intros.
    rewrite <-(snd (projT2 (@initial_proj b b)) (projT1 (initial_proj a)
                                                   ∘ projT1 (initial_proj b)) I).
    rewrite <-(snd (projT2 (@initial_proj b b)) ı I).
    reflexivity.
  Qed.
End Initial.

Arguments initial_obj {_}.
Arguments initial_proj {_ _}.
