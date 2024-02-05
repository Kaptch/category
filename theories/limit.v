From category Require Import
                      base
                      setoid
                      category
                      functor
                      terminal.

Section Limits.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {J : Category}.
  Context {C : Category}.
  Context (F : J [⇒] C).

  Record Cone :=
    {
      cone_obj :> C;
      cone_nat : (Δ cone_obj) [↣] F;
    }.

  Record ConeArr (A B : Cone) :=
    {
      cone_arr :> cone_obj A [~>] cone_obj B;
      cone_comp : ∀ j, (cone_nat A j) ≡ (cone_nat B j) ∘ cone_arr;
    }.

  Program Definition ConeArrSetoid (A B : Cone) : Setoid :=
    {|
      setoid_carrier := ConeArr A B;
      setoid_eq x y := x ≡ y;
    |}.
  Next Obligation.
    split.
    - intros ?; reflexivity.
    - intros ???; now symmetry.
    - intros ?????; etransitivity; eassumption.
  Qed.

  Program Definition ConeCat : Category :=
    {|
      Obj := Cone;
      Arr A B := ConeArrSetoid A B;
      arrow_id A := {|
                     cone_arr := ı;
                   |};
      arrow_comp _ _ _ := λₛ f, λₛ g, {|
                                        cone_arr := f ∘ g;
                                      |};
    |}.
  Next Obligation.
    intros ??.
    now rewrite arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros X Y Z f g ?.
    rewrite <-arrow_comp_assoc.
    rewrite <-(cone_comp _ _ f).
    now rewrite <-(cone_comp _ _ g).
  Qed.
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl; intros ?; simpl.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    apply arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    apply arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl.
    apply arrow_comp_assoc.
  Qed.

  Record Limit :=
    {
      limit_obj :> Terminal ConeCat;
    }.

  Definition LimitUnique (a b : Limit) : Isomorphism a b := TerminalUnique _ _ _.

End Limits.

Arguments cone_obj {_ _ _}.
Arguments cone_nat {_ _ _}.
Arguments cone_arr {_ _ _ _ _}.
Arguments cone_comp {_ _ _ _ _ _}.
Arguments limit_obj {_ _ _}.

Program Definition ConeReindex {J C : Category} (F G : (J [⇒] C)%functor)
  (eta : (F [↣] G)%functor) (c : ConeCat F) : ConeCat G :=
  {|
    cone_obj := cone_obj c;
    cone_nat := (eta ∘ cone_nat c)%cat;
  |}.
