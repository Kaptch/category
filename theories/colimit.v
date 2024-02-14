From category Require Import
                      base
                      setoid
                      category
                      functor
                      initial.

Section Colimits.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {J : Category}.
  Context {C : Category}.
  Context (F : J [⇒] C).

  Record Cocone :=
    {
      cocone_obj :> C;
      cocone_nat : F [↣] (Δ cocone_obj);
    }.

  Record CoconeArr (A B : Cocone) :=
    {
      cocone_arr :> cocone_obj A [~>] cocone_obj B;
      cocone_comp : ∀ j, cocone_arr ∘ (cocone_nat A j) ≡ (cocone_nat B j);
    }.

  Program Definition CoconeArrSetoid (A B : Cocone) : Setoid :=
    {|
      setoid_carrier := CoconeArr A B;
      setoid_eq x y := x ≡ y;
    |}.
  Next Obligation.
    split.
    - intros ?; reflexivity.
    - intros ???; now symmetry.
    - intros ?????; etransitivity; eassumption.
  Qed.

  Program Definition CoconeCat : Category :=
    {|
      Obj := Cocone;
      Arr A B := CoconeArrSetoid A B;
      arrow_id A := {|
                     cocone_arr := ı;
                   |};
      arrow_comp _ _ _ := λₛ f, λₛ g, {|
                                        cocone_arr := f ∘ g;
                                      |};
    |}.
  Next Obligation.
    intros ??.
    now rewrite arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros X Y Z f g ?.
    rewrite arrow_comp_assoc.
    rewrite <-(cocone_comp _ _ f).
    now rewrite <-(cocone_comp _ _ g).
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

  Record Colimit :=
    {
      colimit_obj :> Initial CoconeCat;
    }.

  Definition ColimitUnique (a b : Colimit) : Isomorphism a b := InitialUnique _ _ _.

End Colimits.

Arguments cocone_obj {_ _ _}.
Arguments cocone_nat {_ _ _}.
Arguments cocone_arr {_ _ _ _ _}.
Arguments cocone_comp {_ _ _ _ _ _}.
Arguments colimit_obj {_ _ _}.

Program Definition CoconeReindex {J C : Category} (F G : (J [⇒] C)%functor)
  (eta : (F [↣] G)%functor) (c : CoconeCat G) : CoconeCat F :=
  {|
    cocone_obj := cocone_obj c;
    cocone_nat := (cocone_nat c ∘ eta)%cat;
  |}.
