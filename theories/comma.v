From category Require Import
                      base
                      setoid
                      category
                      functor.

Section Comma.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {A B C : Category}.
  Context (S : A [⇒] C).
  Context (T : B [⇒] C).

  Record CommaObj := {
      comma_obj1 : A;
      comma_obj2 : B;
      comma_obj12 : S comma_obj1 [~>] T comma_obj2;
    }.

  Record CommaArr (x y : CommaObj) := {
      comma_arr1 : comma_obj1 x [~>] comma_obj1 y;
      comma_arr2 : comma_obj2 x [~>] comma_obj2 y;
      comma_arr12 : comma_obj12 y ∘ fmap S comma_arr1 ≡ fmap T comma_arr2 ∘ comma_obj12 x;
    }.

  Program Definition CommaArrSetoid (x y : CommaObj) : Setoid :=
    {|
      setoid_carrier := CommaArr x y;
      setoid_eq t s := comma_arr1 _ _ t ≡ comma_arr1 _ _ s
                       ∧ comma_arr2 _ _ t ≡ comma_arr2 _ _ s;
    |}.
  Next Obligation.
    intros.
    split.
    - intros ?; split; reflexivity.
    - intros ???; split; now symmetry.
    - intros ??? [? ?] [? ?]; split; etransitivity; eassumption.
  Qed.

  Program Definition CommaCat : Category :=
    {|
      Obj := CommaObj;
      Arr x y := CommaArrSetoid x y;
      arrow_id x := {| comma_arr1 := ı; comma_arr2 := ı |};
      arrow_comp _ _ _ := λₛ f, λₛ g,
        {|
          comma_arr1 := comma_arr1 _ _ f ∘ comma_arr1 _ _ g;
          comma_arr2 := comma_arr2 _ _ f ∘ comma_arr2 _ _ g; |};
    |}.
  Next Obligation.
    intros.
    now rewrite !fmap_id, arrow_comp_id_l, arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros.
    rewrite !fmap_comp.
    rewrite !arrow_comp_assoc.
    rewrite <-!comma_arr12.
    rewrite <-!fmap_comp.
    rewrite <-!arrow_comp_assoc.
    rewrite <-!comma_arr12.
    rewrite !fmap_comp.
    rewrite !arrow_comp_assoc.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    split; f_equiv; apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros G.
    split; do 2 f_equiv; apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    now rewrite !arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    now rewrite !arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite !arrow_comp_assoc.
    now split.
  Qed.
End Comma.
