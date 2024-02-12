From category Require Import
  base
  setoid
  category
  sets.

Section Functor.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.

  Polymorphic Record Functor (C : Category) (D : Category) :=
    {
      FO :> C → D;
      fmap {A B} : ((A [~>] B)%cat [→] (FO A [~>] FO B)%cat)%setoid;
      fmap_id {A} : fmap (arrow_id A) ≡ ı;
      fmap_comp {A B C} {f : B [~>] C} {g : A [~>] B}
      : fmap (f ∘ g) ≡ fmap f ∘ fmap g;
    }.

  Program Definition constantFunc (C : Category) (D : Category) (d : D) : Functor C D :=
    {|
      FO X := d;
      fmap A B := λₛ _, ı;
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    now rewrite arrow_comp_id_l.
  Qed.
End Functor.

Arguments FO {_ _}.
Arguments fmap {_ _} _ {_ _}.
Arguments fmap_id {_ _ _}.
Arguments fmap_comp {_ _ _ _ _ _}.
Arguments constantFunc {_ _}.

Declare Scope functor_scope.
Delimit Scope functor_scope with functor.

Notation "a [⇒] b" := (Functor a b) (at level 70, right associativity)
    : functor_scope.
Notation "'Δ' x" := (constantFunc x) (at level 40) : functor_scope.

Section NatTrans.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C D : Category}.
  Context (F G : C [⇒] D).

  Polymorphic Record NatTrans :=
    {
      eta {X : C} :> (F X [~>] G X)%cat;
      eta_comp {X Y : C} {f : X [~>] Y} : eta ∘ fmap F f ≡ fmap G f ∘ eta;
    }.

End NatTrans.

Arguments NatTrans {_ _}.
Arguments eta {_ _ _ _}.
Arguments eta_comp {_ _ _ _}.

Notation "'η' F" := (eta F) (at level 40) : functor_scope.
Notation "'λₙ' x , e" := ({| eta x := e |})
                           (at level 120, x binder, no associativity)
    : functor_scope.
Notation "'λₙ' x '::' t , e" := ({| eta (x : t%type) := e |})
                                 (at level 120, x binder, no associativity)
    : functor_scope.

Section Discrete.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.

  Context (C : Type).
  Context `{!EqDecision C}.

  Program Definition DiscreteCat : Category :=
    {|
      Obj := C;
      Arr A B := [ A = B ];
      arrow_id A := eq_refl;
      arrow_comp _ _ _ := λₛ f, λₛ g, eq_trans g f;
    |}.
  Next Obligation.
    now intros ? ? ? -> ->.
  Qed.
  Next Obligation.
    intros; simpl.
    intros G.
    erewrite UIP_dec; [reflexivity | assumption].
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    unfold eq_trans.
    now destruct f.
  Qed.
  Next Obligation.
    intros; simpl.
    destruct f, g, h; now simpl.
  Qed.

  Program Definition DiscreteFun (D : Category) (f : C → D)
    : (DiscreteCat [⇒] D)%functor :=
    {|
      FO X := f X;
      fmap A B := λₛ g, match g in (_ = c) return (f A [~>] f c)%cat
                        with | eq_refl => ı%cat
                        end
    |}.
  Next Obligation.
    intros; simpl in *.
    rewrite H, a₂.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros ? ? ? ? ? [] []; simpl.
    rewrite arrow_comp_id_l.
    reflexivity.
  Qed.

End Discrete.

Arguments DiscreteCat _ {_}.
Arguments DiscreteFun {_ _ _}.

Notation "'⌊' A '⌋'" := (DiscreteCat A) (at level 40) : cat_scope.

Section FunCat.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C' D' : Category}.

  Program Definition NatTransSetoid (F G : C' [⇒] D') : Setoid :=
    {|
      setoid_carrier := NatTrans F G;
      setoid_eq A B := ∀ X, A X ≡ B X;
    |}.
  Next Obligation.
    split.
    - intros ?; reflexivity.
    - intros ???; now symmetry.
    - intros ?????; now etransitivity.
  Qed.

  Context (F G : C' [⇒] D').

  Program Definition FunCat : Category :=
    {|
      Obj := C' [⇒] D';
      Arr A B := NatTransSetoid A B;
      arrow_id A := λₙ x, ı;
      arrow_comp A B C := λₛ a, λₛ b, λₙ x, (a x) ∘ (b x);
    |}.
  Next Obligation.
    intros; simpl.
    now rewrite arrow_comp_id_l, arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite <-!arrow_comp_assoc.
    rewrite <-eta_comp.
    rewrite arrow_comp_assoc.
    rewrite eta_comp.
    rewrite !arrow_comp_assoc.
    reflexivity.
  Qed.
  Next Obligation.
    intros ? ? ? ? ? ? H X; simpl.
    now rewrite !(H X).
  Qed.
  Next Obligation.
    intros ? ? ? ? ? H ? X; simpl.
    now rewrite !(H X).
  Qed.
  Next Obligation.
    intros; simpl.
    intros X; now rewrite arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    intros X; now rewrite arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl.
    intros X; now rewrite arrow_comp_assoc.
  Qed.
End FunCat.

Notation "a [↣] b" := (@Arr FunCat a b) (at level 70, right associativity)
    : functor_scope.

Program Definition constantFuncReindex {C : Category} {D : Category} {x x' : D}
  (p : (x [~>] x')%cat)
  : (@constantFunc C D x [↣] @constantFunc C D x')%cat%functor :=
  (λₙ a, p)%functor.
Next Obligation.
  intros; simpl.
  now rewrite arrow_comp_id_l, arrow_comp_id_r.
Qed.
