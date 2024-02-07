From category Require Import
  base
  setoid
  category
  sets.

Section Functor.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.

  Context (C D : Category).

  Record Functor :=
    {
      FO :> C → D;
      fmap {A B} : ((A [~>] B)%cat [→] (FO A [~>] FO B)%cat)%setoid;
      fmap_id {A} : fmap (arrow_id A) ≡ ı;
      fmap_comp {A B C} {f : B [~>] C} {g : A [~>] B}
      : fmap (f ∘ g) ≡ fmap f ∘ fmap g;
    }.

  Program Definition constantFunc (d : D) : Functor :=
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

  Record NatTrans :=
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

Section Hom.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.

  Program Definition Hom : ((C op) × C)%cat [⇒] SetoidCat :=
    {|
      FO X := (@Arr C (fst X) (snd X));
      fmap A B := λₛ f, λₛ g, snd f ∘ g ∘ fst f;
    |}.
  Next Obligation.
    now intros [? ?] [? ?] [? ?] ? ? ->.
  Qed.
  Next Obligation.
    intros [? ?] [? ?] [? ?] [? ?] [H1 H2] ?.
    simpl in *.
    f_equiv; [| assumption].
    f_equiv.
    now rewrite H2.
  Qed.
  Next Obligation.
    intros [? ?] ?; simpl.
    now rewrite arrow_comp_id_l, arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros [? ?] [? ?] [? ?] [? ?] [? ?] ?; simpl.
    unfold compose; simpl.
    now rewrite !arrow_comp_assoc.
  Qed.

  Program Definition HomR (c : C op) : C [⇒] SetoidCat :=
    {|
      FO X := Hom (c, X);
      fmap A B := λₛ f, λₛ g, f ∘ g;
    |}.
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now rewrite arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    unfold compose; simpl.
    now rewrite arrow_comp_assoc.
  Qed.

  Program Definition HomL (c : C) : C op [⇒] SetoidCat :=
    {|
      FO X := Hom (X, c);
      fmap A B := λₛ f, λₛ g, g ∘ f;
    |}.
  Next Obligation.
    intros; simpl.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now rewrite arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    unfold compose; simpl.
    now rewrite arrow_comp_assoc.
  Qed.

  Program Definition Yoneda_Fun (F : C op [⇒] SetoidCat) : C op [⇒] SetoidCat :=
    {|
      FO c := (HomL c) [↣] F;
      fmap A B := λₛ f :: @Arr C B A, λₛ x, λₙ y, ((x y) ∘ (λₛ z, (f ∘ z)));
    |}.
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose.
    pose proof (eta_comp x) as H1.
    simpl in H1.
    unfold compose in H1; simpl in H1.
    rewrite <-H1.
    f_equiv.
    now rewrite arrow_comp_assoc.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    pose proof (eta_comp a₁ B _ a) as H1.
    simpl in H1.
    unfold compose in H1; simpl in H1.
    rewrite H1.
    pose proof (eta_comp a₂ B _ a) as H2.
    simpl in H2.
    unfold compose in H2; simpl in H2.
    rewrite H2.
    do 2 f_equiv.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    pose proof (eta_comp a B _ a0) as H1.
    simpl in H1.
    unfold compose in H1; simpl in H1.
    rewrite H1.
    pose proof (eta_comp a B _ a0) as H2.
    simpl in H2.
    unfold compose in H2; simpl in H2.
    rewrite H2.
    do 2 f_equiv.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    rewrite arrow_comp_id_l.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    rewrite arrow_comp_assoc.
    reflexivity.
  Qed.

  Program Definition Yoneda_1 (F : C op [⇒] SetoidCat)
    : (Yoneda_Fun F) [↣] F
    := λₙ c, (λₛ x, x c ı).
  Next Obligation.
    intros; simpl.
    simpl.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    pose proof (eta_comp a X Y f) as H1.
    simpl in H1.
    unfold compose in H1; simpl in H1.
    rewrite <-H1.
    rewrite arrow_comp_id_l, arrow_comp_id_r.
    reflexivity.
  Qed.

  Program Definition Yoneda_2 (F : C op [⇒] SetoidCat)
    : F [↣] (Yoneda_Fun F)
    := λₙ c, (λₛ x, λₙ z, λₛ f, (fmap F f x)).
  Next Obligation.
    intros; simpl.
    intros; simpl.
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    unfold compose.
    rewrite (@fmap_comp (C op) SetoidCat F _ _ _ f a x).
    simpl; unfold compose; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    simpl in *.
    rewrite (@fmap_comp (C op) SetoidCat F _ _ _ a0 f).
    simpl.
    reflexivity.
  Qed.

  Lemma Yoneda_12 (F : C op [⇒] SetoidCat) : (Yoneda_2 F) ∘ (Yoneda_1 F) ≡ ı.
  Proof.
    intros x f.
    intros y.
    intros ?; simpl.
    pose proof (eta_comp (Yoneda_1 F) _ _ a) as H.
    simpl in H.
    unfold compose in H.
    simpl in H.
    rewrite <-H.
    clear.
    unfold Yoneda_Fun in f.
    simpl in *.
    now rewrite arrow_comp_id_r.
  Qed.

  Lemma Yoneda_21 (F : C op [⇒] SetoidCat) : (Yoneda_1 F) ∘ (Yoneda_2 F) ≡ ı.
  Proof.
    intros x f.
    rewrite (@fmap_id (C op) SetoidCat F x f).
    simpl; unfold id; reflexivity.
  Qed.
End Hom.
