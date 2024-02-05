Require Export Utf8.
Require Export RelationClasses Equivalence Morphisms Basics Setoid.
Require Export Coq.Init.Logic.
Require Export Coq.Structures.Equalities.
Require Export Coq.Logic.Eqdep_dec Coq.Logic.ChoiceFacts.

Global Generalizable All Variables.
Global Unset Transparent Obligations.
Global Obligation Tactic := idtac.

Transparent compose.

#[projections(primitive=yes)]
Record seal {A} (f : A) := { unseal : A; seal_eq : unseal = f }.
Global Arguments unseal {_ _} _ : assert.
Global Arguments seal_eq {_ _} _ : assert.

Section Decision.
  Class Decision (P : Prop) := decide : {P} + {¬P}.
  Global Hint Mode Decision ! : typeclass_instances.
  Global Arguments decide _ {_} : simpl never, assert.

  Class RelDecision {A B} (R : A → B → Prop) :=
    decide_rel x y :> Decision (R x y).
  Global Hint Mode RelDecision ! ! ! : typeclass_instances.
  Global Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.

  Notation EqDecision A := (RelDecision (@eq A)).

  Global Instance EqDecisionBool : EqDecision bool.
  Proof.
    intros [|] [|]; [now left | now right | now right | now left].
  Qed.
End Decision.

Notation EqDecision A := (RelDecision (@eq A)).

Declare Scope setoid_scope.
Delimit Scope setoid_scope with setoid.
Local Open Scope setoid_scope.

Section Setoids.
  Record Setoid :=
    {
      setoid_carrier :> Type;
      setoid_eq      :  setoid_carrier → setoid_carrier → Prop;
      setoid_equiv   :> Equivalence setoid_eq
    }.

  Notation "a ≡ b" := (setoid_eq _ a b) (at level 70, no associativity)
      : setoid_scope.

  Global Instance EquivSetoid {S : Setoid} : Equivalence (@setoid_eq S)
    := @setoid_equiv S.

  Record SetoidArrBundle (A B : Setoid) :=
    {
      setoid_arr :> A → B;
      setoid_arr_eq : ∀ a₁ a₂, a₁ ≡ a₂ → (setoid_arr a₁) ≡ (setoid_arr a₂)
    }.

  Global Instance EquivSetoidArrBundle {A B : Setoid}
    : Equivalence (λ f g : SetoidArrBundle A B, ∀ a : A, (f a) ≡ (g a)).
  Proof.
    split.
    - intros f a; reflexivity.
    - intros f g EQ a; symmetry; apply EQ.
    - intros f g h EQ₁ EQ₂ a; etransitivity; [apply EQ₁ | apply EQ₂].
  Qed.

  Program Definition SetoidArr (A B : Setoid) : Setoid :=
    {|
      setoid_carrier := (SetoidArrBundle A B);
      setoid_eq f g := ∀ a, f a ≡ g a;
    |}.

  Program Definition idS {A} : SetoidArr A A
    := {|
      setoid_arr x := x;
    |}.
  Next Obligation.
    intros; simpl.
    assumption.
  Qed.

  Program Definition composeS {A B C} (f : SetoidArr B C) (g : SetoidArr A B)
    : SetoidArr A C
    := {|
      setoid_arr x := f (g x);
    |}.
  Next Obligation.
    intros; simpl; do 2 apply setoid_arr_eq; assumption.
  Qed.

  Global Instance SetoidArrProper1 {A B : Setoid} {f : SetoidArr A B} :
    Proper (@setoid_eq _ ==> @setoid_eq _) f.
  Proof.
    intros ???.
    now apply setoid_arr_eq.
  Qed.

  Global Instance SetoidArrProper2 {A B : Setoid} :
    Proper (@setoid_eq (SetoidArr A B) ==> @setoid_eq A ==> @setoid_eq B)
      (setoid_arr A B).
  Proof.
    intros ?? H ?? G.
    rewrite G.
    apply H.
  Qed.

  Program Definition SetoidProd (A B : Setoid) : Setoid :=
    {|
      setoid_carrier := prod A B;
      setoid_eq a b := prod (fst a ≡ fst b) (snd a ≡ snd b);
    |}.
  Next Obligation.
    split.
    - intros ?; now split.
    - intros ?? [? ?]; now split.
    - intros ??? [? ?] [? ?]; split; etransitivity; eassumption.
  Qed.

  Program Definition PropSetoid : Setoid :=
    {|
      setoid_carrier := Prop;
      setoid_eq a b := iff a b;
    |}.

  Definition Prop_embed (P : Prop) : PropSetoid := P.

  Program Definition EqSetoid {T : Type} (a b : T) : Setoid :=
    {|
      setoid_carrier := a = b;
      setoid_eq x y := True;
    |}.
  Next Obligation.
    split.
    - now intros ?.
    - now intros ??.
    - now intros ????.
  Qed.
End Setoids.

Arguments setoid_eq {_}.
Arguments setoid_equiv {_}.

Notation "a ≡ b" := (setoid_eq a b) (at level 70, no associativity)
    : setoid_scope.
Notation "a [→] b" := (SetoidArr a b) (at level 70, right associativity)
    : setoid_scope.
Notation "a × b" := (SetoidProd a b) (at level 70, right associativity)
    : setoid_scope.
Notation "[ a ]" := ({| setoid_carrier := a |}) : setoid_scope.
Notation "'λₛ' x , e" := ({| setoid_arr x := e; setoid_arr_eq := _ |})
                           (at level 120, x binder, no associativity)
    : setoid_scope.
Notation "'λₛ' x '::' t , e" := ({|
                                   setoid_arr (x : t%type) := e;
                                   setoid_arr_eq := _
                                 |})
                                 (at level 120, x binder, no associativity)
    : setoid_scope.

Definition unique_setoid {A : Setoid} (P : A → Type) (x : A) :=
  (P x) * (forall (x' : A), P x' → (x ≡ x')%setoid).

Notation "'Σ' ! x .. y , p" :=
  (sigT (unique_setoid (fun x => .. (sigT (unique_setoid (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
      format "'[' 'Σ' ! '/ ' x .. y , '/ ' p ']'")
    : type_scope.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Local Open Scope setoid_scope.

Section Category.
  Polymorphic Record Category : Type :=
    {
      Obj :> Type;
      Arr : Obj → Obj → Setoid;
      arrow_id {A} : Arr A A;
      arrow_comp {A B C} : Arr B C [→] Arr A B [→] Arr A C;
      arrow_comp_id_l {A B} {f : Arr A B} : arrow_comp arrow_id f ≡ f;
      arrow_comp_id_r {A B} {f : Arr A B} : arrow_comp f arrow_id ≡ f;
      arrow_comp_assoc {A B C D} {h : Arr C D} {g : Arr B C} {f : Arr A B}
      : arrow_comp (arrow_comp h g) f ≡ arrow_comp h (arrow_comp g f);
    }.
End Category.

Arguments Arr {_}.
Arguments arrow_id {_}.
Arguments arrow_comp {_ _ _ _}.
Arguments arrow_comp_id_l {_ _ _}.
Arguments arrow_comp_id_r {_ _ _}.
Arguments arrow_comp_assoc {_ _ _ _ _}.

Notation "'ı'" := (arrow_id _) : cat_scope.
Notation "f ∘ g" := (arrow_comp f%cat g%cat) (at level 40, left associativity)
    : cat_scope.
Notation "a [~>] b" := (Arr a b) (at level 70, right associativity) : cat_scope.

Section Op.
  Local Open Scope cat_scope.
  Context (C : Category).

  Program Definition Op : Category :=
    {|
      Obj := C;
      Arr A B := (B [~>] A)%cat;
      arrow_id A := ı;
      arrow_comp _ _ _ := λₛ f, λₛ g, g ∘ f;
    |}.
  Next Obligation.
    intros ?????? H; simpl.
    do 2 f_equiv.
    apply H.
  Defined.
  Next Obligation.
    intros ????? H ?; simpl.
    now rewrite H.
  Defined.
  Next Obligation.
    intros; apply arrow_comp_id_r.
  Defined.
  Next Obligation.
    intros; apply arrow_comp_id_l.
  Defined.
  Next Obligation.
    intros; symmetry; apply arrow_comp_assoc.
  Defined.
End Op.

Notation "C 'op'" := (Op C) (at level 70) : cat_scope.

Section Iso.
  Local Open Scope cat_scope.
  Context {C : Category}.

  Record Isomorphism (a b : C) :=
    {
      iso1 :> a [~>] b;
      iso2 : b [~>] a;
      iso12 : (iso2 ∘ iso1) ≡ ı;
      iso21 : (iso1 ∘ iso2) ≡ ı;
    }.
End Iso.

Arguments Isomorphism {_}.
Arguments iso1 {_ _ _} _.
Arguments iso2 {_ _ _} _.
Arguments iso12 {_ _ _} _.
Arguments iso21 {_ _ _} _.

Notation "f '⁻¹'" := (iso2 f) (at level 40) : cat_scope.
Notation "a ≃ b" := (Isomorphism a b) (at level 40) : cat_scope.

Section Mono.
  Local Open Scope cat_scope.
  Context {C : Category}.

  Record Monomorphism (A B : C) := {
      monic :> A [~>] B;
      monic_cancel : ∀ {D : C} (g₁ g₂ : D [~>] A), monic ∘ g₁ ≡ monic ∘ g₂;
    }.
End Mono.

Arguments monic {_ _ _}.

Notation "A [⤷] B" := (Monomorphism A B) (at level 70, right associativity)
    : cat_scope.

Section Epi.
  Local Open Scope cat_scope.
  Context {C : Category}.

  Record Epimorphism (A B : C) := {
      epic :> A [~>] B;
      epic_cancel : ∀ {D : C} (g₁ g₂ : B [~>] D), g₁ ∘ epic ≡ g₂ ∘ epic;
    }.
End Epi.

Arguments epic {_ _ _}.

Notation "A [⇥] B" := (Epimorphism A B) (at level 70, right associativity)
    : cat_scope.

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

Notation "𝟭" := (terminal_obj _) : cat_scope.

Section Functor.
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

Notation "a [↣] b" := (NatTrans a b) (at level 70, right associativity)
    : functor_scope.
Notation "'η' F" := (eta F) (at level 40) : functor_scope.
Notation "'λₙ' x , e" := ({| eta x := e |})
                           (at level 120, x binder, no associativity)
    : functor_scope.
Notation "'λₙ' x '::' t , e" := ({| eta (x : t%type) := e |})
                                 (at level 120, x binder, no associativity)
    : functor_scope.

Section Discrete.
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

Section Setoids.
  Program Definition SetoidCat : Category :=
    {|
      Obj := Setoid;
      Arr A B := (A [→] B)%setoid;
      arrow_id A := {| setoid_arr := id |};
      arrow_comp _ _ _ := λₛ f, λₛ g, {| setoid_arr := compose f g |};
    |}.
  Next Obligation.
    intros; simpl.
    assumption.
  Qed.
  Next Obligation.
    intros; simpl.
    now do 2 apply SetoidArrProper1.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    now apply SetoidArrProper1.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    now unfold compose.
  Qed.
  Next Obligation.
    intros; simpl.
    now unfold compose.
  Qed.
  Next Obligation.
    intros; simpl.
    now unfold compose.
  Qed.
  Next Obligation.
    intros; simpl.
    now unfold compose.
  Qed.
End Setoids.

Section FunCat.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C' D' : Category}.

  Program Definition NatTransSetoid (F G : C' [⇒] D') : Setoid :=
    {|
      setoid_carrier := F [↣] G;
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

Section ProdCat.
  Local Open Scope cat_scope.

  Context (C D : Category).

  Program Definition ProdCat : Category :=
    {|
      Obj := prod C D;
      Arr A B := ((fst A [~>] fst B)%cat × (snd A [~>] snd B)%cat)%setoid;
      arrow_id A := pair (arrow_id (fst A)) (arrow_id (snd A));
      arrow_comp _ _ _ := λₛ f, λₛ g, pair (fst f ∘ fst g) (snd f ∘ snd g);
    |}.
  Next Obligation.
    intros ???? [? ?] [? ?] [H1 H2]; simpl.
    simpl in *.
    split.
    - now rewrite H1.
    - now rewrite H2.
  Qed.
  Next Obligation.
    intros ??? [? ?] [? ?] [H1 H2]; simpl.
    intros [? ?]; simpl.
    split.
    - now do 2 f_equiv.
    - now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl; split; now rewrite !arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl; split; now rewrite !arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl; split; now rewrite !arrow_comp_assoc.
  Qed.
End ProdCat.

Notation "a × b" := (ProdCat a b) (at level 70, right associativity) : cat_scope.

Section Hom.
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
      FO c := NatTransSetoid (HomL c) F;
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
    : @Arr (@FunCat (C op) SetoidCat) (Yoneda_Fun F) F
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
    : @Arr (@FunCat (C op) SetoidCat) F (Yoneda_Fun F)
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

Section Limits.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {J : Category}.
  Context {C : Category}.
  Context (F : J [⇒] C).

  (* Record Cone' := *)
  (*   { *)
  (*     cone_obj' :> C; *)
  (*     cone_nat' : @Arr (@FunCat J C) (Δ cone_obj') F; *)
  (*   }. *)

  (* Record ConeArr' (A B : Cone') := *)
  (*   { *)
  (*     cone_arr' :> @Arr (@FunCat J C) *)
  (*                    (@constantFunc J C (cone_obj' A)) *)
  (*                    (@constantFunc J C (cone_obj' B)); *)
  (*     cone_comp' : (cone_nat' A) ≡ (cone_nat' B) ∘ cone_arr'; *)
  (*   }. *)

  (* Program Definition ConeArrSetoid' (A B : Cone') : Setoid := *)
  (*   {| *)
  (*     setoid_carrier := ConeArr' A B; *)
  (*     setoid_eq x y := x ≡ y; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   split. *)
  (*   - intros ?; reflexivity. *)
  (*   - intros ???; now symmetry. *)
  (*   - intros ?????; etransitivity; eassumption. *)
  (* Qed. *)

  (* Program Definition ConeCat' : Category := *)
  (*   {| *)
  (*     Obj := Cone'; *)
  (*     Arr A B := ConeArrSetoid' A B; *)
  (*     arrow_id A := {| cone_arr' := ı |}; *)
  (*     arrow_comp _ _ _ := λₛ f, λₛ g, {| cone_arr' := f ∘ g |}; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   intros ?. *)
  (*   now rewrite arrow_comp_id_r. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros X Y Z f g. *)
  (*   rewrite <-arrow_comp_assoc. *)
  (*   rewrite <-(cone_comp' _ _ f). *)
  (*   now rewrite <-(cone_comp' _ _ g). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros; simpl; intros ?; simpl. *)
  (*   f_equiv. *)
  (*   apply (H X). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros; simpl. *)
  (*   intros a; intros ?; simpl. *)
  (*   do 2 f_equiv. *)
  (*   apply (H X). *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros; simpl; intros ?. *)
  (*   apply arrow_comp_id_l. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros; simpl; intros ?. *)
  (*   apply arrow_comp_id_r. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros; simpl; intros ?. *)
  (*   apply arrow_comp_assoc. *)
  (* Qed. *)

  (* Record Limit' := *)
  (*   { *)
  (*     limit_obj' :> Terminal ConeCat'; *)
  (*   }. *)

  (* Definition LimitUnique' (a b : Limit') : Isomorphism a b := TerminalUnique _ _ _. *)

  Record Cone :=
    {
      cone_obj :> C;
      cone_proj (X : J) : cone_obj [~>] (F X);
      cone_proj_comp {X Y : J} {f : X [~>] Y}
      : fmap F f ∘ cone_proj X ≡ cone_proj Y;
    }.

  Record ConeArr (A B : Cone) :=
    {
      cone_arr :> ((cone_obj A) [~>] (cone_obj B))%cat;
      cone_arr_comp (j : J) : (cone_proj B j) ∘ cone_arr ≡ (cone_proj A j);
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
      arrow_id A := {| cone_arr := ı |};
      arrow_comp _ _ _ := λₛ f, λₛ g, {| cone_arr := f ∘ g |};
    |}.
  Next Obligation.
    intros ??; apply arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros X Y Z f g j.
    rewrite <-arrow_comp_assoc.
    rewrite <-(cone_arr_comp _ _ g j).
    do 2 f_equiv.
    apply cone_arr_comp.
  Qed.
  Next Obligation.
    intros; simpl; now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros a.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl; apply arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl; apply arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl; apply arrow_comp_assoc.
  Qed.

  Record Limit :=
    {
      limit_obj :> Terminal ConeCat;
    }.

  Definition LimitUnique (a b : Limit) : Isomorphism a b :=
    TerminalUnique _ _ _.
End Limits.

Arguments cone_obj {_ _ _}.
Arguments limit_obj {_ _ _}.

(* Arguments cone_obj' {_ _ _}. *)
(* Arguments limit_obj' {_ _ _}. *)

Section InternalProd.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Lemma arr_prod {D : Type}
    `{!EqDecision D}
    {C : Category}
    (f : ⌊ D ⌋ [⇒] C)
    (g : (⌊ D ⌋ [⇒] C))
    (h : (f [↣] g)%functor)
    {Hf : Limit f}
    {Hg : Limit g}
    : ((cone_obj (terminal_obj (limit_obj Hf)))
         [~>] (cone_obj (terminal_obj (limit_obj Hg))))%cat.
  Proof.
    simpl in *.
    assert (t : sigT (λ ff : ConeCat g,
                      ((cone_obj (terminal_obj (limit_obj Hf)))
                         [~>] ff)%cat)).
    {
      simpl.
      unshelve econstructor.
      - unshelve econstructor.
        + apply (terminal_obj (limit_obj Hf)).
        + intros x; simpl.
          apply ((h x) ∘ (cone_proj f (terminal_obj (limit_obj Hf)) x))%cat.
        + intros ? ? k; simpl.
          rewrite <-!arrow_comp_assoc.
          pose proof (eta_comp h _ _ k) as H.
          simpl in H.
          rewrite <-H.
          rewrite arrow_comp_assoc.
          f_equiv.
          rewrite cone_proj_comp.
          reflexivity.
      - simpl.
        apply arrow_id.
    }
    apply ((@cone_arr _ _ _ _ _
              ((projT1 (terminal_proj (t := (limit_obj Hg) ) (projT1 t))))%cat)
             ∘ (projT2 t))%cat.
  Defined.

End InternalProd.

Section Exp.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.
  Context (bp : ∀ (J : ⌊ bool ⌋ [⇒] C), Limit J).

  Local Program Definition bin_fun_prod (Z Z' Y : C) (f : Z [~>] Z') :
    DiscreteFun (λ b : bool, if b then Z else Y)
      [↣] DiscreteFun (λ b : bool, if b then Z' else Y) :=
    λₙ x, match x with true => f | false => ı end.
  Next Obligation.
    intros ? ? ? ? [|] [|]; simpl; intros g; simpl.
    - generalize dependent g.
      apply (K_dec_type EqDecisionBool).
      rewrite arrow_comp_id_l, arrow_comp_id_r; reflexivity.
    - inversion g.
    - inversion g.
    - generalize dependent g.
      apply (K_dec_type EqDecisionBool).
      rewrite arrow_comp_id_l; reflexivity.
  Qed.

  Definition isEval (X Y Z : C) : Type :=
    cone_obj
      (terminal_obj
         (limit_obj
            (bp (DiscreteFun (λ (b : bool), if b then Z else Y)))))
      [~>] X.

  Record Exp (X Y : C) :=
    {
      exp_obj :> C;
      eval : isEval X Y exp_obj;
      exp_ump : ∀ (Z' : C) (eval' : isEval X Y Z'),
        Σ! f : (Z' [~>] exp_obj),
        eval' ≡
          eval
          ∘ arr_prod
          (DiscreteFun (λ b : bool, if b then Z' else Y))
          (DiscreteFun (λ b : bool, if b then exp_obj else Y))
          (bin_fun_prod Z' exp_obj Y f);
    }.

  (* Program Definition ExpUnique (X Y : C) (a b : Exp X Y) : Isomorphism a b := *)
  (*   {| *)
  (*     iso1 := (projT1 (exp_ump X Y b a (eval X Y a))); *)
  (*     iso2 := (projT1 (exp_ump X Y a b (eval X Y b))); *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   rewrite <-(snd (projT2 (exp_ump X Y a a (eval X Y a))) *)
  (*               (projT1 (exp_ump X Y a b (eval X Y b)) *)
  (*                  ∘ projT1 (exp_ump X Y b a (eval X Y a)))). *)
  (*   - rewrite <-(snd (projT2 (exp_ump X Y a a (eval X Y a))) ı). *)
  (*     + reflexivity. *)
  (*     + rewrite (fst (projT2 (exp_ump X Y a a (eval X Y a)))). *)
  (*       do 2 f_equiv. *)
  (*       * apply (fst (projT2 (exp_ump X Y a a (eval X Y a)))). *)
  (*       * admit. *)
  (*   - admit. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (*   rewrite <-(snd (projT2 (exp_ump X Y b b (eval X Y b))) *)
  (*               (projT1 (exp_ump X Y b a (eval X Y a)) *)
  (*                  ∘ projT1 (exp_ump X Y a b (eval X Y b)))). *)
  (*   - rewrite <-(snd (projT2 (exp_ump X Y b b (eval X Y b))) ı). *)
  (*     + reflexivity. *)
  (*     + admit. *)
  (*   - admit. *)
  (* Admitted. *)
End Exp.

Section SetoidInst.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Program Definition TerminalSet : Terminal SetoidCat :=
    {|
      terminal_obj := [ unit ] : SetoidCat;
      terminal_proj X := existT _ (λₛ _, tt) _;
    |}.
  Next Obligation.
    now simpl.
  Qed.
  Next Obligation.
    econstructor.
    * constructor.
    * intros; simpl.
      intros ?; unfold const; simpl.
      now destruct (x' a).
  Qed.

  Program Definition constantSetFunc (D : Category) : (D) [⇒] SetoidCat
    := constantFunc (terminal_obj TerminalSet).

  Program Definition Setoid_limit (D : Category) (J : D [⇒] SetoidCat)
    : Cone J :=
    {|
      cone_obj := (@Arr (@FunCat D SetoidCat) (constantSetFunc D) J);
      cone_proj X := (λₛ x, x X tt);
    |}.
  Next Obligation.
    intros; simpl.
    f_equiv.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; unfold compose; simpl.
    rewrite <-(eta_comp a X Y f tt).
    simpl; unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition Setoid_limit_terminal_arr (D : Category)
    (J : D [⇒] SetoidCat) (X : Cone J) : ConeArr J X (Setoid_limit D J) :=
    {|
      cone_arr := (λₛ x, λₙ y, λₛ z, (@cone_proj _ _ _ X y x))
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros []; unfold compose; simpl.
    rewrite <-(cone_proj_comp _ X x  (f := f)).
    simpl; unfold compose; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ? [].
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition Setoid_limit_terminal (D : Category) (J : D [⇒] SetoidCat)
    : Terminal (ConeCat J) :=
    {|
      terminal_obj := Setoid_limit D J;
      terminal_proj X := existT _ (Setoid_limit_terminal_arr D J X) _;
    |}.
  Next Obligation.
    intros; simpl.
    econstructor.
    * constructor.
    * intros; simpl.
      intros ? ? []; simpl.
      rewrite <-(@cone_arr_comp D SetoidCat J X _ x').
      simpl.
      unfold compose; simpl.
      reflexivity.
  Qed.

  Program Definition Setoid_hasLimits {D : Category} (J : D [⇒] SetoidCat)
    : Limit J :=
  {|
    limit_obj := Setoid_limit_terminal D J;
  |}.

  Definition Setoid_hasBinProducts (J : (⌊ bool ⌋) [⇒] SetoidCat)
    : Limit J := Setoid_hasLimits J.

  Program Definition SetoidArr_hasEval (X Y : SetoidCat)
    : isEval Setoid_hasBinProducts X Y (SetoidArr Y X) :=
    (λₛ x, (x true tt (x false tt))).
  Next Obligation.
    intros; simpl.
    simpl in *.
    rewrite (H true tt).
    rewrite (H false tt).
    reflexivity.
  Qed.

  Program Definition SetoidArr_ump (X Y : SetoidCat)
    : ∀ (Z' : SetoidCat) (eval' : isEval Setoid_hasBinProducts X Y Z'),
    Σ! f : (Z' [~>] (SetoidArr Y X)),
    eval' ≡
      (SetoidArr_hasEval X Y)
      ∘ arr_prod
      (DiscreteFun (λ b : bool, if b then Z' else Y))
      (@DiscreteFun _ _ SetoidCat (λ b : bool, if b then (SetoidArr Y X) else Y))
      (bin_fun_prod Z' (SetoidArr Y X) Y f) :=
  λ Z' eval',
    existT
      _
      (λₛ z, λₛ y, (eval' (λₙ b :: ⌊ bool ⌋,
                        match b as b'
                              return
                              (constantSetFunc (⌊ bool ⌋) b'
                                 [~>] DiscreteFun (λ b1 : bool, if b1 then Z' else Y) b')
                        with
                        | true => (λₛ _, z)
                        | false => (λₛ _, y)
                        end)))
      _.
  Next Obligation.
    intros; reflexivity.
  Qed.
  Next Obligation.
    intros; reflexivity.
  Qed.
  Next Obligation.
    intros ??????.
    intros [|] [|]; simpl;
      intros; simpl;
      unfold compose; simpl.
    - generalize dependent f;
        apply (K_dec_type EqDecisionBool);
        reflexivity.
    - inversion f.
    - inversion f.
    - generalize dependent f;
        apply (K_dec_type EqDecisionBool);
        reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    f_equiv.
    simpl.
    intros [|] ?; simpl; [reflexivity | apply H].
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    f_equiv.
    simpl.
    intros [|] ?; simpl; [apply H | reflexivity].
  Qed.
  Next Obligation.
    intros.
    constructor.
    - simpl.
      intros; simpl.
      unfold compose; simpl.
      unfold id; simpl.
      f_equiv.
      intros [|]; simpl;
        intros []; simpl;
        reflexivity.
    - intros; simpl.
      intros ? ?; simpl.
      unfold compose; simpl.
      rewrite H.
      simpl; unfold compose; simpl.
      f_equiv.
  Qed.

  Program Definition Setoid_Exp (X Y : SetoidCat)
    : Exp Setoid_hasBinProducts X Y :=
    {|
      exp_obj := SetoidArr Y X;
      eval := SetoidArr_hasEval X Y;
      exp_ump := SetoidArr_ump X Y;
    |}.
End SetoidInst.

Definition PSh (C : Category) : Category := @FunCat (C op)%cat SetoidCat.

Section PSh_exp.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {Obj : Category}.

  Class FComp {X Y : PSh Obj} {A} (K : ∀ {B}, (Arr A B) → X B → Y B) :=
    comp_fmap : ∀ {B C} (δ₂ : Arr B C) (δ₁ : Arr A B) (v : X B),
        K (δ₂ ∘ δ₁) (fmap X δ₂ v) ≡ fmap Y δ₂ (K δ₁ v).

  Record RemFun (X Y : PSh Obj) (A : Obj op) :=
    { arr :> ∀ {B}, (Arr A B) → X B → Y B;
      arr_ext {B : Obj op}
      : Proper (setoid_eq ==> setoid_eq ==> setoid_eq) (@arr B);
      arr_fmap : FComp (@arr)
    }.
  Arguments arr {X Y A} _ {B} _ _.

  Global Instance RF_prop {X Y : PSh Obj} {A} {RF : RemFun X Y A} {B} :
    Proper (setoid_eq ==> setoid_eq ==> setoid_eq) (RF B) :=
    arr_ext _ _ _ RF.

  Global Instance RF_FComp {X Y : PSh Obj} {A} {RF : RemFun X Y A} :
    FComp RF := arr_fmap _ _ _ RF.

  Definition RemFun_eq {X Y : PSh Obj}
    : ∀ {A}, (RemFun X Y A) → (RemFun X Y A) → Prop :=
    λ {A} φ₁ φ₂, ∀ {B} (δ : Arr A B) v, φ₁ _ δ v ≡ φ₂ _ δ v.

  Global Instance RemFun_equiv {X Y : PSh Obj}
    : ∀ {A}, Equivalence (@RemFun_eq X Y A).
  Proof.
    split.
    - intros φ B δ v; reflexivity.
    - intros φ₁ φ₂ EQφ B δ v; symmetry; apply EQφ.
    - intros φ₁ φ₂ φ₃ EQφ₁ EQφ₂ B δ v; etransitivity; [apply EQφ₁ | apply EQφ₂].
  Qed.

  Program Definition RemFun_setoid (X Y : PSh Obj) (A : Obj op) : Setoid :=
    {|
      setoid_carrier := RemFun X Y A;
      setoid_eq := RemFun_eq;
      setoid_equiv := RemFun_equiv;
    |}.

  Program Definition RemFun_fmap {X Y : PSh Obj}
    : ∀ {A B}, (Arr A B) → (RemFun X Y) A → (RemFun X Y) B :=
    λ {A B} δ φ, {| arr C δ' v := φ C (δ' ∘ δ) v |}.
  Next Obligation.
    intros X Y A B δ φ C.
    intros δ₁ δ₂ EQδ v₁ v₂ EQv; now rewrite EQδ, EQv.
  Qed.
  Next Obligation.
    unfold FComp; intros; rewrite arrow_comp_assoc; apply arr_fmap.
  Qed.

  Program Definition PArr (X Y : PSh Obj) : PSh Obj :=
    {| FO A := RemFun_setoid X Y A;
       fmap A B := (λₛ f, λₛ (x : RemFun_setoid X Y A), RemFun_fmap f x);
    |}.
  Next Obligation.
    intros; simpl.
    intros ? ? ?; simpl.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    intros ? ? ?; simpl.
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    intros ???; simpl.
    rewrite arrow_comp_id_l.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    intros ???; simpl.
    rewrite arrow_comp_assoc.
    reflexivity.
  Qed.
End PSh_exp.

Notation "'λₖ' Γ δ μ , e" :=
  {| arr Γ δ μ := e;
    arr_ext := _;
    arr_fmap := _
  |} (at level 120, Γ binder, δ binder, μ binder, no associativity)
    : functor_scope.

Section PSh_inst.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Program Definition PSh_limit_pointwise {C} (D : Category)
    (J : D [⇒] (PSh C)) (c : C op) : D [⇒] SetoidCat :=
    {|
      FO d := J d c;
      fmap A B := (λₛ x, (λₛ y, ((η (fmap J x)) c y)));
    |}.
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    apply (setoid_arr_eq (Arr A B) (Arr (J A) (J B)) (fmap J) _ _ H c a).
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    unfold id; simpl.
    simpl.
    etransitivity; [apply (@fmap_id _ _ J) |].
    reflexivity.
  Qed.

  Next Obligation.
    intros; simpl.
    unfold compose; intros; simpl.
    rewrite (@fmap_comp D (PSh C) J _ _ _ f g c a).
    simpl.
    unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition PSh_limit {C} (D : Category) (J : D [⇒] (PSh C)) : PSh C :=
    {|
      FO c := terminal_obj (limit_obj (Setoid_hasLimits
                                         (PSh_limit_pointwise D J c)));
      fmap A B := λₛ x, λₛ X, λₙ y, λₛ T, (fmap (J y) x (X y tt));
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros []; unfold compose; simpl.
    epose proof (@eta_comp (C op) SetoidCat _ (J Y) _ A B x) as H'.
    simpl in H'.
    unfold compose in H'.
    simpl in H'.
    rewrite H'.
    f_equiv.
    apply (@eta_comp D SetoidCat _ _ X _ _ f tt).
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    f_equiv.
    apply (H X).
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    f_equiv.
    now rewrite H.
  Qed.
  Next Obligation.
    simpl.
    intros ?; simpl.
    intros ?; simpl.
    intros ? ?; simpl.
    intros ? ? []; simpl.
    rewrite (@fmap_id (C op) SetoidCat (J _) A (_ _ tt)).
    simpl; unfold id; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    simpl.
    intros ? ? ? ? ? ? ? ? ? ? []; simpl.
    rewrite (@fmap_comp (C op) SetoidCat (J X) _ _ _ f g (a X tt)).
    simpl; unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition PSh_limit_cone {C} (D : Category) (J : D [⇒] (PSh C))
    : Cone J :=
    {|
      cone_obj := PSh_limit D J;
      cone_proj t := λₙ a, λₛ b, (b t tt);
    |}.
  Next Obligation.
    intros; simpl.
    apply (H _).
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    symmetry.
    apply (eta_comp a X Y f tt).
  Qed.

  Program Definition PSh_limit_cone_terminal_arr {C} (D : Category)
    (J : D [⇒] (PSh C)) (X : ConeCat J) : X [~>] PSh_limit_cone D J :=
    {|
      cone_arr := λₙ a, λₛ b, λₙ c, λₛ d, (@cone_proj _ _ _ X c a b)
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    pose proof (@cone_proj_comp D (PSh C) J X _ _ f) as H'.
    simpl in H'.
    unfold compose in H'.
    simpl in H'.
    rewrite H'.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    epose proof (@eta_comp (C op) SetoidCat _ (J X1) _ _ _ f) as H'.
    simpl in H'.
    unfold compose in H'.
    simpl in H'.
    rewrite H'.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition PSh_limit_cone_terminal {C} (D : Category)
    (J : D [⇒] (PSh C))
    : Terminal (ConeCat J) :=
    {|
      terminal_obj := PSh_limit_cone D J;
      terminal_proj X :=
        existT _ (PSh_limit_cone_terminal_arr D J X) _;
    |}.
  Next Obligation.
    intros; simpl.
    constructor.
    * constructor.
    * intros; simpl.
      intros; simpl.
      pose proof (@cone_arr_comp D (PSh C) J _ _ x' X1 X0 a) as H'.
      simpl in H'.
      unfold compose in H'.
      simpl in H'.
      symmetry.
      destruct a0.
      apply H'.
  Qed.

  Program Definition PSh_hasLimits {C} {D : Category}
    (J : D [⇒] (PSh C)) : Limit J :=
    {|
      limit_obj := PSh_limit_cone_terminal D J;
    |}.

  Program Definition PSh_hasBinProducts {C} (J : (⌊ bool ⌋) [⇒] (PSh C))
    : Limit J := PSh_hasLimits J.

  Program Definition PArr_hasEval {C} (X Y : PSh C)
    : isEval PSh_hasBinProducts X Y (PArr Y X) :=
    λₙ x, λₛ y, (y true tt x ı (y false tt)).
  Next Obligation.
    intros; simpl.
    pose proof (H true tt x ı (@eta _ _ _ _ a₁ false tt)) as G.
    simpl in G.
    rewrite G.
    apply arr_ext.
    - reflexivity.
    - apply SetoidArrProper2.
      + apply (H false).
      + reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    rewrite arrow_comp_id_r.
    rewrite <-(@arr_fmap C Y X X0 (a true tt) X0 Y0 f ı).
    f_equiv.
    now rewrite arrow_comp_id_r.
  Qed.

  Program Definition PArr_ump {C} (X Y : PSh C) :
    ∀ (Z' : PSh C) (eval' : isEval PSh_hasBinProducts X Y Z'),
    Σ! f : (Z' [~>] (PArr Y X)),
    eval' ≡
      (PArr_hasEval X Y)
      ∘ arr_prod
      (DiscreteFun (λ b : bool, if b then Z' else Y))
      (@DiscreteFun _ _ (PSh C) (λ b : bool, if b then (PArr Y X) else Y))
      (bin_fun_prod Z' (PArr Y X) Y f) :=
  λ Z' eval',
    existT
      _
      (λₙ x, λₛ y, λₖ Γ δ μ,
        (@eval' Γ
           (λₙ ν,
             (λₛ t, match ν with
                    | true => (@fmap _ _ Z' _ _ δ y)
                    | false => μ
                    end))))
      _.
  Next Obligation.
    intros; simpl.
    destruct ν; reflexivity.
  Qed.
  Next Obligation.
    intros ? ? ? ? ? ? ? ? ? ? [|] [|]; simpl;
      [| intros contra; inversion contra | intros contra; inversion contra |];
      unfold compose.
    - intros ? [].
      generalize dependent f.
      apply (K_dec_type Bool.bool_dec).
      reflexivity.
    - intros ? [].
      generalize dependent f.
      apply (K_dec_type Bool.bool_dec).
      reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?? H ???; simpl.
    f_equiv.
    intros [|]; simpl; intros ?; [| assumption].
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?????.
    pose proof (@eta_comp (C op) SetoidCat _ _ eval' _ _ δ₂) as H.
    simpl in H.
    unfold compose in H.
    rewrite <-H.
    f_equiv.
    intros [|] []; simpl; [| reflexivity].
    pose proof (@fmap_comp _ _ Z' _ _ _ δ₂ δ₁) as H'.
    rewrite H'.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???; simpl.
    f_equiv.
    intros [|] []; simpl; [f_equiv; assumption | reflexivity].
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    intros ???; simpl.
    f_equiv.
    intros [|] []; simpl; [| reflexivity].
    pose proof (@fmap_comp _ _ Z' _ _ _ δ f a) as H.
    simpl in H.
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    split.
    - intros; simpl.
      unfold compose; simpl.
      f_equiv.
      intros [|] []; simpl.
      + rewrite (@fmap_id _ _ Z' X0).
        simpl.
        unfold id.
        reflexivity.
      + unfold id.
        reflexivity.
    - intros; simpl.
      intros ?????; simpl.
      specialize (H B).
      set (f := _ : constantSetFunc (⌊ bool ⌋)
                      [↣] PSh_limit_pointwise (⌊ bool ⌋)
                      (DiscreteFun (λ b : bool, if b then Z' else Y)) B).
      specialize (H f).
      etransitivity; [apply H | clear H; subst f].
      unfold compose; simpl.
      unfold id; simpl.
      pose proof (@eta_comp (C op) SetoidCat Z'
                    (PArr Y X) x' X0 B δ a B ı v) as H.
      simpl in H.
      unfold compose in H; simpl in H.
      rewrite arrow_comp_id_r in H.
      apply H.
      (* Qed. *)
  Admitted.

  Program Definition PSh_Exp {C} (X Y : PSh C)
    : Exp PSh_hasBinProducts X Y :=
    {|
      exp_obj := PArr Y X;
      eval := PArr_hasEval X Y;
      exp_ump := PArr_ump X Y;
    |}.

End PSh_inst.

Section TerminalLimit.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Global Instance EqDecisionEmpty : EqDecision Empty_set.
  Proof.
    intros [].
  Qed.

  Global Instance EqDecisionUnit : EqDecision unit.
  Proof.
    intros [] []; left; reflexivity.
  Qed.

  Definition Empty_diagram {C} : ⌊ Empty_set ⌋ [⇒] C :=
    DiscreteFun (Empty_set_rect _).

  Program Definition TerminalAsLimit {C}
    (t : ∀ (D : Category) (J : D [⇒] C), Limit J) : Terminal C :=
    {|
      terminal_obj :=
        (cone_obj (terminal_obj (limit_obj (t (⌊ Empty_set ⌋) Empty_diagram))));
    |}.
  Next Obligation.
    intros.
    assert (HHH : sig (λ (HHH : @ConeCat _ C Empty_diagram), cone_obj HHH = X)).
    {
      unshelve eset (HHH :=
                       {|
                         cone_obj := X;
                         cone_proj (Y : ⌊ Empty_set ⌋) := match Y with end;
                         cone_proj_comp (Y : ⌊ Empty_set ⌋) := match Y with end;
                       |} : @ConeCat _ C Empty_diagram).
      exists HHH.
      subst HHH.
      reflexivity.
    }
    destruct HHH as [X' HHH].
    pose proof (@terminal_proj
                  (ConeCat Empty_diagram) (limit_obj (t _ Empty_diagram)) X')
      as HH.
    destruct HH as [HH1 HH2].
    simpl in HH1.
    destruct HH1 as [G1 G2 _].
    rewrite <-HHH.
    exists G1.
    split; [constructor |].
    intros x' _.
    subst.
    destruct HH2 as [_ HH2].
    simpl in HH2.
    unshelve eset (x'' := _ :
                     ConeArr Empty_diagram X'
                       (terminal_obj (limit_obj (t _ Empty_diagram)))).
    {
      unshelve econstructor.
      - apply x'.
      - intros [].
    }
    specialize (HH2 x'' I).
    subst x''.
    simpl in HH2.
    apply HH2.
  Qed.

  Program Definition TerminalIsTerminalLimit {C} (t : Terminal C)
    (J : ⌊ Empty_set ⌋ [⇒] C) : Limit J :=
    {|
      limit_obj :=
        {|
          terminal_obj :=
            {|
              cone_obj := t;
              cone_proj X := match X with end;
            |};
        |};
    |}.
  Next Obligation.
    intros ??? [].
  Qed.
  Next Obligation.
    intros; simpl.
    unshelve eexists; [| split; [constructor | intros x' _]].
    - unshelve econstructor.
      + simpl.
        apply terminal_proj.
      + intros [].
    - simpl.
      destruct (@terminal_proj C t X).
      apply u; constructor.
  Qed.

End TerminalLimit.

Section Slice.
  Local Open Scope cat_scope.
  Context {C : Category}.
  Context (c : C).

  Record SliceObj :=
    {
      slice_obj_src :> C;
      slice_obj_arr : Arr slice_obj_src c;
    }.

  Record SliceArr (A B : SliceObj) :=
    {
      slice_arr :> Arr A B;
      slice_arr_comp : slice_obj_arr B ∘ slice_arr ≡ slice_obj_arr A;
    }.

  Program Definition SliceArrSetoid (A B : SliceObj) : Setoid :=
    {|
      setoid_carrier := SliceArr A B;
      setoid_eq := @setoid_eq (Arr A B);
    |}.
  Next Obligation.
    intros.
    split.
    - intros ?.
      reflexivity.
    - intros ???.
      now symmetry.
    - intros ?? y ??.
      simpl in *.
      etransitivity; eassumption.
  Qed.

  Program Definition Slice : Category :=
    {|
      Obj := SliceObj;
      Arr A B := SliceArrSetoid A B;
      arrow_id A := {| slice_arr := ı |};
      arrow_comp A B C := λₛ f, λₛ g, {| slice_arr := f ∘ g |};
    |}.
  Next Obligation.
    intros.
    apply arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros.
    rewrite <-arrow_comp_assoc.
    rewrite slice_arr_comp.
    apply slice_arr_comp.
  Qed.
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
End Slice.

Section PB.
  Local Open Scope cat_scope.
  Context {C : Category}.

  Record isCommSquare {X Y Z CS_obj : C}
    (f : X [~>] Z)
    (g : Y [~>] Z)
    (CS_proj1 : CS_obj [~>] X)
    (CS_proj2 : CS_obj [~>] Y) : Prop
    :=
    {
      CS_comm :> f ∘ CS_proj1 ≡ g ∘ CS_proj2;
    }.
  Arguments CS_comm {_ _ _ _ _ _}.

  Record isPullback {X Y Z CS_obj : C}
    (f : X [~>] Z)
    (g : Y [~>] Z)
    (CS_proj1 : CS_obj [~>] X)
    (CS_proj2 : CS_obj [~>] Y) : Type
    := {
      is_pb :> isCommSquare f g CS_proj1 CS_proj2;
      is_pb_ump : ∀ {W} (h : W [~>] X) (j : W [~>] Y),
        isCommSquare f g h j → Σ! (i : W [~>] CS_obj),
        h ≡ CS_proj1 ∘ i ∧ j ≡ CS_proj2 ∘ i;
    }.
End PB.

Arguments CS_comm {_ _ _ _ _ _ _}.
Arguments is_pb {_ _ _ _ _ _}.
Arguments is_pb_ump {_ _ _ _ _ _ _}.

Section SubObjectClassifier.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.
  Context {H : ∀ (D : Category) (J : D [⇒] C), Limit J}.

  Record SubobjectClassifier := {
      subobject_classifier :> C;
      true : TerminalAsLimit H [⤷] subobject_classifier;
      subobject_classifier_ump1 : ∀ {U X} (f : U [⤷] X),
        Σ! (char : X [~>] subobject_classifier),
        isPullback char true f (projT1 (terminal_proj U));
    }.
End SubObjectClassifier.

Arguments subobject_classifier {_ _ _}.
Notation "'Ω'" := (subobject_classifier) : cat_scope.

Section Sieves.
  Local Open Scope cat_scope.
  Context {C : Category}.
  Context (c : C).

  Record Sieve := {
      sieve_arrows :> ∀ {d : C}, Arr d c [→] PropSetoid;
      sieve_closed : ∀ {d e : C} (f : Arr d c) (g : Arr e d),
        sieve_arrows f → sieve_arrows (f ∘ g);
    }.

  Program Definition SieveSetoid : Setoid :=
    {|
      setoid_carrier := Sieve;
      setoid_eq A B := ∀ {d} (f : Arr d c), sieve_arrows A f ≡ sieve_arrows B f;
    |}.
  Next Obligation.
    split.
    - intros ? ??.
      reflexivity.
    - intros ?? H ??.
      symmetry.
      apply H.
    - intros ??? H H' ??.
      etransitivity.
      apply H.
      apply H'.
  Qed.

  Program Definition TotalSieve : SieveSetoid :=
    {|
      sieve_arrows d := λₛ f, True;
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    constructor.
  Qed.

End Sieves.

Arguments Sieve {_}.
Arguments TotalSieve {_ _}.
Arguments SieveSetoid {_}.
Arguments sieve_arrows {_ _ _ _}.
Arguments sieve_closed {_ _ _ _ _}.

Notation "'λᵢ' δ , e" :=
  {|
    sieve_arrows δ := e;
    sieve_closed := _
  |} (at level 120, δ binder, no associativity)
    : cat_scope.

Section SievesPSh.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.

  Local Axiom ID_epsilon :
    ∀ T : Type, ConstructiveIndefiniteDescription_on T.

  Program Definition PSh_sieve : PSh C :=
    {|
      FO x := SieveSetoid x;
      fmap A B := λₛ f :: @Arr C B A, λₛ s, λᵢ a, λₛ b, (s _ (f ∘ b));
    |}.
  Next Obligation.
    intros; simpl.
    split.
    - intros.
      simpl in *.
      rewrite <-(setoid_arr_eq _ _ (s a) (f ∘ a₁) (f ∘ a₂)); [assumption |].
      now f_equiv.
    - intros.
      simpl in *.
      rewrite (setoid_arr_eq _ _ (s a) (f ∘ a₁) (f ∘ a₂)); [assumption |].
      now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    simpl in *.
    rewrite (setoid_arr_eq _ _ (s e) (f ∘ (f0 ∘ g)) (f ∘ f0 ∘ g)).
    - now apply sieve_closed.
    - symmetry; apply arrow_comp_assoc.
  Qed.
  Next Obligation.
    intros; simpl.
    intros d g.
    apply (H d).
  Qed.
  Next Obligation.
    intros; simpl.
    intros a d f.
    now do 3 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros a; simpl.
    intros d f.
    unfold id.
    f_equiv.
    apply arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    intros a d h; simpl.
    f_equiv.
    apply arrow_comp_assoc.
  Qed.

  Program Definition PSh_true_arr
    : TerminalAsLimit (@PSh_hasLimits C) [~>] PSh_sieve
    := λₙ _, λₛ _, TotalSieve.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.

  Program Definition PSh_true_arr_mono
    : TerminalAsLimit (@PSh_hasLimits C) [⤷] PSh_sieve :=
    {|
      monic := PSh_true_arr;
    |}.
  Next Obligation.
    intros; simpl.
    intros X ? d f.
    reflexivity.
  Qed.

  Program Definition PSh_char {X Y : PSh C} (f : X [⤷] Y) : Y [~>] PSh_sieve :=
    λₙ c, λₛ x, λᵢ d, λₛ α, ∃ u : X d, (monic f d) u ≡ fmap Y α x.
  Next Obligation.
    intros; simpl.
    split; intros [u G]; exists u.
    - now rewrite <-H.
    - now rewrite H.
  Qed.
  Next Obligation.
    intros ??????? h g; simpl.
    intros [u G].
    exists (fmap X g u).
    pose proof (eta_comp (monic f) _ _ g u) as H.
    simpl in H.
    unfold compose in H.
    rewrite H; clear H.
    pose proof (@fmap_comp _ _ Y _ _ _ g h x) as J.
    simpl in J.
    rewrite J; clear J.
    unfold compose; simpl.
    f_equiv.
    apply G.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros d g.
    split; intros [u G]; exists u.
    - now rewrite <-H.
    - now rewrite H.
  Qed.
  Next Obligation.
    intros ????? h; simpl.
    intros a d g; split; intros [u G].
    - exists u.
      rewrite G.
      symmetry; apply (@fmap_comp _ _ Y _ _ _ g h a).
    - exists u.
      rewrite G.
      apply (@fmap_comp _ _ Y _ _ _ g h a).
  Qed.

  Lemma char_Pb {X Y : PSh C} (f : X [⤷] Y)
    : isPullback (PSh_char f)
        (PSh_true_arr)
        f
        (projT1 (terminal_proj X)).
  Proof.
    unshelve econstructor.
    - unshelve econstructor.
      intros x.
      simpl.
      intros; simpl.
      split; [constructor |].
      intros _.
      exists (fmap X f0 a).
      pose proof (eta_comp (monic f) _ _ f0 a) as H.
      simpl in H; unfold compose in H; simpl in H.
      apply H.
    - intros.
      unshelve eexists (λₙ x, _).
      + unshelve eexists.
        * intros w; simpl.
          pose proof (proj2 (CS_comm h j H x w x ı) I) as J.
          simpl in J.
          destruct (ID_epsilon _ _ J) as [J' _].
          apply J'.
        * intros; simpl.
          admit.
      + intros; simpl.
        intros; simpl.
        unfold compose; simpl.
        admit.
  Admitted.
End SievesPSh.
