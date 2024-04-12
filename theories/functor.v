From category Require Import
  base
  setoid
  category
  sets.

Section Functor.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.

  Record Functor (C : Category) (D : Category) : Type :=
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

  Lemma fmap_id' {X Y : Category} {G : Functor X Y}
    : ∀ {A} (f : (A [~>] A)%cat), (f ≡ ı)%cat → (fmap _ _ G f ≡ ı)%cat.
  Proof.
    intros ? f ->.
    apply fmap_id.
  Qed.

  Lemma fmap_comp' {X Y : Category} {G : Functor X Y}
    : ∀ {A B C} (f : (A [~>] C)%cat) (g : (B [~>] C)%cat) (h : (A [~>] B)%cat),
    (f ≡ g ∘ h)%cat → (fmap _ _ G f ≡ fmap _ _ G g ∘ fmap _ _ G h)%cat.
  Proof.
    intros ?????? ->.
    apply fmap_comp.
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

  Context {C : Category}.
  Context {D : Category}.
  Context (F G : C [⇒] D).

  Record NatTrans :=
    {
      eta {X : C} :> (F X [~>] G X)%cat;
      eta_comp {X Y : C} (f : X [~>] Y) : eta ∘ fmap F f ≡ fmap G f ∘ eta;
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
    now rewrite H.
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

  Context (C' : Category).
  Context (D' : Category).

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
    now rewrite arrow_comp_id_l arrow_comp_id_r.
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

Notation "a [↣] b" := (@Arr (FunCat _ _) a b) (at level 70, right associativity)
    : functor_scope.

Program Definition constantFuncReindex {C : Category} {D : Category} {x x' : D}
  (p : (x [~>] x')%cat)
  : (@constantFunc C D x [↣] @constantFunc C D x')%cat%functor :=
  (λₙ a, p)%functor.
Next Obligation.
  intros; simpl.
  now rewrite arrow_comp_id_l arrow_comp_id_r.
Qed.

Program Definition FunctorId {C : Category}
  : Functor C C :=
  {|
    FO x := x;
    fmap A B := (λₛ f, f)%setoid;
  |}.
Next Obligation.
  intros; now simpl.
Qed.
Next Obligation.
  intros; now simpl.
Qed.
Next Obligation.
  intros; now simpl.
Qed.

Program Definition FunctorCompose {A B C : Category} (F : Functor B C)
  (G : Functor A B) : Functor A C :=
  {|
    FO i := F (G i);
    fmap X Y := (λₛ f, fmap F (fmap G f))%setoid;
  |}.
Next Obligation.
  intros; simpl.
  now rewrite H.
Qed.
Next Obligation.
  intros; simpl.
  now rewrite ->2 fmap_id.
Qed.
Next Obligation.
  intros; simpl.
  now rewrite ->2 fmap_comp.
Qed.

Lemma FunctorComposeFmapIdL {A B : Category} (F : Functor A B)
  : ∀ {a b : A} (f : (a [~>] b)%cat), (fmap (FunctorCompose FunctorId F) f ≡ fmap F f)%setoid.
Proof.
  intros a b f.
  reflexivity.
Qed.

Lemma FunctorComposeFmapIdR {A B : Category} (F : Functor A B)
  : ∀ {a b : A} (f : (a [~>] b)%cat), (fmap (FunctorCompose F FunctorId) f ≡ fmap F f)%setoid.
Proof.
  intros a b f.
  reflexivity.
Qed.

Lemma FunctorComposeFmapAssoc {A B C D : Category}
  (F : Functor A B) (G : Functor B C) (H : Functor C D)
  : ∀ {a b : A} (f : (a [~>] b)%cat), (fmap (FunctorCompose H (FunctorCompose G F)) f ≡ fmap (FunctorCompose (FunctorCompose H G) F) f)%setoid.
Proof.
  intros a b f.
  reflexivity.
Qed.

Lemma FunctorComposeIdL {A B : Category} (F : Functor A B)
  : ∀ a, ((FunctorCompose FunctorId F) a = F a).
Proof.
  intros a.
  reflexivity.
Qed.

Lemma FunctorComposeIdR {A B : Category} (F : Functor A B)
  : ∀ a, ((FunctorCompose F FunctorId) a = F a).
Proof.
  intros a.
  reflexivity.
Qed.

Lemma FunctorComposeAssoc {A B C D : Category}
  (F : Functor A B) (G : Functor B C) (H : Functor C D)
  : ∀ a, ((FunctorCompose H (FunctorCompose G F)) a = (FunctorCompose (FunctorCompose H G) F) a).
Proof.
  intros a.
  reflexivity.
Qed.

Record FunctorSetoidBundle {A B : Category} (F G : Functor A B) : Prop :=
  {
    functor_obj_eq : ∀ x, F x = G x;
    functor_arr_eq : ∀ {a b : A} (f : (a [~>] b)%cat),
      (eq_rect _ (λ x, (G a [~>] x)%cat)
         (eq_rect _ (λ x, (x [~>] F b)%cat) (fmap F f) (G a) (functor_obj_eq a))
         (G b) (functor_obj_eq b) ≡ fmap G f)%setoid;
  }.

Program Definition FunctorProd {A B C D : Category} (F : Functor A C)
  (G : Functor B D) : Functor (A × B)%cat (C × D)%cat :=
  {|
    FO i := (F (fst i), G (snd i));
    fmap X Y := (λₛ f, (fmap F (fst f), fmap G (snd f)))%setoid;
  |}.
Next Obligation.
  intros ???? ?? [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
  split; now f_equiv.
Qed.
Next Obligation.
  intros ???? ?? [? ?]; simpl in *.
  now split; rewrite fmap_id.
Qed.
Next Obligation.
  intros ???? ?? [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
  now split; rewrite fmap_comp.
Qed.

Fixpoint endofunctor_n {C : Category} (F : Functor C C) (n : nat)
  : Functor C C :=
  match n with
  | 0 => F
  | S n' => FunctorCompose (endofunctor_n F n') F
  end.
