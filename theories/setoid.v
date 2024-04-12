From category Require Import
  base.

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

  Record SetoidArrBundle (A : Setoid) (B : Setoid) : Type :=
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

  Program Definition SetoidArr (A : Setoid) (B : Setoid) : Setoid :=
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

  Program Definition flipS {A B C : Setoid}
    : SetoidArr (SetoidArr A (SetoidArr B C)) (SetoidArr B (SetoidArr A C)) :=
    {|
      setoid_arr := λ f, {| setoid_arr := λ x, {| setoid_arr := λ y, f y x |} |};
    |}.
  Next Obligation.
    intros; simpl.
    now apply f.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?. now apply setoid_arr_eq.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ??.
    apply H.
  Qed.

  Program Definition constS {A B : Setoid} (b : B) :
    SetoidArr A B :=
    {|
      setoid_arr := λ _, b;
    |}.
  Next Obligation.
    intros; reflexivity.
  Qed.

  Global Instance SetoidArrProper {A B : Setoid} :
    Proper (@setoid_eq (SetoidArr A B) ==> @setoid_eq A ==> @setoid_eq B)
      (setoid_arr A B).
  Proof.
    intros ?? H t ? G.
    rewrite (H t).
    now apply setoid_arr_eq.
  Qed.

  Global Instance SetoidArrProper' {A B : Setoid} {f : SetoidArr A B} :
    Proper (@setoid_eq _ ==> @setoid_eq _) f.
  Proof.
    intros ???.
    now f_equiv.
  Qed.

  Program Definition SetoidProd (A : Setoid) (B : Setoid) : Setoid :=
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

  Program Definition SubsetSetoid (X : Setoid) (P : X → Prop) : Setoid :=
    {|
      setoid_carrier := { x : X | P x };
      setoid_eq a b := proj1_sig a ≡ proj1_sig b;
    |}.
  Next Obligation.
    intros; split.
    - intros ?; reflexivity.
    - intros ???; now symmetry.
    - intros ?????; etransitivity; eassumption.
  Qed.

  Program Definition QuotientSetoid (X : Setoid) (R : X → X → Prop)
    (Heq : Equivalence R) :=
    {|
      setoid_carrier := X;
      setoid_eq := R;
      setoid_equiv := Heq;
    |}.

End Setoids.

Arguments setoid_eq {_}.
Arguments setoid_equiv {_}.
Arguments setoid_arr {_ _} _ _ &.

Notation "a ≡ b" := (setoid_eq a b) (at level 70, no associativity)
    : setoid_scope.
Notation "a [→] b" := (SetoidArr a b) (at level 70, right associativity)
    : setoid_scope.
Notation "a × b" := (SetoidProd a b) (at level 70, right associativity)
    : setoid_scope.
Notation "[ a ]" := ({| setoid_carrier := a; setoid_eq := eq |}) : setoid_scope.
Notation "'λₛ' x , e" := ({| setoid_arr x := e; setoid_arr_eq := _ |})
                           (at level 120, x binder, no associativity)
    : setoid_scope.
Notation "'λₛ' x '::' t , e" := ({|
                                   setoid_arr (x : t%type) := e;
                                   setoid_arr_eq := _
                                 |})
                                 (at level 120, x binder, no associativity)
    : setoid_scope.

Notation "X '∕' R" := (QuotientSetoid X R _) (at level 70) : setoid_scope.

Definition unique_setoid {A : Setoid} (P : A → Type) (x : A) :=
  prod (P x) (forall (x' : A), P x' → (x ≡ x')%setoid).

Notation "'Σ' ! x .. y , p" :=
  (sigT (unique_setoid (fun x => .. (sigT (unique_setoid (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
      format "'[' 'Σ' ! '/ ' x .. y , '/ ' p ']'")
    : type_scope.
