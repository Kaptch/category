From category Require Import
                      base
                      setoid.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Local Open Scope setoid_scope.

Section Category.
  Record Category : Type :=
    {
      Obj :> Type;
      Arr : Obj → Obj → Setoid;
      arrow_id {A} : Arr A A;
      arrow_comp {A B C} : Arr B C [→] Arr A B [→] Arr A C;
      arrow_comp_id_l {A B} {f : Arr A B} : arrow_comp arrow_id f ≡ f;
      arrow_comp_id_r {A B} {f : Arr A B} : arrow_comp f arrow_id ≡ f;
      arrow_comp_assoc {A B C D} {h : Arr C D} {g : Arr B C} {f : Arr A B}
      : arrow_comp (arrow_comp h g) f ≡ arrow_comp h (arrow_comp g f);
      (* arrow_comp_assoc_sym {A B C D} {h : Arr C D} {g : Arr B C} {f : Arr A B} *)
      (* : arrow_comp h (arrow_comp g f) ≡ arrow_comp (arrow_comp h g) f; *)
    }.
End Category.

Arguments Arr {_}.
Arguments arrow_id {_}.
Arguments arrow_comp {_ _ _ _}.
Arguments arrow_comp_id_l {_ _ _}.
Arguments arrow_comp_id_r {_ _ _}.
Arguments arrow_comp_assoc {_ _ _ _ _}.
(* Arguments arrow_comp_assoc_sym {_ _ _ _ _}. *)

Notation "'ı'" := (arrow_id _) : cat_scope.
Notation "f ∘ g" := (arrow_comp f%cat g%cat) (at level 40, left associativity)
    : cat_scope.
Notation "a [~>] b" := (Arr a b) (at level 70, right associativity) : cat_scope.

Global Instance ArrCReflexive {C : Category} : CRelationClasses.Reflexive (@Arr C).
Proof.
  intros ?; apply arrow_id.
Qed.

Global Instance ArrCTransitive {C : Category} : CRelationClasses.Transitive (@Arr C).
Proof.
  intros ??? H G; eapply arrow_comp; eassumption.
Qed.

Section Op.
  Local Open Scope cat_scope.
  Context (C : Category).

  Program Definition Op : Category :=
    {|
      Obj := C;
      Arr A B := (B [~>] A)%cat;
      arrow_id A := ı;
      arrow_comp _ _ _ := flipS (arrow_comp);
      arrow_comp_id_l _ _ := arrow_comp_id_r;
      arrow_comp_id_r _ _ := arrow_comp_id_l;
      arrow_comp_assoc _ _ _ _ _ _ _ := _;
      (* arrow_comp_assoc_sym _ _ _ _ _ _ _ := arrow_comp_assoc _ _ _; *)
    |}.
  Next Obligation.
    intros; simpl.
    rewrite arrow_comp_assoc.
    reflexivity.
  Qed.
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

Global Instance IsoCReflexive {C : Category}
  : CRelationClasses.Reflexive (@Isomorphism C).
Proof.
  intros i.
  refine {|
      iso1 := ı%cat;
      iso2 := ı%cat;
    |}.
  - apply arrow_comp_id_l.
  - apply arrow_comp_id_l.
Defined.

Global Instance IsoCSymmetric {C : Category}
  : CRelationClasses.Symmetric (@Isomorphism C).
Proof.
  intros a b H.
  refine {|
      iso1 := iso2 H;
      iso2 := iso1 H;
    |}.
  - now rewrite iso21.
  - now rewrite iso12.
Defined.

Global Instance IsoCTransitive {C : Category}
  : CRelationClasses.Transitive (@Isomorphism C).
Proof.
  intros a b c H G.
  refine {|
      iso1 := (iso1 G ∘ iso1 H)%cat;
      iso2 := (iso2 H ∘ iso2 G)%cat;
    |}.
  - rewrite arrow_comp_assoc.
    rewrite <-(arrow_comp_assoc (G ⁻¹)%cat).
    rewrite iso12.
    rewrite arrow_comp_id_l.
    rewrite iso12.
    reflexivity.
  - rewrite arrow_comp_assoc.
    rewrite <-(arrow_comp_assoc H).
    rewrite iso21.
    rewrite arrow_comp_id_l.
    rewrite iso21.
    reflexivity.
Defined.

Global Instance IsoCEquiv {C : Category}
  : CRelationClasses.Equivalence (@Isomorphism C).
Proof.
  split; apply _.
Defined.

Section Mono.
  Local Open Scope cat_scope.
  Context {C : Category}.

  Record Monomorphism (A B : C) := {
      monic :> A [~>] B;
      monic_cancel : ∀ {D : C} (g₁ g₂ : D [~>] A), monic ∘ g₁ ≡ monic ∘ g₂ → g₁ ≡ g₂;
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
      epic_cancel : ∀ {D : C} (g₁ g₂ : B [~>] D), g₁ ∘ epic ≡ g₂ ∘ epic → g₁ ≡ g₂;
    }.
End Epi.

Arguments epic {_ _ _}.

Notation "A [⇥] B" := (Epimorphism A B) (at level 70, right associativity)
    : cat_scope.

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
    - now f_equiv.
    - now f_equiv.
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
