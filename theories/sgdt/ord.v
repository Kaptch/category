From category Require Import
  base
  setoid
  category
  sets
  terminal
  functor
  limit
  prod
  exp
  pullback
  subobject
  instances.sets
  instances.presheaf.

From stdpp Require Import
  base.

From category Require Import
  ordinals.set_ordinals
  ordinals.set_model
  ordinals.arithmetic
  ordinals.set_functions
  ordinals.stepindex.

Require Import sgdt.wf_IR.

Require Import classes.limits.
Require Import classes.exp.
Require Import classes.subobject.
Require Import internal_lang.presheaf.

Local Set Universe Polymorphism.

Local Open Scope cat_scope.
Local Open Scope functor_scope.

Lemma functor_iso_preserve {D E : Category}
    {G : D [⇒] E}
    {a b : D} : a ≃ b → G a ≃ G b.
  Proof.
    intros J.
    refine {|
        iso1 := functor.fmap G (iso1 J);
        iso2 := functor.fmap G (iso2 J);
      |}.
    - rewrite <-fmap_comp.
      rewrite iso12.
      apply fmap_id.
    - rewrite <-fmap_comp.
      rewrite iso21.
      apply fmap_id.
  Defined.

  Lemma iso_op {D : Category}
    {a b : D} : @Isomorphism D a b -> @Isomorphism (D op) a b.
  Proof.
    intros G.
    unshelve econstructor.
    - simpl.
      apply (iso2 G).
    - simpl.
      apply (iso1 G).
    - simpl.
      apply (iso12 G).
    - simpl.
      apply (iso21 G).
  Defined.

  Lemma iso_prod {D E : Category}
    (a b : D × E) : fst a ≃ fst b → snd a ≃ snd b → a ≃ b.
  Proof.
    intros G1 G2.
    destruct a, b.
    unshelve econstructor.
    - apply (iso1 G1, iso1 G2).
    - apply (iso2 G1, iso2 G2).
    - simpl; split;
        apply iso12.
    - simpl; split;
        apply iso21.
  Defined.

  Lemma iso_bifunc {C : Category}
    (F : (C op × C) [⇒] C)
    {a b : C}
    : a ≃ b → F (a, a) ≃ F (b, b).
  Proof.
    intros H.
    apply functor_iso_preserve.
    apply iso_prod.
    - apply iso_op, H.
    - apply H.
  Defined.

  Lemma fmap_comp_bifunc {X1 X2 Y : Category} {G : Functor (X1 × X2) Y}
    : ∀ {A1 B1 C1 : X1} {A2 B2 C2 : X2}
        (f1 : (A1 [~>] B1)%cat) (f2 : (A2 [~>] B2)%cat)
        (g1 : (B1 [~>] C1)%cat) (g2 : (B2 [~>] C2)%cat),
  setoid_eq (@functor.fmap (X1 × X2) Y G (A1, A2) (C1, C2) (g1 ∘ f1, g2 ∘ f2))
    ((@functor.fmap (X1 × X2) Y G (B1, B2) (C1, C2) (g1, g2))
       ∘ (@functor.fmap (X1 × X2) Y G (A1, A2) (B1, B2) (f1, f2))).
  Proof.
    intros.
    simpl.
    epose proof (@fmap_comp (X1 × X2) Y G
                   (A1, A2) (B1, B2) (C1, C2)
                   (g1, g2) (f1, f2)) as H.
    simpl in H.
    rewrite H.
    reflexivity.
  Qed.

Polymorphic Class Dist (SI: indexT) A := dist : SI → relation A.

Instance: Params (@dist) 4 := {}.
Notation "x ≡{ α }≡ y" := (dist α x y)
  (at level 70, α at next level, format "x  ≡{ α }≡  y").
Notation "x ≡{ α }@{ A }≡ y" := (dist (A:=A) α x y)
  (at level 70, α at next level, only parsing).

#[export] Hint Extern 0 (_ ≡{_}≡ _) => reflexivity : core.
#[export] Hint Extern 0 (_ ≡{_}≡ _) => symmetry; assumption : core.
Notation NonExpansive f := (∀ α, Proper (dist α ==> dist α) f).
Notation NonExpansive2 f := (∀ α, Proper (dist α ==> dist α ==> dist α) f).

Polymorphic Class Distance A `{!Equiv A, !Dist SI A} := {
  dist_equiv : ∀ x y, (∀ α, x ≡{α}≡ y) ↔ x ≡ y;
  dist_equivalence :: ∀ α, Equivalence (dist α);
  dist_downwards : ∀ α β x y, x ≡{α}≡ y → β ⪯ α → x ≡{β}≡ y;
}.

Global Instance dist_ne `{!Equiv A, !Dist SI A, !Distance A} α : Proper (dist α ==> dist α ==> iff) (@dist SI A _ α).
Proof. intros ?? Heq ?? Heq'; rewrite Heq Heq'; done. Qed.

Global Instance dist_proper `{!Equiv A, !Dist SI A, !Distance A} α : Proper ((≡) ==> (≡) ==> iff) (@dist SI A _ α).
Proof. intros ?? Heq ?? Heq'. eapply dist_equiv in Heq, Heq'; rewrite Heq Heq'; done. Qed.
Global Instance dist_proper_2 `{!Equiv A, !Dist SI A, !Distance A} α x : Proper ((≡) ==> iff) (dist α x).
Proof. apply dist_proper, dist_equiv; done. Qed.

Lemma dist_le `{!Equiv A, !Dist SI A, !Distance A} α α' x y : x ≡{α}≡ y → α' ⪯ α → x ≡{α'}≡ y.
Proof. destruct 2; eauto using dist_downwards; congruence. Qed.
Lemma dist_le' `{!Equiv A, !Dist SI A, !Distance A} α α' x y : α' ⪯ α → x ≡{α}≡ y → x ≡{α'}≡ y.
Proof. intros; eauto using dist_le. Qed.
Global Instance ne_proper
  `{!Equiv A, !Dist SI A, !Distance A}
  `{!Equiv B, !Dist SI B, !Distance B} (f : A → B) `{!NonExpansive f} :
  Proper ((≡) ==> (≡)) f | 100.
Proof. by intros x1 x2; rewrite -!dist_equiv; intros Hx n; rewrite (Hx n). Qed.
Global Instance ne_proper_2
  `{!Equiv A, !Dist SI A, !Distance A}
  `{!Equiv B, !Dist SI B, !Distance B}
  `{!Equiv C, !Dist SI C, !Distance C} (f : A → B → C) `{!NonExpansive2 f} :
  Proper ((≡) ==> (≡) ==> (≡)) f | 100.
Proof.
  unfold Proper, respectful; setoid_rewrite <- dist_equiv.
  by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
Qed.

Definition dist_later `{!Dist SI A} (α : SI) (x y : A) : Prop := ∀ β, β ≺ α → x ≡{β}≡ y.

Global Instance dist_later_equivalence `{!Dist SI A, !Equiv A} `{!Distance A} α : Equivalence (@dist_later SI A _ α).
Proof.
  split.
  - now intros ???.
  - unfold dist_later; intros ?? H ??; now rewrite H.
  - unfold dist_later; intros ??? H1 H2 ??; now rewrite H1 ?H2.
Qed.

Lemma dist_dist_later `{!Dist SI A, !Equiv A} `{!Distance A} α (x y : A) : dist α x y → dist_later α x y.
Proof. intros Heq ??; eapply dist_downwards; eauto. Qed.

Lemma dist_later_dist `{!Dist SI A, !Equiv A} `{!Distance A} α β (x y : A) : β ≺ α → dist_later α x y → dist β x y.
Proof. intros ? H; by apply H.  Qed.

Lemma dist_later_zero `{!Dist SI A, !Equiv A} `{!Distance A} (x y : A): dist_later zero x y.
Proof. intros ? [] % index_lt_zero_is_normal. Qed.

Lemma dist_later_succ `{!Dist SI A, !Equiv A} `{!Distance A} α (x y : A) : dist α x y → dist_later (succ α) x y.
Proof. intros Heq ??; eapply dist_downwards; [apply Heq | by apply index_succ_iff]. Qed.

Global Instance ne_dist_later `{!Dist SI A, !Equiv A} `{!Distance A} `{!Dist SI B, !Equiv B} `{!Distance B} (f : A → B) :
  NonExpansive f → ∀ α, Proper (dist_later α ==> dist_later α) f.
Proof. intros Hf ??????; by eapply Hf, H. Qed.

Global Instance ne2_dist_later_l
  `{!Dist SI A, !Equiv A} `{!Distance A}
  `{!Dist SI B, !Equiv B} `{!Distance B}
  `{!Dist SI C, !Equiv C} `{!Distance C} (f : A → B → C) :
  NonExpansive2 f → ∀ α, Proper (dist_later α ==> dist α ==> dist_later α) f.
Proof. intros H α a b H1 c d H2 β Hβ. apply H; eapply dist_downwards; eauto. Qed.
Global Instance ne2_dist_later_r
  `{!Dist SI A, !Equiv A} `{!Distance A}
  `{!Dist SI B, !Equiv B} `{!Distance B}
  `{!Dist SI C, !Equiv C} `{!Distance C} (f : A → B → C) :
  NonExpansive2 f → ∀ α, Proper (dist α ==> dist_later α ==> dist_later α) f.
Proof. intros H α a b H1 c d H2 β Hβ. apply H; eapply dist_downwards; eauto. Qed.

Notation Contractive f := (∀ α, Proper (dist_later α ==> dist α) f).

Global Instance const_contractive `{!Dist SI A, !Equiv A} `{!Distance A} `{!Dist SI B, !Equiv B} `{!Distance A} (x : A) :
  Contractive (@const A B x).
Proof. by intros α y1 y2. Qed.

Section contractive.
  Local Set Default Proof Using "Type*".
  Context `{!Dist SI A, !Equiv A} `{!Distance A} `{!Dist SI B, !Equiv B} `{!Distance B} (f : A → B) `{!Contractive f}.
  Implicit Types x y : A.

  Lemma contractive_0 x y : f x ≡{zero}≡ f y.
  Proof. by apply (_ : Contractive f), dist_later_zero. Qed.
  Lemma contractive_mono α x y : dist_later α x y → f x ≡{α}≡ f y.
  Proof. by apply (_ : Contractive f). Qed.

  Global Instance contractive_ne : NonExpansive f | 100.
  Proof.
    intros n x y ?; eapply dist_downwards with (α := succ n).
    - eapply contractive_mono.
      intros ??. eapply dist_le; eauto.
      by rewrite index_succ_iff.
    - apply index_lt_le_subrel, index_succ_greater.
  Qed.

  Global Instance contractive_proper : Proper ((≡) ==> (≡)) f | 100.
  Proof. intros ??; apply (ne_proper _). Qed.
End contractive.

(* Enriched categories and functors. *)

Global Instance ArrowEquiv (C : Category) :
  ∀ (a b : C), Equiv (a [~>] b).
Proof.
  intros a b.
  intros f g.
  apply (setoid_eq f g).
Defined.

Polymorphic Class EnrichedCategory SI (C : Category) := MkEnrCat {
  hom_dist :: ∀ a b, Dist SI (a [~>] b);
  hom_dist_distance :: ∀ a b, Distance (a [~>] b);
  comp_ne :: ∀ a b c, NonExpansive2 (setoid_arr (@arrow_comp C a b c));
}.
Global Arguments MkEnrCat {_ _} _ _ _.

Polymorphic Class EnrichedFunctor `{!EnrichedCategory SI C, !EnrichedCategory SI D} (F : Functor C D) := {
  h_map_ne :: ∀ a b, NonExpansive (@functor.fmap _ _ F a b)
}.

Polymorphic Class LocallyContractiveFunctor `{!EnrichedCategory SI C, !EnrichedCategory SI D} (F : Functor C D) := {
  h_map_contr :: ∀ a b, Contractive (@functor.fmap _ _ F a b)
}.

Global Instance enriched_compose
  `{!EnrichedCategory SI C, !EnrichedCategory SI D, !EnrichedCategory SI E}
  (F : Functor C D) `{!EnrichedFunctor F} (G : Functor D E) `{!EnrichedFunctor G} : EnrichedFunctor (FunctorCompose G F).
Proof. constructor; intros ??????; rewrite /=. by do 2 f_equiv. Qed.

Global Instance enriched_locally_contractive_compose
  `{!EnrichedCategory SI C, !EnrichedCategory SI D, !EnrichedCategory SI E}
  (F : Functor C D) `{!EnrichedFunctor F} (G : Functor D E) `{!LocallyContractiveFunctor G} :
  LocallyContractiveFunctor (FunctorCompose G F).
Proof.
  constructor; intros ????? Hdist; rewrite /=.
  apply h_map_contr; intros ??; apply h_map_ne; apply Hdist; done.
Qed.

Global Instance locally_contractive_enriched_compose
  `{!EnrichedCategory SI C, !EnrichedCategory SI D, !EnrichedCategory SI E}
  (F : Functor C D) `{!LocallyContractiveFunctor F} (G : Functor D E) `{!EnrichedFunctor G} :
  LocallyContractiveFunctor (FunctorCompose G F).
Proof.
  constructor; intros ????? Hdist; rewrite /=.
  apply h_map_ne; apply h_map_contr; intros ??; apply Hdist; done.
Qed.

Global Program Instance ProdCat_enriched {SI} `{EnrichedCategory SI C}
  `{EnrichedCategory SI D}
  : EnrichedCategory SI (C × D) :=
  MkEnrCat (λ _ _ α f g, fst f ≡{α}≡ fst g ∧ snd f ≡{α}≡ snd g) _ _.
Next Obligation.
  intros SI C ? D ? [a1 a2] [b1 b2].
  constructor.
  - intros [? ?] [? ?].
    split; intros HHH.
    + split.
      * apply dist_equiv; intros α.
        apply (proj1 (HHH α)).
      * apply dist_equiv; intros α.
        apply (proj2 (HHH α)).
    + intros α.
      split; apply dist_equiv, HHH.
  - intros α.
    apply _.
  - intros α β [f1 f2] [g1 g2] [H1 H2] G.
    split; apply (dist_downwards α); assumption.
Defined.
Next Obligation.
  intros ????? [? ?] [? ?] [? ?] ? [? ?] [? ?] [? ?] [? ?] [? ?] [? ?].
  split; by apply comp_ne.
Qed.

Global Program Instance OpCat_enriched {SI} `{EnrichedCategory SI C}
  : EnrichedCategory SI (C op) := _.
Next Obligation.
  intros.
  unshelve econstructor.
  - intros a b α f g.
    simpl in *.
    apply (f ≡{α}≡ g).
  - intros.
    apply (@hom_dist_distance _ _ H b a).
  - intros a b c α f g H1 h i H2.
    apply (@comp_ne SI C _ c b a α h i H2 f g H1).
Defined.

Global Instance const_functor_locally_contractive `{!EnrichedCategory SI C} c : LocallyContractiveFunctor (constantFunc c).
Proof. constructor; repeat intros ?; rewrite /=; done. Qed.

Global Instance id_functor_enriched `{!EnrichedCategory SI C} : EnrichedFunctor (@FunctorId C).
Proof. constructor; repeat intros ?; rewrite /=; done. Qed.

(* α-isomorphism *)

Record Aisomorphism `{!EnrichedCategory SI C} (α : SI) {a b} (f : a [~>] b) (g : b [~>] a) :=
MkAIso {
  Aiso_lr : g ∘ f ≡{α}≡ ı;
  Aiso_rl : f ∘ g ≡{α}≡ ı;
}.
Global Arguments MkAIso {_ _ _ _ _ _ _ _} _ _.
Global Arguments Aiso_lr {_ _ _ _ _ _ _ _} _.
Global Arguments Aiso_rl {_ _ _ _ _ _ _ _} _.

Record Aisomorphic `{!EnrichedCategory SI C} α a b := MkAIsoIc {
  Aforward : a [~>] b;
  Abackward : b [~>] a;
  Ais_iso : Aisomorphism α Aforward Abackward
}.
Global Arguments MkAIsoIc {_ _ _ _ _ _} _ _ _.
Global Arguments Aforward {_ _ _ _ _ _} _.
Global Arguments Abackward {_ _ _ _ _ _} _.
Global Arguments Ais_iso {_ _ _ _ _ _} _.

Infix "≃{ α }≃" := (Aisomorphic α) (at level 70, no associativity) : category_scope.
Infix "≃{ α }@{ C }≃" := (@Aisomorphic C _ α)
  (at level 70, only parsing, no associativity) : category_scope.

#[export] Hint Extern 1 (_ ≡{_}≡ _) => apply dist_equiv; assumption : core.

Lemma enr_func_iso_ne {C D : Category} `{!EnrichedCategory SI C, EnrichedCategory SI D} (F : Functor C D) `{!EnrichedFunctor F}
  α {a b} {f : a [~>] b} {g : b [~>] a} (aiso : @Aisomorphism SI C _ α _ _ f g) :
  Aisomorphism α (functor.fmap F f) (functor.fmap F g).
Proof.
  split.
  - rewrite -fmap_comp (Aiso_lr aiso) fmap_id //.
  - rewrite -fmap_comp (Aiso_rl aiso) fmap_id //.
Qed.

Global Instance locally_contractive_enriched
  `{!EnrichedCategory SI C, EnrichedCategory SI D} (F : Functor C D)
  `{!LocallyContractiveFunctor F} : EnrichedFunctor F.
Proof.
  constructor; intros ??????.
  apply h_map_contr.
  intros ? ?; eapply dist_le; first eassumption.
  apply index_lt_le_subrel; done.
Qed.

Lemma contr_func_iso_contr
  `{!EnrichedCategory SI C, EnrichedCategory SI D} (F : Functor C D) `{!LocallyContractiveFunctor F}
  α {a b} {f : a [~>] b} {g : b [~>] a}
  (aiso : ∀ β, β ≺ α → @Aisomorphism SI C _ β _ _ f g) :
  Aisomorphism α (functor.fmap F f) (functor.fmap F g).
Proof.
  split.
  - rewrite -fmap_comp -fmap_id.
    apply h_map_contr.
    intros β Hβ; apply (Aiso_lr (aiso β Hβ)).
  - rewrite -fmap_comp -fmap_id.
    apply h_map_contr.
    intros β Hβ; apply (Aiso_rl (aiso β Hβ)).
Qed.

Program Definition Aismorphism_id `{!EnrichedCategory SI C} α c : Aisomorphism α (@arrow_id C c) (@arrow_id C c) := MkAIso _ _.
Solve All Obligations with by repeat intros ?; rewrite arrow_comp_id_l.
Fail Next Obligation.

Definition Aismorphism_swap
  `{!EnrichedCategory SI C} {α} {a b} {f : a [~>] b} {g : b [~>] a} (iso : Aisomorphism α f g) : Aisomorphism α g f :=
  MkAIso (Aiso_rl iso) (Aiso_lr iso).

Program Definition Aismorphism_compose `{!EnrichedCategory SI C} {α} {a b c}
  {f : a [~>] b} {g : b [~>] a} (iso : Aisomorphism α f g)
  {h : b [~>] c} {i : c [~>] b} (iso : Aisomorphism α h i) : Aisomorphism α (h ∘ f) (g ∘ i) := MkAIso _ _.
Next Obligation.
  intros ??????? f g isofg h i isohi.
  rewrite (arrow_comp_assoc g) -(arrow_comp_assoc i).
  rewrite (comp_ne _ _ _ _ g g _ (i ∘ h ∘ f) f).
  - apply isofg.
  - reflexivity.
  - rewrite (comp_ne _ _ _ _ (i ∘ h) ı _ f f).
    + by rewrite arrow_comp_id_l.
    + apply isohi.
    + reflexivity.
Qed.
Next Obligation.
  intros ??????? f g isofg h i isohi.
  rewrite (arrow_comp_assoc h) -(arrow_comp_assoc f).
  rewrite (comp_ne _ _ _ _ h h _ (f ∘ g ∘ i) i).
  - apply isohi.
  - reflexivity.
  - rewrite (comp_ne _ _ _ _ (f ∘ g) ı _ i i).
    + by rewrite arrow_comp_id_l.
    + apply isofg.
    + reflexivity.
Qed.
Fail Next Obligation.

Definition isomorphic_refl `{!EnrichedCategory SI C} α (c : Obj C) : Aisomorphic α c c :=
  MkAIsoIc _ _ (Aismorphism_id _ _).
Definition isomorphic_symm `{!EnrichedCategory SI C} α (a b : Obj C) : Aisomorphic α a b → Aisomorphic α b a :=
  λ iso, MkAIsoIc _ _ (Aismorphism_swap (Ais_iso iso)).
Definition isomorphic_trans `{!EnrichedCategory SI C} α (a b c : Obj C) :
  Aisomorphic α a b → Aisomorphic α b c → Aisomorphic α a c :=
  λ iso1 iso2, MkAIsoIc _ _ (Aismorphism_compose (Ais_iso iso1) (Ais_iso iso2)).

Section Ord.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context (SI : indexT).

  Program Definition OrdCatArrSetoid (A B : SI) : Setoid :=
    {|
      setoid_carrier := A ⪯ B;
      setoid_eq (X Y : A ⪯ B) := X = Y;
    |}.

  Program Definition OrdCat : Category :=
    {|
      Obj := SI;
      Arr A B := OrdCatArrSetoid A B;
      arrow_id A := rc_refl _ A;
      arrow_comp A B C := (λₛ f, λₛ g, transitivity g f)%setoid;
    |}.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros ?.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.

  Program Definition cover_arrow_nat {n : OrdCat} : (zero : OrdCat) [~>] n.
  Proof.
    apply index_zero_minimum.
  Qed.

  Program Definition step_arrow_nat {n : OrdCat} : n [~>] (succ n).
  Proof.
    apply index_lt_le_subrel.
    apply index_succ_greater.
  Qed.

  Program Definition down_arrow_nat {n m : OrdCat}
    (f : (succ n : OrdCat) [~>] succ m)
    : n [~>] m.
  Proof.
    apply index_le_succ_inj.
    apply f.
  Qed.

  Program Definition up_arrow_nat {n m : OrdCat}
    (f : n [~>] m)
    : (succ n : OrdCat) [~>] succ m.
  Proof.
    apply index_le_succ_mono.
    apply f.
  Qed.

  Lemma fmap_irrel {X : PSh (OrdCat)} {n m : OrdCat} (f g : n [~>] m)
    (x : X m) : functor.fmap X f x ≡ functor.fmap X g x.
  Proof.
    simpl in *.
    now rewrite (proof_irrel f g).
  Qed.

  Program Definition basis_el (β : OrdCat) : Type := { α : OrdCat | α ⪯ β }.
End Ord.

Notation "'↓' β" := (basis_el β) (at level 50).

Section BoundedOrd.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {SI : indexT}.
  Context {P : SI → Prop}.
  Context {PI : ∀ α, ProofIrrel (P α)}.

  Definition BoundedOrdCatObj := { β : SI | P β }.

  Program Definition BoundedOrdCatArrSetoid (A B : BoundedOrdCatObj) : Setoid :=
    {|
      setoid_carrier := `A ⪯ `B;
      setoid_eq (X Y : `A ⪯ `B) := X = Y;
    |}.

  Program Definition BoundedOrdCat : Category :=
    {|
      Obj := BoundedOrdCatObj;
      Arr A B := BoundedOrdCatArrSetoid A B;
      arrow_id A := rc_refl _ A;
      arrow_comp A B C := (λₛ f, λₛ g, transitivity g f)%setoid;
    |}.
  Next Obligation.
    intros; simpl.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl; intros.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl.
    apply proof_irrel.
  Qed.

  Program Definition functor_bounded_restriction {C : Category}
    (F : Functor ((OrdCat SI) op) C)
    : Functor (BoundedOrdCat op) C :=
    {|
      FO X := F (`X);
      functor.fmap X Y := λₛ f,
        let (X, _) := X in
        let (Y, _) := Y in
        functor.fmap F f;
    |}.
  Next Obligation.
    intros; simpl.
    destruct X as [X ?];
      destruct Y as [Y ?].
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros.
    destruct A as [A ?].
    simpl.
    rewrite fmap_id.
    reflexivity.
  Defined.
  Next Obligation.
    intros ? ? X Y Z f g.
    destruct X as [X ?];
      destruct Y as [Y ?];
      destruct Z as [Z ?].
    simpl.
    rewrite fmap_comp.
    reflexivity.
  Defined.

  Lemma functor_bounded_restriction_agree {C : Category}
    (G : Functor ((OrdCat SI) op) C)
    (β : BoundedOrdCat) :
    (functor_bounded_restriction G) β = G (`β).
  Proof.
    reflexivity.
  Qed.

End BoundedOrd.

Ltac elim_eq_irrel := match goal with
                      | |- context G [eq_rect_r _ _ ?a] =>
                          try rewrite (proof_irrel a Logic.eq_refl)
                      end.

Section Temp.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Local Opaque has_limits.
  Local Opaque has_terminal.

  Context (SI : indexT).

  Context (C : Category).
  Context `{HE : EnrichedCategory SI C}.
  Context `{HL : hasLimits C}.
  Context (F : ((C op) × C) [⇒] C).

  Record Solution : Type :=
    {
      solution :> C;
      solution_correct : solution ≃ (F (solution, solution));
    }.

  Context {FC : LocallyContractiveFunctor F}.
  Context (el : 𝟙 @ C [~>] F (𝟙 @ C, 𝟙 @ C)).

  Set Transparent Obligations.

  Record hyp (P : SI → Prop) (X : ∀ α, P α → Obj C)
    (π : ∀ α β (H1 : P α) (H2 : P β), α ≺ β → (X α H1) [~>] (X β H2))
    (δ : ∀ α β (H1 : P α) (H2 : P β), α ≺ β → (X β H2) [~>] (X α H1))
    (ϕ : ∀ α (H : P α), (X α H) [~>] (F (X α H, X α H)))
    (ψ : ∀ α (H : P α), (F (X α H, X α H)) [~>] (X α H))
    :=
    {
      δπ α β H1 H2 Hlt : δ α β H1 H2 Hlt ∘ π α β H1 H2 Hlt ≡ ı;
      πδ α β H1 H2 Hlt : π α β H1 H2 Hlt ∘ δ α β H1 H2 Hlt ≡{α}≡ ı;
      π_comp α₁ α₂ α₃ Hα₁ Hα₂ Hα₃ Hlt1 Hlt2 Hlt3 :
      (π α₂ α₃ Hα₂ Hα₃ Hlt2) ∘ (π α₁ α₂ Hα₁ Hα₂ Hlt1) ≡ (π α₁ α₃ Hα₁ Hα₃ Hlt3);
      δ_comp α₁ α₂ α₃ Hα₁ Hα₂ Hα₃ Hlt1 Hlt2 Hlt3 :
      (δ α₁ α₂ Hα₁ Hα₂ Hlt1) ∘ (δ α₂ α₃ Hα₂ Hα₃ Hlt2) ≡ (δ α₁ α₃ Hα₁ Hα₃ Hlt3);
      ψϕ α Hα : (ψ α Hα) ∘ (ϕ α Hα) ≡ ı;
      ϕψ α Hα : (ϕ α Hα) ∘ (ψ α Hα) ≡{α}≡ ı;
      approx_eq α Ha Hsa : X (succ α) Hsa ≃ F ((X α Ha), (X α Ha));
      (* approx_eq_unique α Ha Hsa :  *)
      (*   ∀ (i : X (succ α) Hsa ≃ F ((X α Ha), (X α Ha))), *)
      (*   i ≡ approx_eq α Ha Hsa ∧ (i ⁻¹) ≡ (approx_eq α Ha Hsa ⁻¹); *)
      (* approx_π_fold_ϕ γ Hγ Hsγ (Hlt : γ ≺ succ γ) : *)
      (* π γ (succ γ) Hγ Hsγ Hlt ≡ ((approx_eq _ Hγ Hsγ) ⁻¹) ∘ ϕ γ Hγ; *)
    }.
  Arguments hyp {_} _ _ _ _ _.

  Record approx {P : SI → Prop} :=
    {
      approx_X : ∀ α, P α → C;
      approx_π : ∀ α₁ α₂ (Hα₁ : P α₁) (Hα₂ : P α₂),
        α₁ ≺ α₂ → approx_X α₁ Hα₁ [~>] approx_X α₂ Hα₂;
      approx_δ : ∀ α₁ α₂ (Hα₁ : P α₁) (Hα₂ : P α₂),
        α₁ ≺ α₂ → approx_X α₂ Hα₂ [~>] approx_X α₁ Hα₁;
      approx_ϕ : ∀ α (Hα : P α),
        approx_X α Hα [~>] F ((approx_X α Hα), (approx_X α Hα));
      approx_ψ : ∀ α (Hα : P α),
        F ((approx_X α Hα), (approx_X α Hα)) [~>] approx_X α Hα;
      approx_props : hyp approx_X approx_π approx_δ approx_ϕ approx_ψ
    }.
  Arguments approx _ : clear implicits.

  Program Definition approx_diagram {P : SI → Prop} {PI : ∀ a, ProofIrrel (P a)}
    (H : @approx P) : ((@BoundedOrdCat SI P) op) [⇒] C :=
    {|
      FO x := approx_X H (`x) (proj2_sig x);
    |}.
  Next Obligation.
    intros.
    destruct A, B.
    simpl.
    unshelve econstructor.
    + intros f.
      simpl in f.
      destruct (index_le_lt_eq_dec _ _ f).
      * by apply approx_δ.
      * subst.
        rewrite (proof_irrel p p0).
        apply ı.
    + intros; simpl.
      destruct H0.
      simpl.
      reflexivity.
  Defined.
  Next Obligation.
    intros ? ? ? [? ?].
    simpl.
    destruct (index_le_lt_eq_dec x x (rc_refl (≺) x)).
    + exfalso.
      by eapply index_lt_irrefl.
    + unfold eq_rect_r.
      simpl.
      assert ((Logic.eq_sym e) = Logic.eq_refl) as ->.
      { apply proof_irrel. }
      simpl.
      assert ((proof_irrel p p) = Logic.eq_refl) as ->.
      {
        unshelve eapply proof_irrel.
        apply eq_pi.
        intros z.
        left.
        apply proof_irrel.
      }
      simpl.
      reflexivity.
  Qed.
  Next Obligation.
    intros ? ? ? [? ?] [? ?] [? ?].
    simpl.
    intros.
    destruct (index_le_lt_eq_dec x0 x g).
    + destruct (index_le_lt_eq_dec x1 x0 f).
      * destruct (index_le_lt_eq_dec x1 x (transitivity f g)).
        -- symmetry. eapply δ_comp.
           apply H.
        -- subst.
           exfalso.
           apply (index_lt_irrefl _ (transitivity i i0)).
      * subst.
        destruct (index_le_lt_eq_dec x0 x (transitivity f g)).
        -- unfold eq_rect_r.
           simpl.
           destruct (Logic.eq_sym (proof_irrel p0 p1)).
           simpl.
           rewrite arrow_comp_id_l.
           rewrite (proof_irrel i i0).
           reflexivity.
        -- subst.
           exfalso.
           by eapply index_lt_irrefl.
    + subst.
      unfold eq_rect_r.
      simpl.
      destruct (Logic.eq_sym (proof_irrel p p0)).
      simpl.
      rewrite arrow_comp_id_r.
      assert (index_le_lt_eq_dec x1 x (transitivity f g) = index_le_lt_eq_dec x1 x f) as <-.
      {
        destruct (index_le_lt_eq_dec x1 x (transitivity f g));
          destruct (index_le_lt_eq_dec x1 x f).
        - f_equal.
          apply proof_irrel.
        - subst.
          exfalso.
          by eapply index_lt_irrefl.
        - subst.
          exfalso.
          by eapply index_lt_irrefl.
        - subst.
          f_equal.
          apply proof_irrel.
      }
      destruct (index_le_lt_eq_dec x1 x (transitivity f g)).
      * reflexivity.
      * subst.
        simpl.
        reflexivity.
  Qed.

  (* Program Definition solution_diagram {P : SI → Prop} {PI : ∀ a, ProofIrrel (P a)} *)
  (*   (H : @approx P) : ((@BoundedOrdCat SI P) op) [⇒] C := *)
  (*   {| *)
  (*     FO x := F (approx_diagram H x, approx_diagram H x); *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   intros ? ? ? [? ?] [? ?]. *)
  (*   simpl. *)
  (*   unshelve econstructor. *)
  (*   - simpl. *)
  (*     intros f. *)


  (* Record agree_fam {I : Type} {PI : I → (SI → Prop)} *)
  (*   {AI : ∀ (i : I), approx (PI i)} : Type := { *)
  (*     agree_eq : ∀ i j γ (H0 : PI i γ) (H1 : PI j γ), *)
  (*       (approx_X (AI i) γ H0) ≃ (approx_X (AI j) γ H1); *)
  (*     agree_coh  *)
  (*   }. *)

  Record approx_agree {P0 P1 : SI → Prop}
    {A0 : approx P0}
    {A1 : approx P1} : Type :=
    {
      agree_eq : ∀ γ (H0 : P0 γ) (H1 : P1 γ),
        (approx_X A0 γ H0) ≃ (approx_X A1 γ H1);
      (* agree_eq_unique : ∀ γ (H0 : P0 γ) (H1 : P1 γ), *)
      (*   ∀ (i : (approx_X A0 γ H0) ≃ (approx_X A1 γ H1)), *)
      (*   i ≡ agree_eq γ H0 H1 ∧ (i ⁻¹) ≡ (agree_eq γ H0 H1 ⁻¹); *)
      agree_π_nat : ∀ γ0 γ1 (Hlt : γ0 ≺ γ1)
                      (Hγ0 : P0 γ0) (Hγ0' : P1 γ0) (Hγ1 : P0 γ1) (Hγ1' : P1 γ1),
        approx_π A0 γ0 γ1 Hγ0 Hγ1 Hlt ≡
          ((agree_eq γ1 Hγ1 Hγ1') ⁻¹)
          ∘ approx_π A1 γ0 γ1 Hγ0' Hγ1' Hlt
          ∘ (agree_eq γ0 Hγ0 Hγ0');
      agree_δ_nat : ∀ γ0 γ1 (Hlt : γ0 ≺ γ1)
                      (Hγ0 : P0 γ0) (Hγ0' : P1 γ0) (Hγ1 : P0 γ1) (Hγ1' : P1 γ1),
        approx_δ A0 γ0 γ1 Hγ0 Hγ1 Hlt ≡
          ((agree_eq γ0 Hγ0 Hγ0') ⁻¹)
          ∘ approx_δ A1 γ0 γ1 Hγ0' Hγ1' Hlt
          ∘ (agree_eq γ1 Hγ1 Hγ1');
      agree_ϕ_nat : ∀ γ (Hγ : P0 γ) (Hγ' : P1 γ),
        approx_ϕ A0 γ Hγ ≡
          ((iso_bifunc F (agree_eq γ Hγ Hγ')) ⁻¹)
          ∘ approx_ϕ A1 γ Hγ'
          ∘ (agree_eq γ Hγ Hγ');
      agree_ψ_nat : ∀ γ (Hγ : P0 γ) (Hγ' : P1 γ),
        approx_ψ A0 γ Hγ ≡
          ((agree_eq γ Hγ Hγ') ⁻¹)
          ∘ approx_ψ A1 γ Hγ'
          ∘ (iso_bifunc F (agree_eq γ Hγ Hγ'));
    }.
  Arguments approx_agree {_ _} _ _.

  Lemma approx_agree_symmetric (P0 P1 : SI → Prop)
    (H0 : ∀ x, ProofIrrel (P0 x))
    (H1 : ∀ x, ProofIrrel (P1 x))
    A0 A1 : @approx_agree P0 P1 A0 A1 → @approx_agree P1 P0 A1 A0.
  Proof.
    intros H.
    unshelve econstructor.
    - intros.
      symmetry.
      apply H.
    - intros.
      unfold CRelationClasses.symmetry.
      simpl.
      epose proof (agree_π_nat H γ0 γ1 Hlt Hγ0' Hγ0 Hγ1' Hγ1) as G.
      simpl in G.
      rewrite G; clear G.
      rewrite <-2 arrow_comp_assoc.
      rewrite iso21.
      rewrite arrow_comp_id_l.
      rewrite arrow_comp_assoc.
      rewrite iso21.
      rewrite arrow_comp_id_r.
      reflexivity.
    - intros.
      unfold CRelationClasses.symmetry.
      simpl.
      epose proof (agree_δ_nat H γ0 γ1 Hlt Hγ0' Hγ0 Hγ1' Hγ1) as G.
      simpl in G.
      rewrite G; clear G.
      rewrite <-2 arrow_comp_assoc.
      rewrite iso21.
      rewrite arrow_comp_id_l.
      rewrite arrow_comp_assoc.
      rewrite iso21.
      rewrite arrow_comp_id_r.
      reflexivity.
    - intros.
      unfold CRelationClasses.symmetry.
      simpl.
      epose proof (agree_ϕ_nat H γ Hγ' Hγ) as G.
      simpl in G.
      rewrite G; clear G.
      rewrite <-2 arrow_comp_assoc.
      rewrite arrow_comp_assoc.
      rewrite <-fmap_comp.
      rewrite fmap_id'.
      + rewrite arrow_comp_id_l.
        rewrite iso21.
        rewrite arrow_comp_id_r.
        reflexivity.
      + simpl.
        split;
          rewrite iso21; reflexivity.
    - intros.
      unfold CRelationClasses.symmetry.
      simpl.
      epose proof (agree_ψ_nat H γ Hγ' Hγ) as G.
      simpl in G.
      rewrite G; clear G.
      rewrite <-2 arrow_comp_assoc.
      rewrite arrow_comp_assoc.
      rewrite <-fmap_comp.
      rewrite fmap_id'.
      + rewrite arrow_comp_id_r.
        rewrite iso21.
        rewrite arrow_comp_id_l.
        reflexivity.
      + simpl.
        split;
          rewrite iso21; reflexivity.
  Qed.

  Lemma approx_agree_reflexive (P : SI → Prop) (HP : ∀ x, ProofIrrel (P x)) A : @approx_agree P P A A.
  Proof.
    unshelve econstructor.
    - intros.
      rewrite (proof_irrel H0 H1).
      reflexivity.
    - intros; simpl.
      unfold eq_rect_r.
      destruct (Logic.eq_sym (proof_irrel Hγ0 Hγ0')).
      simpl.
      destruct (Logic.eq_sym (proof_irrel Hγ1 Hγ1')).
      simpl.
      rewrite arrow_comp_id_l arrow_comp_id_r.
      reflexivity.
    - unfold CRelationClasses.reflexivity.
      simpl.
      unfold eq_rect_r.
      intros.
      simpl.
      destruct (Logic.eq_sym (proof_irrel Hγ1 Hγ1')).
      simpl.
      destruct (Logic.eq_sym (proof_irrel Hγ0 Hγ0')).
      simpl.
      rewrite arrow_comp_id_l arrow_comp_id_r.
      reflexivity.
    - unfold CRelationClasses.reflexivity.
      simpl.
      unfold eq_rect_r.
      intros.
      simpl.
      destruct (Logic.eq_sym (proof_irrel Hγ Hγ')).
      simpl.
      rewrite fmap_id.
      rewrite arrow_comp_id_l arrow_comp_id_r.
      reflexivity.
    - unfold CRelationClasses.reflexivity.
      simpl.
      unfold eq_rect_r.
      intros.
      simpl.
      destruct (Logic.eq_sym (proof_irrel Hγ Hγ')).
      simpl.
      rewrite fmap_id.
      rewrite arrow_comp_id_l arrow_comp_id_r.
      reflexivity.
  Qed.

  Lemma approx_agree_transitive (P0 P1 P2 : SI → Prop)
    (H0 : ∀ x, ProofIrrel (P0 x))
    (H1 : ∀ x, ProofIrrel (P1 x))
    (H2 : ∀ x, ProofIrrel (P2 x))
    A0 A1 A2 :
    (∀ γ, P0 γ → P2 γ → P1 γ)
    → @approx_agree P0 P1 A0 A1
    → @approx_agree P1 P2 A1 A2 → @approx_agree P0 P2 A0 A2.
  Proof.
    intros H Hag0 Hag1.
    unshelve econstructor.
    - intros.
      etransitivity.
      + apply (agree_eq Hag0 _ _ (H _ H3 H4)).
      + apply (agree_eq Hag1 _ _ H4).
    - intros; simpl.
      epose proof (agree_π_nat Hag1 γ0 γ1 Hlt (H γ0 Hγ0 Hγ0') Hγ0' (H γ1 Hγ1 Hγ1') Hγ1') as G.
      rewrite ->2 arrow_comp_assoc.
      rewrite <-(arrow_comp_assoc (agree_eq Hag1 γ1 (H γ1 Hγ1 Hγ1') Hγ1' ⁻¹)).
      rewrite <-(arrow_comp_assoc _ (agree_eq Hag1 γ0 (H γ0 Hγ0 Hγ0') Hγ0')).
      rewrite <-G; clear G.
      rewrite <-arrow_comp_assoc.
      apply agree_π_nat.
    - intros; simpl.
      epose proof (agree_δ_nat Hag1 γ0 γ1 Hlt (H γ0 Hγ0 Hγ0') Hγ0' (H γ1 Hγ1 Hγ1') Hγ1') as G.
      rewrite ->2 arrow_comp_assoc.
      rewrite <-(arrow_comp_assoc (agree_eq Hag1 γ0 (H γ0 Hγ0 Hγ0') Hγ0' ⁻¹)).
      rewrite <-(arrow_comp_assoc _ (agree_eq Hag1 γ1 (H γ1 Hγ1 Hγ1') Hγ1')).
      rewrite <-G; clear G.
      rewrite <-arrow_comp_assoc.
      apply agree_δ_nat.
    - intros; simpl.
      rewrite fmap_comp_bifunc.
      epose proof (agree_ϕ_nat Hag1 γ (H γ Hγ Hγ') Hγ') as G.
      simpl in G.
      rewrite !arrow_comp_assoc.
      rewrite <-(arrow_comp_assoc (approx_ϕ A2 γ Hγ')).
      setoid_rewrite <-(arrow_comp_assoc (functor.fmap F _)) at 2.
      rewrite <-(arrow_comp_assoc _ (approx_ϕ A2 γ Hγ')).
      rewrite <-G; clear G.
      rewrite <-arrow_comp_assoc.
      apply agree_ϕ_nat.
    - intros; simpl.
      rewrite fmap_comp_bifunc.
      epose proof (agree_ψ_nat Hag1 γ (H γ Hγ Hγ') Hγ') as G.
      simpl in G.
      rewrite !arrow_comp_assoc.
      rewrite <-(arrow_comp_assoc (approx_ψ A2 γ Hγ')).
      rewrite <-(arrow_comp_assoc (agree_eq Hag1 γ (H γ Hγ Hγ') Hγ' ⁻¹)).
      rewrite <-(arrow_comp_assoc _ (approx_ψ A2 γ Hγ')).
      rewrite <-G.
      rewrite <-arrow_comp_assoc.
      apply agree_ψ_nat.
  Qed.

  Record extension {γ : SI} {A : approx (λ γ', γ' ≺ γ)} :=
    {
      ext_Xγ : C;
      ext_πγ : ∀ γ0 (Hγ0 : γ0 ≺ γ), approx_X A γ0 Hγ0 [~>] ext_Xγ;
      ext_δγ : ∀ γ0 (Hγ0 : γ0 ≺ γ), ext_Xγ [~>] approx_X A γ0 Hγ0;
      ext_ϕγ : ext_Xγ [~>] F (ext_Xγ, ext_Xγ);
      ext_ψγ : F (ext_Xγ, ext_Xγ) [~>] ext_Xγ;

      ext_δγ_πγ_id γ0 Hγ0 : ext_δγ γ0 Hγ0 ∘ ext_πγ γ0 Hγ0 ≡ ı;
      ext_πγ_δγ_id γ0 Hγ0 : ext_πγ γ0 Hγ0 ∘ ext_δγ γ0 Hγ0 ≡{γ0}≡ ı;
      ext_πγ_funct γ0 γ1 Hγ0 Hγ1 Hlt : ext_πγ γ1 Hγ1 ∘ approx_π A γ0 γ1 Hγ0 Hγ1 Hlt
                                         ≡ ext_πγ γ0 Hγ0;
      ext_δγ_funct γ0 γ1 Hγ0 Hγ1 Hlt : approx_δ A γ0 γ1 Hγ0 Hγ1 Hlt ∘ ext_δγ γ1 Hγ1
                                         ≡ ext_δγ γ0 Hγ0;

      ext_ψγ_ϕγ_id : ext_ψγ ∘ ext_ϕγ ≡ ı;
      ext_ϕγ_ψγ_id : ext_ϕγ ∘ ext_ψγ ≡{γ}≡ ı;

      ext_eq γ' (Hlt : γ' ≺ γ) : γ = succ γ' →
                                 ext_Xγ ≃ F (approx_X A γ' Hlt, approx_X A γ' Hlt);
      (* ext_eq_unique γ' (Hlt : γ' ≺ γ) P :  *)
      (*   ∀ (i : ext_Xγ ≃ F (approx_X A γ' Hlt, approx_X A γ' Hlt)), *)
      (*   i ≡ ext_eq γ' Hlt P ∧ (i ⁻¹) ≡ (ext_eq γ' Hlt P ⁻¹); *)
    }.
  Arguments extension {_} _.

  Record extension_agree {γ}
    {A0 A1 : approx (λ γ', γ' ≺ γ)}
    {E0 : extension A0}
    {E1 : extension A1}
    {H : approx_agree A0 A1} :=
    {
      eagree_eq : ext_Xγ E0 ≃ ext_Xγ E1;
      (* eagree_eq_unique :  *)
      (*   ∀ (i : ext_Xγ E0 ≃ ext_Xγ E1), *)
      (*   i ≡ eagree_eq ∧ (i ⁻¹) ≡ (eagree_eq ⁻¹); *)
      eagree_π_nat γ' Hγ' :
      ext_πγ E0 γ' Hγ' ≡ (eagree_eq ⁻¹)
        ∘ ext_πγ E1 γ' Hγ'
        ∘ (agree_eq H γ' Hγ' Hγ');
      eagree_δ_nat γ' Hγ' :
      ext_δγ E0 γ' Hγ' ≡ ((agree_eq H γ' Hγ' Hγ') ⁻¹)
        ∘ ext_δγ E1 γ' Hγ'
        ∘ eagree_eq;
      eagree_ϕ_nat :
      ext_ϕγ E0 ≡ ((iso_bifunc F eagree_eq) ⁻¹)
        ∘ ext_ϕγ E1
        ∘ eagree_eq;
      eagree_ψ_nat :
      ext_ψγ E0 ≡ (eagree_eq ⁻¹)
        ∘ ext_ψγ E1
        ∘ (iso_bifunc F eagree_eq);
    }.
  Arguments extension_agree {_ _ _} _ _ _.

  Section zero_case.
    Definition approx_base_π :
      ∀ α₁ α₂ : SI, α₁ ⪯ zero → α₂ ⪯ zero → α₁ ≺ α₂ → F (𝟙 @ C, 𝟙 @ C) [~>] F (𝟙 @ C, 𝟙 @ C).
    Proof.
      simpl.
      intros ? ? Hα₁ Hα₂ Hlt.
      exfalso.
      inversion Hα₁; subst;
        [| by eapply index_lt_zero_is_normal].
      inversion Hα₂; subst;
        [| by eapply index_lt_zero_is_normal].
      by eapply index_lt_irrefl.
    Defined.

    Definition approx_base_δ :
      ∀ α₁ α₂ : SI, α₁ ⪯ zero → α₂ ⪯ zero → α₁ ≺ α₂ → F (𝟙 @ C, 𝟙 @ C) [~>] F (𝟙 @ C, 𝟙 @ C).
    Proof.
      simpl.
      intros ? ? Hα₁ Hα₂ Hlt.
      exfalso.
      inversion Hα₁; subst;
        [| by eapply index_lt_zero_is_normal].
      inversion Hα₂; subst;
        [| by eapply index_lt_zero_is_normal].
      by eapply index_lt_irrefl.
    Defined.

    Definition approx_base_ϕ :
      ∀ α : SI, α ⪯ zero → F (𝟙 @ C, 𝟙 @ C) [~>] F (F (𝟙 @ C, 𝟙 @ C), F (𝟙 @ C, 𝟙 @ C)).
    Proof using C F HL SI el.
      simpl.
      intros.
      apply (functor.fmap F).
      simpl.
      apply (! @ C, el).
    Defined.

    Definition approx_base_ψ :
      ∀ α : SI, α ⪯ zero → F (F (𝟙 @ C, 𝟙 @ C), F (𝟙 @ C, 𝟙 @ C)) [~>] F (𝟙 @ C, 𝟙 @ C).
    Proof using C F HL SI el.
      intros.
      apply (functor.fmap F).
      simpl.
      apply (el, ! @ C).
    Defined.

    Lemma approx_base_iso :
      ∀ α : SI,
      α ⪯ zero → succ α ⪯ zero → F (𝟙 @ C, 𝟙 @ C) ≃ F (F (𝟙 @ C, 𝟙 @ C), F (𝟙 @ C, 𝟙 @ C)).
    Proof.
      intros ? ? Hle.
      exfalso.
      inversion Hle; subst;
        [| by eapply index_lt_zero_is_normal].
      by eapply index_succ_not_zero.
    Qed.

    Lemma approx_base_δπ :
      ∀ (α β : SI) (H1 : α ⪯ zero) (H2 : β ⪯ zero) (Hlt : α ≺ β),
      approx_base_δ α β H1 H2 Hlt ∘ approx_base_π α β H1 H2 Hlt ≡ ı.
    Proof.
      intros ? ? Hα₁ Hα₂ Hlt.
      exfalso.
      inversion Hα₁; subst;
        [| by eapply index_lt_zero_is_normal].
      inversion Hα₂; subst;
        [| by eapply index_lt_zero_is_normal].
      by eapply index_lt_irrefl.
    Qed.

    Lemma approx_base_πδ :
      ∀ (α β : SI) (H1 : α ⪯ zero) (H2 : β ⪯ zero) (Hlt : α ≺ β),
      approx_base_π α β H1 H2 Hlt ∘ approx_base_δ α β H1 H2 Hlt ≡{α}≡ ı.
    Proof.
      intros ? ? Hα₁ Hα₂ Hlt.
      exfalso.
      inversion Hα₁; subst;
        [| by eapply index_lt_zero_is_normal].
      inversion Hα₂; subst;
        [| by eapply index_lt_zero_is_normal].
      by eapply index_lt_irrefl.
    Qed.

    Lemma approx_base_π_comp :
      ∀ (α₁ α₂ α₃ : SI) (Hα₁ : α₁ ⪯ zero) (Hα₂ : α₂ ⪯ zero) (Hα₃ : α₃ ⪯ zero)
        (Hlt1 : α₁ ≺ α₂) (Hlt2 : α₂ ≺ α₃) (Hlt3 : α₁ ≺ α₃),
      approx_base_π α₂ α₃ Hα₂ Hα₃ Hlt2 ∘ approx_base_π α₁ α₂ Hα₁ Hα₂ Hlt1
        ≡ approx_base_π α₁ α₃ Hα₁ Hα₃ Hlt3.
    Proof.
      intros ? ? ? Hα₁ Hα₂ ? Hlt.
      exfalso.
      inversion Hα₁; subst;
        [| by eapply index_lt_zero_is_normal].
      inversion Hα₂; subst;
        [| by eapply index_lt_zero_is_normal].
      by eapply index_lt_irrefl.
    Qed.

    Lemma approx_base_δ_comp :
      ∀ (α₁ α₂ α₃ : SI) (Hα₁ : α₁ ⪯ zero) (Hα₂ : α₂ ⪯ zero) (Hα₃ : α₃ ⪯ zero)
        (Hlt1 : α₁ ≺ α₂) (Hlt2 : α₂ ≺ α₃) (Hlt3 : α₁ ≺ α₃),
      approx_base_δ α₁ α₂ Hα₁ Hα₂ Hlt1 ∘ approx_base_δ α₂ α₃ Hα₂ Hα₃ Hlt2
        ≡ approx_base_δ α₁ α₃ Hα₁ Hα₃ Hlt3.
    Proof.
      intros ? ? ? Hα₁ Hα₂ ? Hlt.
      exfalso.
      inversion Hα₁; subst;
        [| by eapply index_lt_zero_is_normal].
      inversion Hα₂; subst;
        [| by eapply index_lt_zero_is_normal].
      by eapply index_lt_irrefl.
    Qed.

    Lemma approx_base_ψϕ :
      ∀ (α : SI) (Hα : α ⪯ zero), approx_base_ψ α Hα ∘ approx_base_ϕ α Hα ≡ ı.
    Proof.
      intros; simpl.
      unfold approx_base_ψ, approx_base_ϕ.
      rewrite <-fmap_comp, <-fmap_id.
      f_equiv.
      split.
      + erewrite <-(snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) _);
          last done.
        simpl.
        by apply (snd (projT2 (@terminal_proj _ _ _)) _).
      + erewrite <-(snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) _);
          last done.
        by apply (snd (projT2 (@terminal_proj _ _ _)) _).
    Qed.

    Lemma approx_base_ϕψ :
      ∀ (α : SI) (Hα : α ⪯ zero), approx_base_ϕ α Hα ∘ approx_base_ψ α Hα ≡{α}≡ ı.
    Proof using C F FC HE HL SI el.
      intros.
      unfold approx_base_ψ, approx_base_ϕ.
      rewrite <-fmap_comp, <-fmap_id.
      apply contractive_mono; [apply FC |].
      rewrite (index_zero_is_unique α); [apply dist_later_zero |].
      intros β Hcontra.
      eapply index_lt_zero_is_normal.
      apply (index_lt_le_trans _ _ _ Hcontra Hα).
    Qed.

    Lemma approx_base_hyp :
      hyp (λ (α : SI) (_ : α ⪯ zero), F (𝟙 @ C, 𝟙 @ C)) approx_base_π approx_base_δ
        approx_base_ϕ approx_base_ψ.
    Proof using C F FC HE HL SI el.
      unshelve econstructor.
      - apply approx_base_δπ.
      - apply approx_base_πδ.
      - apply approx_base_π_comp.
      - apply approx_base_δ_comp.
      - apply approx_base_ψϕ.
      - apply approx_base_ϕψ.
      - apply approx_base_iso.
      (* - intros; simpl. *)
      (*   exfalso. *)
      (*   inversion Hsa; subst; *)
      (*     [| by eapply index_lt_zero_is_normal]. *)
      (*   by eapply index_succ_not_zero. *)
      (* - intros ? ? Hcontra. *)
      (*   exfalso. *)
      (*   rewrite index_succ_iff in Hcontra. *)
      (*   apply index_lt_succ_inj in Hcontra. *)
      (*   by eapply index_lt_zero_is_normal. *)
    Qed.

    Program Definition approx_base : @approx (λ x, x ⪯ zero) :=
      Build_approx _ (λ _ _, F (𝟙 @ C, 𝟙 @ C))
        approx_base_π
        approx_base_δ
        approx_base_ϕ
        approx_base_ψ
        approx_base_hyp.

  End zero_case.

  Unset Program Cases.

  Section succ_case.
    Context (β : SI).
    Context (IH : @approx (λ γ, γ ≺ succ β)).

    Lemma succ_char γ (Hγ : γ ≺ succ β) : { γ ≺ β } + { γ = β}.
    Proof.
      destruct (index_le_lt_dec β γ) as [H1 | H1].
      - right. apply index_succ_iff in Hγ. by apply index_le_ge_eq.
      - by left.
    Qed.

    Definition ext_succ_obj : C :=
      (F (((approx_X IH) β (index_succ_greater β)),
           ((approx_X IH) β (index_succ_greater β)))).

    Definition ext_succ_πγ :
      ∀ (γ0 : SI) (Hγ0 : γ0 ≺ succ β), approx_X IH γ0 Hγ0 [~>] ext_succ_obj.
    Proof.
      intros γ Hγ.
      destruct (succ_char γ Hγ) as [Hγ' | Hγ'].
      + apply ((approx_ϕ IH β (index_succ_greater β)) ∘
                 (approx_π IH γ β Hγ (index_succ_greater β) Hγ')).
      + subst.
        rewrite (proof_irrel Hγ (index_succ_greater β)).
        apply (approx_ϕ IH β (index_succ_greater β)).
    Defined.

    Definition ext_succ_δγ :
      ∀ (γ0 : SI) (Hγ0 : γ0 ≺ succ β), ext_succ_obj [~>] approx_X IH γ0 Hγ0.
    Proof.
      intros γ Hγ.
      destruct (succ_char γ Hγ) as [Hγ' | Hγ'].
      + apply ((approx_δ IH γ β Hγ (index_succ_greater β) Hγ') ∘
                 (approx_ψ IH β (index_succ_greater β))).
      + subst.
        rewrite (proof_irrel Hγ (index_succ_greater β)).
        apply (approx_ψ IH β (index_succ_greater β)).
    Defined.

    Definition ext_succ_ϕγ : ext_succ_obj [~>] F (ext_succ_obj, ext_succ_obj).
    Proof.
      apply (functor.fmap F).
      simpl.
      apply (approx_ψ IH β (index_succ_greater β),
              approx_ϕ IH β (index_succ_greater β)).
    Defined.

    Definition ext_succ_ψγ : F (ext_succ_obj, ext_succ_obj) [~>] ext_succ_obj.
    Proof.
      apply (functor.fmap F).
      simpl.
      apply (approx_ϕ IH β (index_succ_greater β),
              approx_ψ IH β (index_succ_greater β)).
    Defined.

    Lemma ext_succ_δπ :
      ∀ (γ0 : SI) (Hγ0 : γ0 ≺ succ β), ext_succ_δγ γ0 Hγ0 ∘ ext_succ_πγ γ0 Hγ0 ≡ ı.
    Proof.
      intros γ Hγ.
      unfold ext_succ_δγ, ext_succ_πγ.
      simpl.
      destruct (succ_char γ Hγ) as [Hγ' | Hγ'].
      + rewrite arrow_comp_assoc.
        rewrite <-(arrow_comp_assoc (approx_ψ IH β (index_succ_greater β))).
        rewrite (ψϕ _ _ _ _ _ _ (approx_props IH) β (index_succ_greater β)).
        rewrite arrow_comp_id_l.
        apply (δπ _ _ _ _ _ _ (approx_props IH) γ β Hγ (index_succ_greater β) Hγ').
      + subst.
        unfold eq_rect_r.
        destruct (Logic.eq_sym (proof_irrel Hγ (index_succ_greater β))).
        simpl.
        destruct (Logic.eq_sym (proof_irrel (index_succ_greater β) (index_succ_greater β))).
        simpl.
        apply (ψϕ _ _ _ _ _ _ (approx_props IH)).
    Qed.

    Lemma ext_succ_πδ :
      ∀ (γ0 : SI) (Hγ0 : γ0 ≺ succ β), ext_succ_πγ γ0 Hγ0 ∘ ext_succ_δγ γ0 Hγ0 ≡{γ0}≡ ı.
    Proof.
      intros γ Hγ.
      unfold ext_succ_δγ, ext_succ_πγ.
      simpl.
      destruct (succ_char γ Hγ) as [Hγ' | Hγ'].
      + rewrite arrow_comp_assoc.
        rewrite <-(arrow_comp_assoc (approx_π IH γ β Hγ (index_succ_greater β) Hγ')).
        pose proof (πδ _ _ _ _ _ _ (approx_props IH) γ β Hγ (index_succ_greater β) Hγ').
        rewrite (comp_ne _ _ _ γ (approx_ϕ IH β (index_succ_greater β))
                   (approx_ϕ IH β (index_succ_greater β))
                   (reflexivity _)
                   (approx_π IH γ β Hγ (index_succ_greater β) Hγ'
                      ∘ approx_δ IH γ β Hγ (index_succ_greater β) Hγ'
                      ∘ approx_ψ IH β (index_succ_greater β))
                   (approx_ψ IH β (index_succ_greater β))).
        * eapply dist_downwards.
          -- apply (ϕψ _ _ _ _ _ _ (approx_props IH)).
          -- apply index_lt_le_subrel, Hγ'.
        * rewrite comp_ne; [|
                             apply (πδ _ _ _ _ _ _ (approx_props IH)
                                      γ β Hγ (index_succ_greater β) Hγ')
                           |];
            [rewrite arrow_comp_id_l; reflexivity | reflexivity].
      + subst.
        unfold eq_rect_r.
        simpl.
        destruct (Logic.eq_sym (proof_irrel Hγ (index_succ_greater β))).
        simpl.
        apply (ϕψ _ _ _ _ _ _ (approx_props IH)).
    Qed.

    Lemma ext_succ_πγ_funct :
      ∀ (γ0 γ1 : SI) (Hγ0 : γ0 ≺ succ β) (Hγ1 : γ1 ≺ succ β) (Hlt : γ0 ≺ γ1),
      ext_succ_πγ γ1 Hγ1 ∘ approx_π IH γ0 γ1 Hγ0 Hγ1 Hlt ≡ ext_succ_πγ γ0 Hγ0.
    Proof.
      intros γ0 γ1 Hγ0 Hγ1 Hlt.
      unfold ext_succ_πγ.
      simpl.
      destruct (succ_char γ0 Hγ0) as [Hγ0' | Hγ0'];
        destruct (succ_char γ1 Hγ1) as [Hγ1' | Hγ1'].
      + rewrite arrow_comp_assoc.
        f_equiv.
        apply (π_comp _ _ _ _ _ _ (approx_props IH)).
      + subst.
        unfold eq_rect_r.
        simpl.
        destruct (Logic.eq_sym (proof_irrel Hγ1 (index_succ_greater β))).
        simpl.
        f_equiv.
        rewrite (proof_irrel Hlt Hγ0').
        reflexivity.
      + subst.
        exfalso.
        eapply index_lt_irrefl.
        apply (index_lt_trans β γ1 β Hlt Hγ1').
      + subst.
        exfalso.
        by eapply index_lt_irrefl.
    Qed.

    Lemma ext_succ_δγ_funct :
      ∀ (γ0 γ1 : SI) (Hγ0 : γ0 ≺ succ β) (Hγ1 : γ1 ≺ succ β) (Hlt : γ0 ≺ γ1),
      approx_δ IH γ0 γ1 Hγ0 Hγ1 Hlt ∘ ext_succ_δγ γ1 Hγ1 ≡ ext_succ_δγ γ0 Hγ0.
    Proof.
      intros γ0 γ1 Hγ0 Hγ1 Hlt.
      unfold ext_succ_δγ.
      simpl.
      destruct (succ_char γ1 Hγ1) as [Hγ1' | Hγ1'];
        destruct (succ_char γ0 Hγ0) as [Hγ0' | Hγ0'].
      + rewrite <-arrow_comp_assoc.
        do 2 f_equiv.
        apply (δ_comp _ _ _ _ _ _ (approx_props IH)).
      + subst.
        exfalso.
        eapply index_lt_irrefl.
        apply (index_lt_trans β γ1 β Hlt Hγ1').
      + subst.
        unfold eq_rect_r.
        simpl.
        destruct (Logic.eq_sym (proof_irrel Hγ1 (index_succ_greater β))).
        simpl.
        rewrite (proof_irrel Hlt Hγ0').
        reflexivity.
      + subst.
        exfalso.
        by eapply index_lt_irrefl.
    Qed.

    Lemma ext_succ_ψϕ :
      ext_succ_ψγ ∘ ext_succ_ϕγ ≡ ı.
    Proof.
      unfold ext_succ_ψγ, ext_succ_ϕγ.
      simpl.
      setoid_rewrite <-fmap_comp.
      setoid_rewrite <-fmap_id.
      f_equiv.
      simpl.
      split;
        apply (ψϕ _ _ _ _ _ _ (approx_props IH)).
    Qed.

    Lemma ext_succ_ϕψ :
      ext_succ_ϕγ ∘ ext_succ_ψγ ≡{succ β}≡ ı.
    Proof using C F FC HE IH SI β.
      simpl.
      setoid_rewrite <-fmap_comp.
      setoid_rewrite <-fmap_id.
      apply contractive_mono; [apply FC |].
      apply dist_later_succ.
      split;
        apply (ϕψ _ _ _ _ _ _ (approx_props IH)).
    Qed.

    Lemma ext_succ_eq :
      ∀ (γ' : SI) (Hlt : γ' ≺ succ β),
      succ β = succ γ' → ext_succ_obj ≃ F (approx_X IH γ' Hlt, approx_X IH γ' Hlt).
    Proof.
      intros γ' Hlt Heq.
      apply index_succ_inj in Heq.
      subst.
      rewrite (proof_irrel Hlt (index_succ_greater β)).
      reflexivity.
    Defined.

    Program Definition succ_extension : extension IH.
    Proof using C F FC HE IH SI β.
      unshelve econstructor.
      - apply ext_succ_obj.
      - apply ext_succ_πγ.
      - apply ext_succ_δγ.
      - apply ext_succ_ϕγ.
      - apply ext_succ_ψγ.
      - apply ext_succ_δπ.
      - apply ext_succ_πδ.
      - apply ext_succ_πγ_funct.
      - apply ext_succ_δγ_funct.
      - apply ext_succ_ψϕ.
      - apply ext_succ_ϕψ.
      - apply ext_succ_eq.
    Defined.
  End succ_case.

  Definition succ_extension_iso β (A0 A1 : approx (λ γ, γ ≺ succ β))
    (G : approx_agree A0 A1) :
    ext_Xγ (succ_extension β A0) ≃ ext_Xγ (succ_extension β A1).
  Proof.
    set (t1 := ext_eq (succ_extension β A0) β (index_succ_greater β) Logic.eq_refl).
    set (t1' := ext_eq (succ_extension β A1) β (index_succ_greater β) Logic.eq_refl).
    set (t2 := iso_bifunc F (agree_eq G β (index_succ_greater β) (index_succ_greater β))).
    refine {|
        iso1 := ((t1' ⁻¹) ∘ t2 ∘ t1);
        iso2 := ((t1 ⁻¹) ∘ (t2 ⁻¹) ∘ t1');
      |}.
    + rewrite ->arrow_comp_assoc.
      rewrite <-2 (arrow_comp_assoc t1').
      rewrite iso21.
      rewrite arrow_comp_id_l.
      rewrite arrow_comp_assoc.
      rewrite <-(arrow_comp_assoc (t2 ⁻¹)).
      rewrite iso12.
      rewrite arrow_comp_id_l.
      apply iso12.
    + rewrite ->arrow_comp_assoc.
      rewrite <-2 (arrow_comp_assoc t1).
      rewrite iso21.
      rewrite arrow_comp_id_l.
      rewrite arrow_comp_assoc.
      rewrite <-(arrow_comp_assoc t2).
      rewrite iso21.
      rewrite arrow_comp_id_l.
      apply iso12.
  Defined.

  Lemma succ_extension_coherent β (A0 A1 : approx (λ γ, γ ≺ succ β)) :
    ∀ H : approx_agree A0 A1,
    @extension_agree (succ β) A0 A1 (succ_extension β A0) (succ_extension β A1) H.
  Proof.
    intros G.
    unshelve econstructor.
    - by apply succ_extension_iso.
    - simpl.
      intros γ' Hγ'.
      unfold ext_succ_πγ, ext_succ_eq.
      destruct (succ_char β γ' Hγ') as [T | T].
      + unfold eq_rect_r.
        simpl.
        assert ((index_succ_inj β β Logic.eq_refl)
                = Logic.eq_refl) as ->.
        { apply proof_irrel. }
        simpl.
        destruct (Logic.eq_sym (proof_irrel (index_succ_greater β) (index_succ_greater β))).
        simpl.
        rewrite arrow_comp_id_l.
        rewrite arrow_comp_id_r.
        rewrite (agree_ϕ_nat G β (index_succ_greater β) (index_succ_greater β)).
        simpl.
        rewrite !arrow_comp_assoc.
        do 2 f_equiv.
        rewrite (agree_π_nat G γ' β T Hγ' Hγ'
                   (index_succ_greater β) (index_succ_greater β)).
        rewrite arrow_comp_assoc.
        rewrite <-(arrow_comp_assoc (agree_eq G β (index_succ_greater β) (index_succ_greater β))).
        rewrite iso21.
        rewrite arrow_comp_id_l.
        reflexivity.
      + subst.
        unfold eq_rect_r.
        simpl.
        destruct (Logic.eq_sym (proof_irrel Hγ' (index_succ_greater β))).
        simpl.
        assert ((index_succ_inj β β Logic.eq_refl)
                = Logic.eq_refl) as ->.
        { apply proof_irrel. }
        simpl.
        destruct (Logic.eq_sym (proof_irrel (index_succ_greater β) (index_succ_greater β))).
        simpl.
        rewrite arrow_comp_id_l.
        rewrite arrow_comp_id_r.
        apply agree_ϕ_nat.
    - intros.
      simpl.
      unfold ext_succ_δγ, ext_succ_eq.
      destruct (succ_char β γ' Hγ') as [H | H].
      + assert (index_succ_inj β β Logic.eq_refl = Logic.eq_refl) as ->.
        { apply proof_irrel. }
        simpl.
        unfold eq_rect_r.
        destruct (Logic.eq_sym (proof_irrel (index_succ_greater β) (index_succ_greater β))).
        simpl.
        rewrite arrow_comp_id_l arrow_comp_id_r.
        rewrite (agree_δ_nat G γ' β H Hγ' Hγ' (index_succ_greater β) (index_succ_greater β)).
        rewrite !arrow_comp_assoc.
        f_equiv.
        f_equiv.
        rewrite (agree_ψ_nat G β (index_succ_greater β) (index_succ_greater β)).
        rewrite <-! arrow_comp_assoc.
        rewrite iso21.
        rewrite arrow_comp_id_l.
        simpl.
        reflexivity.
      + subst.
        unfold eq_rect_r.
        simpl.
        destruct (Logic.eq_sym (proof_irrel Hγ' (index_succ_greater β))).
        simpl.
        assert (index_succ_inj β β Logic.eq_refl = Logic.eq_refl) as ->.
        { apply proof_irrel. }
        simpl.
        destruct (Logic.eq_sym (proof_irrel (index_succ_greater β) (index_succ_greater β))).
        simpl.
        rewrite arrow_comp_id_l arrow_comp_id_r.
        apply agree_ψ_nat.
    - simpl.
      unfold ext_succ_ϕγ, ext_succ_eq.
      assert (index_succ_inj β β Logic.eq_refl = Logic.eq_refl) as ->.
      { apply proof_irrel. }
      simpl.
      unfold CRelationClasses.reflexivity.
      simpl.
      unfold eq_rect_r.
      simpl.
      destruct (Logic.eq_sym (proof_irrel (index_succ_greater β) (index_succ_greater β))).
      simpl.
      rewrite <- arrow_comp_assoc.
      rewrite arrow_comp_id_r.
      rewrite <- arrow_comp_assoc.
      rewrite arrow_comp_id_r.
      rewrite arrow_comp_assoc.
      rewrite <-fmap_comp.
      simpl.
      rewrite <-fmap_comp.
      f_equiv.
      split; simpl.
      + rewrite arrow_comp_id_l arrow_comp_id_r.
        apply agree_ψ_nat.
      + rewrite arrow_comp_id_l arrow_comp_id_r.
        rewrite <-arrow_comp_assoc.
        apply agree_ϕ_nat.
    - simpl.
      unfold ext_succ_ψγ, ext_succ_eq.
      assert (index_succ_inj β β Logic.eq_refl = Logic.eq_refl) as ->.
      { apply proof_irrel. }
      simpl.
      unfold CRelationClasses.reflexivity.
      simpl.
      unfold eq_rect_r.
      simpl.
      destruct (Logic.eq_sym (proof_irrel (index_succ_greater β) (index_succ_greater β))).
      simpl.
      rewrite !arrow_comp_assoc.
      rewrite ->2 arrow_comp_id_l.
      rewrite <-arrow_comp_assoc.
      rewrite <-fmap_comp.
      rewrite <-fmap_comp.
      f_equiv.
      simpl.
      split.
      + rewrite arrow_comp_id_l arrow_comp_id_r.
        rewrite <-arrow_comp_assoc.
        apply agree_ϕ_nat.
      + rewrite arrow_comp_id_l arrow_comp_id_r.
        apply agree_ψ_nat.
  Qed.

  (* Section lim_case. *)
  (*   Context (β : @limit_idx SI) (IH : @approx (λ γ, γ ≺ β)). *)

  (*   Program Definition blim_diagram : *)
  (*     ((@BoundedOrdCat SI (limit_index β)) op) [⇒] C := *)
  (*     {| *)
  (*       FO (γ : (@BoundedOrdCat SI (limit_index β)) op) := F (approx_X IH (`γ) (proj2_sig γ), approx_X IH (`γ) (proj2_sig γ)); *)
  (*       (* functor.fmap A B := λₛ f, _; *) *)
  (*     |}. *)
  (*   Next Obligation. *)
  (*     intros. *)
  (*     unshelve econstructor. *)
  (*     - intros f. *)
  (*       destruct A, B. *)
  (*       apply functor.fmap. *)
  (*       simpl. *)
  (*       simpl in *. *)
  (*       destruct (index_le_lt_eq_dec _ _ f) as [G | G]. *)
  (*       + apply (approx_π _ _ _ _ _ G, approx_δ _ _ _ _ _ G). *)
  (*       + subst. *)
  (*         simpl. *)
  (*         assert (i = i0) as ->. *)
  (*         { apply proof_irrel. } *)
  (*         apply (ı, ı). *)
  (*     - intros; simpl. *)
  (*       simpl in H. *)
  (*       subst. *)
  (*       reflexivity. *)
  (*   Defined. *)
  (*   Next Obligation. *)
  (*     intros. *)
  (*     unfold blim_diagram_obligation_1. *)
  (*     destruct A. *)
  (*     simpl. *)
  (*     destruct (index_le_lt_eq_dec x x (rc_refl (≺) x)) as [H | H]. *)
  (*     - exfalso. *)
  (*       by eapply index_lt_irrefl. *)
  (*     - assert (H = Logic.eq_refl) as ->. *)
  (*       { apply proof_irrel. } *)
  (*       unfold eq_rect_r. *)
  (*       simpl. *)
  (*       assert ((proof_irrel i i) = Logic.eq_refl) as ->. *)
  (*       { unshelve eapply proof_irrel. *)
  (*         apply eq_pi. *)
  (*         intros z. *)
  (*         left. *)
  (*         apply proof_irrel. *)
  (*       } *)
  (*       simpl. *)
  (*       rewrite fmap_id. *)
  (*       reflexivity. *)
  (*   Qed. *)
  (*   Next Obligation. *)
  (*     intros; simpl. *)
  (*     destruct A, B, C0. *)
  (*     simpl in *. *)
  (*     destruct (index_le_lt_eq_dec x1 x0 f) as [H | H]; *)
  (*       destruct (index_le_lt_eq_dec x0 x g) as [G | G]. *)
  (*     - unfold eq_rect_r. *)
  (*       destruct (index_le_lt_eq_dec x1 x (transitivity f g)) as [J | J]. *)
  (*       + rewrite <-fmap_comp. *)
  (*         f_equiv. *)
  (*         split; simpl. *)
  (*         * rewrite π_comp. *)
  (*           2: apply IH. *)
  (*           reflexivity. *)
  (*         * rewrite δ_comp. *)
  (*           2: apply IH. *)
  (*           reflexivity. *)
  (*       + subst. *)
  (*         simpl. *)
  (*         exfalso. *)
  (*         apply (index_lt_irrefl _ (transitivity H G)). *)
  (*     - subst. *)
  (*       destruct (index_le_lt_eq_dec x1 x (transitivity f g)) as [J | J]. *)
  (*       + rewrite <-fmap_comp. *)
  (*         f_equiv. *)
  (*         split; simpl. *)
  (*         * unfold eq_rect_r. *)
  (*           simpl. *)
  (*           destruct (Logic.eq_sym (proof_irrel i i0)). *)
  (*           simpl. *)
  (*           rewrite arrow_comp_id_l. *)
  (*           rewrite (proof_irrel H J). *)
  (*           reflexivity. *)
  (*         * unfold eq_rect_r. *)
  (*           simpl. *)
  (*           destruct (Logic.eq_sym (proof_irrel i i0)). *)
  (*           simpl. *)
  (*           rewrite arrow_comp_id_r. *)
  (*           rewrite (proof_irrel H J). *)
  (*           reflexivity. *)
  (*       + subst. *)
  (*         exfalso. *)
  (*         by eapply index_lt_irrefl. *)
  (*     - subst. *)
  (*       destruct (index_le_lt_eq_dec x0 x (transitivity f g)) as [J | J]. *)
  (*       + rewrite <-fmap_comp. *)
  (*         f_equiv. *)
  (*         split; simpl. *)
  (*         * unfold eq_rect_r. *)
  (*           simpl. *)
  (*           destruct (Logic.eq_sym (proof_irrel i0 i1)). *)
  (*           simpl. *)
  (*           rewrite arrow_comp_id_r. *)
  (*           rewrite (proof_irrel G J). *)
  (*           reflexivity. *)
  (*         * unfold eq_rect_r. *)
  (*           simpl. *)
  (*           destruct (Logic.eq_sym (proof_irrel i0 i1)). *)
  (*           simpl. *)
  (*           rewrite arrow_comp_id_l. *)
  (*           rewrite (proof_irrel G J). *)
  (*           reflexivity. *)
  (*       + subst. *)
  (*         exfalso. *)
  (*         by eapply index_lt_irrefl. *)
  (*     - subst. *)
  (*       destruct (index_le_lt_eq_dec x x (transitivity f g)) as [J | J]. *)
  (*       + exfalso. *)
  (*         by eapply index_lt_irrefl. *)
  (*       + unfold eq_rect_r. *)
  (*         simpl. *)
  (*         destruct (Logic.eq_sym (proof_irrel i i0)). *)
  (*         simpl. *)
  (*         assert (J = Logic.eq_refl) as ->. *)
  (*         { apply proof_irrel. } *)
  (*         simpl. *)
  (*         destruct (Logic.eq_sym (proof_irrel i0 i1)). *)
  (*         simpl. *)
  (*         rewrite fmap_id. *)
  (*         rewrite arrow_comp_id_l. *)
  (*         reflexivity. *)
  (*   Qed. *)

  (*   Let XXX := (cone_obj (terminal_obj (limit_obj (has_limits blim_diagram)))). *)
  (*   Let π γ Hγ : ∀ X : BoundedOrdCat op, (Δ approx_X IH γ Hγ) X [~>] blim_diagram X. *)
  (*   Proof. *)
  (*     intros γ'. *)
  (*     destruct (index_lt_eq_lt_dec (`γ') γ). *)
  (*     + destruct s. *)
  (*       * apply ((approx_ϕ IH (`γ') (proj2_sig γ')) *)
  (*                  ∘ approx_δ IH _ _ (proj2_sig γ') Hγ i). *)
  (*       * subst. *)
  (*         simpl. *)
  (*         rewrite (proof_irrel (proj2_sig γ') Hγ). *)
  (*         apply (approx_ϕ IH (`γ') Hγ). *)
  (*     + apply (((approx_ϕ IH (`γ') (proj2_sig γ'))) *)
  (*                ∘ approx_π IH _ _ Hγ (proj2_sig γ') i). *)
  (*   Defined. *)
  (*   Let δ γ Hγ : XXX [~>] approx_X IH γ Hγ := *)
  (*         ((approx_ψ IH γ Hγ) ∘ cone_nat (terminal_obj (limit_obj (has_limits blim_diagram))) (Specif.exist _ γ Hγ)). *)


  (*   Program Definition limit_extension : extension IH. *)
  (*   Proof. *)
  (*     unshelve econstructor. *)
  (*     - apply XXX. *)
  (*     - intros; simpl. *)
  (*       pose proof (π γ0 Hγ0 (Specif.exist _ γ0 Hγ0)). *)
  (*       simpl in X. *)
  (*       admit. *)
  (*     - intros; simpl. *)
  (*       apply δ. *)
  (*     - *)
  (*   Admitted. *)

  (* End lim_case. *)

  (* Section limit_coherent. *)
  (*   Context (β : @limit_idx SI) (A0 A1 : approx (λ γ, γ ≺ β)) *)
  (*     (H : approx_agree A0 A1). *)

  (*   (* Lemma limit_extension_coherent : *) *)
  (*   (*   @extension_agree β A0 A1 (limit_extension β A0) (limit_extension β A1) H. *) *)
  (*   (* Proof. *) *)
  (*   (* Admitted. *) *)

  (* End limit_coherent. *)

  Section merge_extension.
    Context (β: SI).
    Context (A : approx (λ γ, γ ≺ β)).
    Context (E : extension A).

    Lemma le_lt_eq_dec γ (Hγ : γ ⪯ β) : {γ ≺ β} + {γ= β}.
    Proof.
      destruct (index_le_lt_dec β γ) as [H1 | H1].
      - right. by apply index_le_ge_eq.
      - by left.
    Qed.

    Program Definition extended_approx : @approx (λ γ, γ ⪯ β).
    Proof using A C E F HL SI β.
      unshelve econstructor.
      - intros α Hα.
        destruct (le_lt_eq_dec α Hα) as [Hα' | _].
        + apply (approx_X A α Hα').
        + apply (ext_Xγ E).
      - intros α1 α2 Hα1 Hα2 Hα; simpl.
        destruct (le_lt_eq_dec α1 Hα1) as [Hα1' | _];
          destruct (le_lt_eq_dec α2 Hα2) as [Hα2' | _].
        + by apply (approx_π A).
        + apply (ext_πγ E).
        + apply (ext_δγ E).
        + apply ı.
      - intros α1 α2 Hα1 Hα2 Hα; simpl.
        destruct (le_lt_eq_dec α1 Hα1) as [Hα1' | _];
          destruct (le_lt_eq_dec α2 Hα2) as [Hα2' | _].
        + by apply (approx_δ A).
        + apply (ext_δγ E).
        + apply (ext_πγ E).
        + apply ı.
      - intros α Hα; simpl.
        destruct (le_lt_eq_dec α Hα) as [Hα' | Hα'].
        + apply approx_ϕ.
        + subst.
          apply ext_ϕγ.
      - intros α Hα; simpl.
        destruct (le_lt_eq_dec α Hα) as [Hα' | Hα'].
        + apply approx_ψ.
        + subst.
          apply ext_ψγ.
      - simpl.
        unshelve econstructor.
        + intros α α' H1 H2 Hlt.
          destruct (le_lt_eq_dec α H1) as [H1' | H1'];
            destruct (le_lt_eq_dec α' H2) as [H2' | H2'].
          * eapply δπ, A.
          * subst.
            apply ext_δγ_πγ_id.
          * subst.
            exfalso.
            eapply index_lt_irrefl.
            apply (index_lt_trans β _ β Hlt H2').
          * by rewrite arrow_comp_id_l.
        + intros α α' H1 H2 Hlt.
          destruct (le_lt_eq_dec α H1) as [H1' | H1'];
            destruct (le_lt_eq_dec α' H2) as [H2' | H2'].
          * eapply πδ, A.
          * subst.
            apply ext_πγ_δγ_id.
          * subst.
            exfalso.
            eapply index_lt_irrefl.
            apply (index_lt_trans α' _ α' H2' Hlt ).
          * by rewrite arrow_comp_id_l.
        + intros α α' α'' H1 H2 H3 Hlt1 Hlt2 Hlt3.
          destruct (le_lt_eq_dec α H1) as [H1' | H1'];
            destruct (le_lt_eq_dec α' H2) as [H2' | H2'];
            destruct (le_lt_eq_dec α'' H3) as [H3' | H3'].
          * rewrite π_comp; [| apply A].
            reflexivity.
          * subst.
            apply ext_πγ_funct.
          * subst.
            exfalso.
            eapply index_lt_irrefl.
            apply (index_lt_trans α'' _ α'' H3' Hlt2).
          * rewrite arrow_comp_id_l.
            reflexivity.
          * subst.
            exfalso.
            eapply index_lt_irrefl.
            apply (index_lt_trans α'' _ α'' H3' Hlt3).
          * subst.
            exfalso.
            by eapply index_lt_irrefl.
          * rewrite arrow_comp_id_r.
            reflexivity.
          * rewrite arrow_comp_id_r.
            reflexivity.
        + intros α α' α'' H1 H2 H3 Hlt1 Hlt2 Hlt3.
          destruct (le_lt_eq_dec α H1) as [H1' | H1'];
            destruct (le_lt_eq_dec α' H2) as [H2' | H2'];
            destruct (le_lt_eq_dec α'' H3) as [H3' | H3'].
          * rewrite δ_comp; [| apply A].
            reflexivity.
          * subst.
            apply ext_δγ_funct.
          * subst.
            exfalso.
            eapply index_lt_irrefl.
            apply (index_lt_trans α'' _ α'' H3' Hlt2).
          * rewrite arrow_comp_id_r.
            reflexivity.
          * subst.
            exfalso.
            eapply index_lt_irrefl.
            apply (index_lt_trans α'' _ α'' H3' Hlt3).
          * subst.
            exfalso.
            by eapply index_lt_irrefl.
          * rewrite arrow_comp_id_l.
            reflexivity.
          * rewrite arrow_comp_id_r.
            reflexivity.
        + intros α Hα.
          destruct (le_lt_eq_dec α Hα) as [Hα' | Hα'].
          * eapply ψϕ, A.
          * subst.
            unfold eq_rect_r.
            simpl.
            apply ext_ψγ_ϕγ_id.
        + intros α Hα.
          destruct (le_lt_eq_dec α Hα) as [Hα' | Hα'].
          * eapply ϕψ, A.
          * subst.
            unfold eq_rect_r.
            simpl.
            apply ext_ϕγ_ψγ_id.
        + intros α Hα Hsα.
          destruct (le_lt_eq_dec (succ α) Hsα) as [Hα' | Hα'];
            destruct (le_lt_eq_dec α Hα) as [Hα'' | Hα''].
          * eapply approx_eq, A.
          * subst.
            exfalso.
            eapply index_lt_irrefl.
            apply (index_lt_trans (succ β) _ (succ β) Hα' (index_succ_greater β)).
          * subst.
            by apply ext_eq.
          * subst.
            exfalso.
            pose proof (index_succ_greater α) as Hcontra.
            rewrite <-Hα'' in Hcontra.
            by eapply index_lt_irrefl.
    Defined.

    Lemma extended_approx_agree : approx_agree A extended_approx.
    Proof.
      unshelve econstructor.
      - intros γ G1 G2.
        simpl.
        destruct (le_lt_eq_dec γ G2) as [Hα' | ?].
        + by rewrite (proof_irrel G1 Hα').
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
      - simpl.
        intros.
        destruct (le_lt_eq_dec γ1 Hγ1') as [H | H];
          unfold eq_rect_r, CRelationClasses.reflexivity; simpl.
        + destruct (Logic.eq_sym (proof_irrel Hγ1 H)); simpl.
          rewrite arrow_comp_id_l.
          destruct (le_lt_eq_dec γ0 Hγ0') as [G | G].
          * destruct (Logic.eq_sym (proof_irrel Hγ0 G)).
            simpl.
            rewrite arrow_comp_id_r.
            reflexivity.
          * subst.
            exfalso.
            by eapply index_lt_irrefl.
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
      - simpl.
        intros.
        destruct (le_lt_eq_dec γ0 Hγ0') as [H | H].
        + unfold eq_rect_r.
          destruct (Logic.eq_sym (proof_irrel Hγ0 H)).
          simpl.
          rewrite arrow_comp_id_l.
          destruct (le_lt_eq_dec γ1 Hγ1') as [G | G].
          * destruct (Logic.eq_sym (proof_irrel Hγ1 G)).
            simpl.
            rewrite arrow_comp_id_r.
            reflexivity.
          * subst.
            exfalso.
            by eapply index_lt_irrefl.
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
      - simpl.
        intros γ Hγ Hγ'.
        destruct (le_lt_eq_dec γ Hγ') as [Hγ1 | Hγ1].
        + destruct (proof_irrel Hγ Hγ1).
          simpl.
          rewrite arrow_comp_id_r.
          rewrite fmap_id.
          rewrite arrow_comp_id_l.
          reflexivity.
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
      - intros; simpl.
        destruct (le_lt_eq_dec γ Hγ') as [Hγ1 | Hγ1].
        + destruct (proof_irrel Hγ Hγ1).
          simpl.
          rewrite arrow_comp_id_l.
          rewrite fmap_id.
          rewrite arrow_comp_id_r.
          reflexivity.
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
    Qed.
  End merge_extension.

  Lemma extension_coherent β (A0 A1 : approx (λ γ, γ ≺ β))
    (E0 : extension A0) (E1 : extension A1) :
    ∀ H : approx_agree A0 A1,
    @extension_agree β A0 A1 E0 E1 H
    → approx_agree
        (extended_approx β A0 E0)
        (extended_approx β A1 E1).
  Proof.
    intros G1 G2.
    unshelve econstructor.
    - intros γ Hγ1 Hγ2.
      simpl.
      rewrite (proof_irrel Hγ1 Hγ2).
      destruct (le_lt_eq_dec β γ Hγ2) as [Hγ' | ?].
      + by apply agree_eq.
      + subst.
        apply G2.
    - intros; simpl.
      destruct (proof_irrel Hγ0 Hγ0').
      unfold eq_rect_r.
      simpl.
      destruct (le_lt_eq_dec β γ0 Hγ0) as [H | H].
      + destruct (Logic.eq_sym (proof_irrel Hγ1 Hγ1')).
        simpl.
        destruct (le_lt_eq_dec β γ1 Hγ1') as [G | G].
        * apply agree_π_nat.
        * subst.
          simpl.
          apply eagree_π_nat.
      + subst.
        destruct (Logic.eq_sym (proof_irrel Hγ1 Hγ1')).
        simpl.
        destruct (le_lt_eq_dec β γ1 Hγ1') as [H | H].
        * exfalso.
          apply (index_lt_irrefl _ (transitivity Hlt H)).
        * subst.
          simpl.
          rewrite arrow_comp_id_r.
          rewrite iso12.
          reflexivity.
    - intros; simpl.
      unfold eq_rect_r.
      destruct (proof_irrel Hγ1 Hγ1').
      simpl.
      destruct (Logic.eq_sym (proof_irrel Hγ0 Hγ0')).
      simpl.
      destruct (le_lt_eq_dec β γ0 Hγ0') as [H | H].
      + destruct (le_lt_eq_dec β γ1 Hγ1) as [G | G].
        * apply agree_δ_nat.
        * subst.
          simpl.
          apply eagree_δ_nat.
      + subst.
        simpl.
        destruct (le_lt_eq_dec β γ1 Hγ1) as [G | G].
        * exfalso.
          apply (index_lt_irrefl _ (transitivity Hlt G)).
        * subst.
          exfalso.
          by eapply index_lt_irrefl.
    - intros γ Hγ Hγ'.
      unfold eq_rect_r.
      destruct (proof_irrel Hγ Hγ').
      simpl.
      destruct (le_lt_eq_dec β γ Hγ) as [Hγ1 | Hγ1].
      + apply agree_ϕ_nat.
      + subst.
        unfold eq_rect_r.
        simpl.
        apply eagree_ϕ_nat.
    - intros γ Hγ Hγ'.
      unfold eq_rect_r.
      destruct (proof_irrel Hγ Hγ').
      simpl.
      destruct (le_lt_eq_dec β γ Hγ) as [Hγ1 | Hγ1].
      + apply agree_ψ_nat.
      + subst.
        unfold eq_rect_r.
        simpl.
        apply eagree_ψ_nat.
  Qed.

  (* TODO: unique iso??? *)
  (* TODO: coherent iso (additional structure) *)
  Section merge.
    Context (P : SI → Prop).
    Context (IH : ∀ α, P α → approx (λ γ, γ ⪯ α)).
    Context (IH_agree : ∀ α0 α1 Hα0 Hα1, approx_agree (IH α0 Hα0) (IH α1 Hα1)).

    (* ??? *)
    Lemma aaaaa (α1 α2 α3 : SI)
      (Hα1 : P α1)
      (Hα2 : P α2)
      (Hα3 : P α3)
      (Hlt1 : α1 ≺ α2)
      (Hlt2 : α2 ≺ α3)
      (Hlt3 : α1 ≺ α3)
      : agree_eq (IH_agree α2 α3 Hα2 Hα3) α1 (index_lt_le_subrel α1 α2 Hlt1)
          (index_lt_le_subrel α1 α3 Hlt3)
          ∘ agree_eq (IH_agree α1 α2 Hα1 Hα2) α1 (reflexivity α1) (index_lt_le_subrel α1 α2 Hlt1)
          ≡ agree_eq (IH_agree α1 α3 Hα1 Hα3) α1 (reflexivity α1) (index_lt_le_subrel α1 α3 Hlt3).
    Proof.
    Admitted.

    (* ??? *)
    Lemma bbbbb (α1 α2 α3 : SI)
      (Hα1 : P α1)
      (Hα2 : P α2)
      (Hα3 : P α3)
      (Hlt1 : α1 ≺ α2)
      (Hlt2 : α2 ≺ α3)
      (Hlt3 : α1 ≺ α3)
      : agree_eq (IH_agree α1 α2 Hα1 Hα2) α1 (reflexivity α1) (index_lt_le_subrel α1 α2 Hlt1) ⁻¹
  ∘ (agree_eq (IH_agree α2 α3 Hα2 Hα3) α1 (index_lt_le_subrel α1 α2 Hlt1)
       (index_lt_le_subrel α1 α3 Hlt3) ⁻¹)
  ≡ agree_eq (IH_agree α1 α3 Hα1 Hα3) α1 (reflexivity α1) (index_lt_le_subrel α1 α3 Hlt3) ⁻¹.
    Proof.
    Admitted.

    Program Definition merged_approx : approx P.
    Proof using C F HE IH IH_agree P SI.
      unshelve econstructor.
      - intros α G.
        apply (approx_X (IH α G) α (reflexivity _)).
      - intros α1 α2 H1 H2 G; simpl.
        apply ((approx_π (IH α2 H2) α1 α2 (index_lt_le_subrel _ _ G)
                  (reflexivity _) G)
                 ∘ (iso1 (agree_eq (IH_agree α1 α2 H1 H2) α1
                            (reflexivity α1) (index_lt_le_subrel α1 α2 G)))).
      - intros α1 α2 H1 H2 G; simpl.
        apply ((iso2 (agree_eq (IH_agree α1 α2 H1 H2) α1
                        (reflexivity α1) (index_lt_le_subrel α1 α2 G)))
                 ∘ (approx_δ (IH α2 H2) α1 α2 (index_lt_le_subrel _ _ G)
                      (reflexivity _) G)).
      - intros α Hα; simpl.
        apply approx_ϕ.
      - intros α Hα; simpl.
        apply approx_ψ.
      - constructor.
        + intros α β H1 H2 Hlt.
          rewrite arrow_comp_assoc.
          rewrite <-(arrow_comp_assoc (approx_δ (IH β H2) α β (index_lt_le_subrel α β Hlt) (reflexivity β) Hlt)).
          rewrite δπ; last apply IH.
          rewrite arrow_comp_id_l.
          rewrite iso12.
          reflexivity.
        + intros α β H1 H2 Hlt.
          rewrite arrow_comp_assoc.
          rewrite <-(arrow_comp_assoc (agree_eq (IH_agree α β H1 H2) α (reflexivity α) (index_lt_le_subrel α β Hlt))).
          rewrite iso21.
          rewrite arrow_comp_id_l.
          rewrite πδ; last apply IH.
          reflexivity.
        + intros α1 α2 α3 Hα1 Hα2 Hα3 Hlt1 Hlt2 Hlt3.
          rewrite <-(π_comp _ _ _ _ _ _ (approx_props (IH α3 Hα3)) α1 α2 α3
                      (index_lt_le_subrel α1 α3 Hlt3)
                      (index_lt_le_subrel α2 α3 Hlt2)
                      (reflexivity α3)
                      Hlt1
                      Hlt2
                      Hlt3).
          rewrite ->2 arrow_comp_assoc.
          f_equiv.
          rewrite (agree_π_nat (IH_agree α2 α3 Hα2 Hα3) _ _ _ _ (index_lt_le_subrel α1 α3 Hlt3) _ (index_lt_le_subrel α2 α3 Hlt2)).
          rewrite <-arrow_comp_assoc.
          rewrite <-arrow_comp_assoc.
          rewrite <-arrow_comp_assoc.
          rewrite iso21.
          rewrite arrow_comp_id_l.
          rewrite arrow_comp_assoc.
          f_equiv.
          by apply aaaaa.
        + intros α1 α2 α3 Hα1 Hα2 Hα3 Hlt1 Hlt2 Hlt3.
          rewrite <-(δ_comp _ _ _ _ _ _ (approx_props (IH α3 Hα3)) α1 α2 α3
                      (index_lt_le_subrel α1 α3 Hlt3)
                      (index_lt_le_subrel α2 α3 Hlt2)
                      (reflexivity α3)
                      Hlt1
                      Hlt2
                      Hlt3).
          rewrite <-2 arrow_comp_assoc.
          do 2 f_equiv.
          rewrite (agree_δ_nat (IH_agree α2 α3 Hα2 Hα3) _ _ _ _ (index_lt_le_subrel α1 α3 Hlt3) _ (index_lt_le_subrel α2 α3 Hlt2)).
          rewrite arrow_comp_assoc.
          rewrite arrow_comp_assoc.
          rewrite arrow_comp_assoc.
          rewrite iso21.
          rewrite arrow_comp_id_r.
          rewrite <-arrow_comp_assoc.
          do 2 f_equiv.
          by apply bbbbb.
        + intros.
          eapply ψϕ.
          apply IH.
        + intros.
          eapply ϕψ.
          apply IH.
        + intros.
          erewrite approx_eq; last apply IH.
          apply functor_iso_preserve.
          Unshelve.
          {
            apply iso_prod.
            * apply iso_op.
              eapply agree_eq; last apply IH_agree.
            * eapply agree_eq; last apply IH_agree.
          }
          {
            apply index_lt_le_subrel.
            apply index_succ_greater.
          }
    Defined.

    Lemma merged_agree γ Hγ: approx_agree (IH γ Hγ) merged_approx.
    Proof.
      unshelve econstructor.
      - intros.
    Admitted.
  End merge.

  Lemma merge_coherent_agree (P : SI → Prop) (IH1 IH2 : ∀ α, P α → approx (λ γ, γ ⪯ α))
    (H1 : ∀ α0 α1 Hα0 Hα1, approx_agree (IH1 α0 Hα0) (IH1 α1 Hα1))
    (H2 : ∀ α0 α1 Hα0 Hα1, approx_agree (IH2 α0 Hα0) (IH2 α1 Hα1)):
    (∀ α Hα, approx_agree (IH1 α Hα) (IH2 α Hα))
    → approx_agree (merged_approx P IH1 H1) (merged_approx P IH2 H2).
  Proof.
    intros IH.
    unshelve econstructor.
    - intros.
  Admitted.

  (* TODO: full_A_transfinite *)
  Definition full_approximation : approx (λ _, True).
  Proof.
    unshelve eapply (full_A_transfinite SI (@approx) (@approx_agree) _ _ _ _ (@extension) (@extension_agree)).
    - intros. unshelve eexists. all: intros; exfalso; by eapply H.
    - intros; eapply approx_agree_transitive.
      + apply H0.
      + apply H1.
      + apply H2.
      + apply H.
      + apply X.
      + apply X0.
    - intros; by apply approx_agree_symmetric.
    - intros; by apply approx_agree_reflexive.
    - intros; apply (extended_approx γ ap ext).
    - intros; eapply merged_approx. apply X.
    - apply succ_extension.
    - admit. (* limit case *)
    - intros; apply extended_approx_agree.
    - intros; simpl.
      eapply extension_coherent.
      apply X.
    - intros; simpl.
      apply merged_agree.
    - intros; simpl.
      by apply merge_coherent_agree.
    - intros; apply approx_base.
    - intros; apply succ_extension_coherent.
    - admit. (* limit case *)
  Admitted.

  Section final.
    Context (IH : @approx (λ _, True)).

    Program Definition final_diagram :
      ((OrdCat SI) op) [⇒] C :=
      {|
        FO (β : OrdCat SI) := F (approx_X IH β I, approx_X IH β I);
        functor.fmap A B := λₛ f, _;
      |}.
    Next Obligation.
      intros A B f.
      simpl.
      simpl in f.
      destruct (index_le_lt_eq_dec _ _ f) as [G | G].
      - apply (@functor.fmap ((C op) × C) C F
                 (approx_X IH A I, approx_X IH A I)
                 (approx_X IH B I, approx_X IH B I)
                 ((approx_π IH B A I I G), (approx_δ IH B A I I G))).
      - subst.
        apply ı.
    Defined.
    Next Obligation.
      intros.
      unfold final_diagram_obligation_1.
      simpl in H.
      subst.
      destruct (index_le_lt_eq_dec B A a₂) as [H | H].
      - reflexivity.
      - subst.
        unfold eq_rect_r.
        simpl.
        reflexivity.
    Qed.
    Next Obligation.
      intros; simpl.
      unfold final_diagram_obligation_1.
      destruct (index_le_lt_eq_dec A A (rc_refl (≺) A)) as [H | H].
      - exfalso.
        by eapply index_lt_irrefl.
      - subst.
        unfold eq_rect_r.
        rewrite (proof_irrel H Logic.eq_refl).
        simpl.
        reflexivity.
    Qed.
    Next Obligation.
      intros; simpl.
      unfold final_diagram_obligation_1.
      destruct (index_le_lt_eq_dec B A g) as [H1 | H1];
        destruct (index_le_lt_eq_dec C0 B f) as [H2 | H2].
      - case_match.
        + setoid_rewrite <-fmap_comp.
          f_equiv.
          simpl.
          split.
          * rewrite π_comp; first reflexivity.
            apply IH.
          * rewrite δ_comp; first reflexivity.
            apply IH.
        + subst.
          exfalso.
          eapply index_lt_irrefl.
          apply (transitivity H1 H2).
      - case_match.
        + unfold eq_rect_r.
          destruct H2.
          simpl.
          rewrite arrow_comp_id_l.
          rewrite (proof_irrel i H1).
          reflexivity.
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
      - subst.
        case_match.
        + unfold eq_rect_r.
          simpl.
          rewrite arrow_comp_id_r.
          rewrite (proof_irrel i H2).
          reflexivity.
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
      - subst.
        case_match.
        + exfalso.
          by eapply index_lt_irrefl.
        + unfold eq_rect_r.
          simpl.
          rewrite arrow_comp_id_l.
          clear H.
          assert (e = Logic.eq_refl) as ->.
          { apply proof_irrel. }
          simpl.
          reflexivity.
    Qed.

    Program Definition subfinal_diagram :
      ((OrdCat SI) op) [⇒] C :=
      {|
        FO (β : OrdCat SI) := approx_X IH β I;
        functor.fmap A B := λₛ f, _;
      |}.
    Next Obligation.
      intros A B f.
      simpl.
      simpl in f.
      destruct (index_le_lt_eq_dec _ _ f) as [G | G].
      - apply (approx_δ IH B A I I G).
      - subst.
        apply ı.
    Defined.
    Next Obligation.
      intros.
      unfold subfinal_diagram_obligation_1.
      simpl in H.
      subst.
      reflexivity.
    Qed.
    Next Obligation.
      intros; simpl.
      unfold subfinal_diagram_obligation_1.
      destruct (index_le_lt_eq_dec A A (rc_refl (≺) A)) as [H | H].
      - exfalso.
        by eapply index_lt_irrefl.
      - subst.
        unfold eq_rect_r.
        rewrite (proof_irrel H Logic.eq_refl).
        simpl.
        reflexivity.
    Qed.
    Next Obligation.
      intros; simpl.
      unfold subfinal_diagram_obligation_1.
      destruct (index_le_lt_eq_dec B A g) as [H1 | H1];
        destruct (index_le_lt_eq_dec C0 B f) as [H2 | H2].
      - case_match.
        + rewrite δ_comp; first reflexivity.
          apply IH.
        + subst.
          exfalso.
          eapply index_lt_irrefl.
          apply (transitivity H1 H2).
      - case_match.
        + unfold eq_rect_r.
          destruct H2.
          simpl.
          rewrite arrow_comp_id_l.
          rewrite (proof_irrel i H1).
          reflexivity.
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
      - subst.
        case_match.
        + unfold eq_rect_r.
          simpl.
          rewrite arrow_comp_id_r.
          rewrite (proof_irrel i H2).
          reflexivity.
        + subst.
          exfalso.
          by eapply index_lt_irrefl.
      - subst.
        case_match.
        + exfalso.
          by eapply index_lt_irrefl.
        + unfold eq_rect_r.
          simpl.
          rewrite arrow_comp_id_l.
          clear H.
          assert (e = Logic.eq_refl) as ->.
          { apply proof_irrel. }
          simpl.
          reflexivity.
    Qed.

    Let Xlim := cone_obj (terminal_obj (limit_obj (has_limits final_diagram))).
    Let Xlim_side : Δ Xlim [↣] final_diagram :=
      (cone_nat (terminal_obj (limit_obj (has_limits final_diagram)))).

    Let Xlim_equalises γ0 γ1 Hlt : functor.fmap final_diagram Hlt ∘ Xlim_side γ1 ≡ Xlim_side γ0.
    Proof.
      rewrite <-(eta_comp Xlim_side _ _ Hlt).
      simpl.
      rewrite arrow_comp_id_r.
      reflexivity.
    Qed.

    Program Definition δ_lim γ : Xlim [~>] subfinal_diagram γ :=
      approx_ψ IH γ I ∘ Xlim_side γ.

    Program Definition π_lim γ : subfinal_diagram γ [~>] Xlim := _.
    Next Obligation.
      intros; simpl.
      unfold Xlim.
    Admitted.

    Program Definition ψ_lim : F (Xlim, Xlim) [~>] Xlim.
    Proof.
    Admitted.
    Program Definition ϕ_lim : Xlim [~>] F (Xlim, Xlim).
    Proof.
    Admitted.

    Program Definition pre_solution_F : Solution.
    Proof using IH.
      unshelve econstructor.
      - apply Xlim.
      - refine {|
            iso1 := ϕ_lim;
            iso2 := ψ_lim;
          |}.
        + admit.
        + admit.
      - admit.
    Admitted.
  End final.

  Lemma final_solution : Solution.
  Proof using C F H SI.
    apply (@pre_solution_F full_approximation).
  Qed.

End Temp.

(* Section ToposOfTrees. *)
(*   Local Open Scope setoid_scope. *)
(*   Local Open Scope cat_scope. *)
(*   Local Open Scope functor_scope. *)
(*   Local Open Scope logic_scope. *)

(*   Context (SI : indexT). *)

(*   Definition tree := PSh ((OrdCat SI)). *)

(*   (* index_rec_lim_ext modulo setoid equiv *) *)
(*   Local Instance index_is_limit_irrel (l : SI) : ProofIrrel (index_is_limit l). *)
(*   Proof. *)
(*     intros H1 H2. *)
(*     unfold index_is_limit in *. *)
(*     apply proof_irrelevance. *)
(*   Qed. *)

(*   Local Program Instance index_rec_lim_ext' {P: SI → Type} (lim': ∀ (α : @limit_idx SI), (∀ β, β ≺ α → P β) → P α) *)
(*     : index_rec_lim_ext lim'. *)
(*   Next Obligation. *)
(*     intros. *)
(*     destruct α. *)
(*     simpl. *)
(*     assert (limit_index_not_zero = H1) as HEQ. *)
(*     { apply proof_irrel. } *)
(*     destruct HEQ. *)
(*     assert (limit_index_is_limit = H2) as HEQ. *)
(*     { apply proof_irrel. } *)
(*     destruct HEQ. *)
(*     reflexivity. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     intros. *)
(*     f_equal. *)
(*     extensionality x. *)
(*     extensionality Hx. *)
(*     apply H. *)
(*   Qed. *)

(*   (* Program Definition Plus (X : tree) : tree := *) *)
(*   (*   {| *) *)
(*   (*     FO A := colimit ; *) *)
(*   (*   |}. *) *)

(*   (* Program Definition Sheafify (X : tree) (α : limit_idx) *) *)
(*   (*   (H : ∀ β : SI, β ≺ α → (X β)) : Setoid := *) *)
(*   (*   {| *) *)
(*   (*     setoid_carrier := ({ t : ∀ (β : SI) (p : β ≺ α), X β | t = t }); *) *)
(*   (*     setoid_eq A B := ∀ β p, `A β p ≡ `B β p; *) *)
(*   (*   |}. *) *)
(*     (* : BoundedOrdCat [⇒] SetoidCat *) *)
(*   (*   := {| *) *)
(*   (*     FO X := H (`X) Point; *) *)
(*   (*   |}. *) *)
(*   (* Next Obligation. *) *)
(*   (*   intros; simpl. *) *)
(*   (*   unshelve econstructor. *) *)
(*   (*   - intros f. *) *)
(*   (*     simpl. *) *)

(*   (* Program Definition PartialCone : := term. *) *)
(*   (*     α : limit_idx *) *)
(*   (*           H : ∀ β : SI, β ≺ α → Setoid *) *)
(*   (*                                   Setoid *) *)

(*   (* Program Definition LaterSetoid (X : tree) (i : OrdCat SI) : SetoidCat *) *)
(*   (*   := (@ord_match SI (const Setoid) *) *)
(*   (*         ([ unit ]) *) *)
(*   (*         (λ i', X i') *) *)
(*   (*         (λ α, X (limit_index α)) i). *) *)

(*   (* Lemma ord_match_zero (P : OrdCat SI -> Type) s f l : ord_match P s f l zero = s. *) *)
(*   (* Proof. *) *)
(*   (*   unfold ord_match. *) *)
(*   (*   destruct index_is_zero as [EQ|NT]. *) *)
(*   (*   - symmetry. apply Eqdep_dec.eq_rect_eq_dec, index_eq_dec. *) *)
(*   (*   - exfalso; by eapply index_lt_irrefl. *) *)
(*   (* Qed. *) *)

(*   (* Lemma ord_match_succ (P : OrdCat SI -> Type) s f l α : ord_match P s f l (succ α) = f α. *) *)
(*   (* Proof. *) *)
(*   (*   unfold ord_match. *) *)
(*   (*   destruct index_is_zero as [EQ|NT];[|destruct index_dec_limit as [[β EQ]|Hlim]]. *) *)
(*   (*   - exfalso. by eapply index_succ_not_zero. *) *)
(*   (*   - eapply index_succ_inj in EQ as EQ'. subst α. *) *)
(*   (*     symmetry. apply Eqdep_dec.eq_rect_eq_dec, index_eq_dec. *) *)
(*   (*   - exfalso. eapply index_lt_irrefl, Hlim, index_succ_greater. *) *)
(*   (* Qed. *) *)

(*   Program Definition LaterSetoid (X : tree) (i : OrdCat SI) : SetoidCat *)
(*     := (@index_rec SI (const Setoid) *)
(*           ([ unit ]) *)
(*           (λ i' _, X i') *)
(*           (λ α _, X (limit_index α)) i). *)

(*   Definition LaterFmapZero' (X : tree) : *)
(*     ∀ n : SI, n ⪯ zero → (LaterSetoid X zero) [~>] (LaterSetoid X n). *)
(*   Proof. *)
(*     intros α G. *)
(*     assert (α = zero) as ->. *)
(*     { *)
(*       apply index_zero_is_unique. *)
(*       intros β contra. *)
(*       apply (index_lt_zero_is_normal β (index_lt_le_trans _ _ _ contra G)). *)
(*     } *)
(*     apply idS. *)
(*   Defined. *)

(*   Program Definition LaterFmapZero (X : tree) : *)
(*     ∀ n : OrdCat SI, (n [~>] zero) [→] (LaterSetoid X zero) [~>] (LaterSetoid X n) *)
(*   := λ α, λₛ H, LaterFmapZero' X α H. *)
(*   Next Obligation. *)
(*     intros ???? ->. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Definition LaterFmapSucc' (X : tree) α *)
(*     (prev : (∀ n : OrdCat SI, n [~>] α *)
(*                               → (LaterSetoid X α) [~>] (LaterSetoid X n))) *)
(*     : *)
(*     ∀ n : OrdCat SI, (n [~>] succ α) *)
(*                      → (LaterSetoid X (succ α)) [~>] (LaterSetoid X n). *)
(*   Proof. *)
(*     intros β P; simpl. *)
(*     unfold LaterSetoid at 1. *)
(*     erewrite index_rec_succ; [| apply _]. *)
(*     apply index_le_lt_eq_dec in P. *)
(*     destruct P as [H | HEQ]. *)
(*     - unshelve eapply (index_rec (λ β, β ≺ succ α → (X α) [→] (LaterSetoid X β)) _ _ _ β H). *)
(*       + intros G. *)
(*         simpl. *)
(*         unfold LaterSetoid at 1. *)
(*         erewrite index_rec_zero; [| apply _]. *)
(*         apply constS, tt. *)
(*       + simpl. *)
(*         intros γ f. *)
(*         unfold LaterSetoid at 1. *)
(*         erewrite index_rec_succ; [| apply _]. *)
(*         intros G. *)
(*         apply (functor.fmap X (index_lt_le_subrel _ _ (index_lt_succ_inj _ _ G))). *)
(*       + intros γ f G; simpl. *)
(*         simpl in f. *)
(*         unfold LaterSetoid at 1. *)
(*         erewrite index_rec_lim; [| apply _]. *)
(*         apply (functor.fmap X (index_succ_iff_proj_r2l _ _ _ G)). *)
(*     - rewrite HEQ. *)
(*       unfold LaterSetoid at 1. *)
(*       erewrite index_rec_succ; [| apply _]. *)
(*       apply idS. *)
(*   Defined. *)

(*   Program Definition LaterFmapSucc (X : tree) α *)
(*     (prev : ∀ n : OrdCat SI, (n [~>] α) [→] (LaterSetoid X α) [~>] (LaterSetoid X n)) *)
(*     : *)
(*     ∀ n : OrdCat SI, (n [~>] succ α) [→] (LaterSetoid X (succ α)) *)
(*                        [~>] (LaterSetoid X n) *)
(*   := λ n, λₛ H, LaterFmapSucc' X α prev n H. *)
(*   Next Obligation. *)
(*     intros ?????? ->. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Definition LaterFmapLim' (X : tree) (α : limit_idx) *)
(*     (prev : (∀ β : OrdCat SI, *)
(*                β ≺ α *)
(*                → ∀ n : OrdCat SI, *)
(*                (n [~>] β) *)
(*                  [→] (LaterSetoid X β [~>] LaterSetoid X n))) *)
(*     : *)
(*     ∀ n : OrdCat SI, *)
(*     (n [~>] limit_index α) → (LaterSetoid X (limit_index α) [~>] LaterSetoid X n). *)
(*   Proof. *)
(*     intros n H. *)
(*     unfold LaterSetoid at 1. *)
(*     erewrite index_rec_lim; [| apply _]. *)
(*     apply index_le_lt_eq_dec in H. *)
(*     destruct H as [H | HEQ]. *)
(*     - unshelve eapply (index_rec (λ β, β ≺ α → (X (limit_index α)) [→] (LaterSetoid X β)) _ _ _ n H). *)
(*       + intros G. *)
(*         simpl. *)
(*         unfold LaterSetoid at 1. *)
(*         erewrite index_rec_zero; [| apply _]. *)
(*         apply constS, tt. *)
(*       + simpl. *)
(*         intros γ f. *)
(*         unfold LaterSetoid at 1. *)
(*         erewrite index_rec_succ; [| apply _]. *)
(*         intros G. *)
(*         apply (functor.fmap X (index_succ_le _ _ (index_lt_le_subrel _ _ G))). *)
(*       + intros γ f G; simpl. *)
(*         simpl in f. *)
(*         unfold LaterSetoid at 1. *)
(*         erewrite index_rec_lim; [| apply _]. *)
(*         apply (functor.fmap X (index_lt_le_subrel _ _ G)). *)
(*     - rewrite HEQ. *)
(*       unfold LaterSetoid at 1. *)
(*       erewrite index_rec_lim; [| apply _]. *)
(*       apply idS. *)
(*   Defined. *)

(*   Program Definition LaterFmapLim (X : tree) (α : limit_idx) *)
(*     (prev : (∀ β : OrdCat SI, *)
(*        β ≺ α *)
(*        → ∀ n : OrdCat SI, *)
(*                (n [~>] β) *)
(*                  [→] (LaterSetoid X β [~>] LaterSetoid X n))) *)
(*     : *)
(*     ∀ n : OrdCat SI, *)
(*     (n [~>] limit_index α) [→] (LaterSetoid X (limit_index α) [~>] LaterSetoid X n) *)
(*   := λ n, λₛ H, LaterFmapLim' X α prev n H. *)
(*   Next Obligation. *)
(*     intros ?????? ->. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Definition LaterFmap (X : tree) (n m : OrdCat SI) : *)
(*     (n [~>] m) [→] LaterSetoid X m [~>] LaterSetoid X n. *)
(*   Proof. *)
(*     (* unshelve epose proof (projT2 (@index_cumulative_rec SI (λ _, True) (λ α H, ∀ β, α ≺ β → LaterSetoid X α [~>] LaterSetoid X β) _ _ n) m). *) *)
(*     (* - simpl. *) *)
(*     (*   done. *) *)
(*     (* - simpl. *) *)
(*     (*   intros. *) *)
(*     (*   epose proof (projT2 (G zero _) β _). *) *)
(*     (*   simpl in X0. *) *)

(*     apply (@index_rec SI *)
(*              (λ m, ∀ n : OrdCat SI, (n [~>] m) *)
(*                                       [→] (LaterSetoid X m) *)
(*                                       [→] (LaterSetoid X n)) *)
(*              (LaterFmapZero X) *)
(*              (LaterFmapSucc X) *)
(*              (LaterFmapLim X) *)
(*              m n). *)
(*   Defined. *)

(*   Lemma LaterFmapId (X : tree) (n : OrdCat SI) *)
(*     : LaterFmap X n n ı ≡ ı. *)
(*   Proof. *)
(*     destruct (index_type_dec n) as [[-> | H] | H]. *)
(*     - unfold LaterFmap. *)
(*       erewrite index_rec_zero; [| apply index_rec_lim_ext']. *)
(*       intros ?; simpl in *. *)
(*       unfold LaterFmapZero'; simpl. *)
(*       elim_eq_irrel. *)
(*       simpl. *)
(*       reflexivity. *)
(*     - destruct H as [? ->]. *)
(*       unfold LaterFmap. *)
(*       erewrite index_rec_succ; [| apply index_rec_lim_ext']. *)
(*       intros ?; simpl in *. *)
(*       unfold LaterSetoid in a. *)
(*       simpl in a. *)
(*       unfold LaterFmapSucc'; simpl. *)
(*       destruct (index_le_lt_eq_dec (succ x) (succ x) _). *)
(*       + exfalso. *)
(*         eapply index_lt_irrefl. *)
(*         apply i. *)
(*       + rewrite (proof_irrel e Logic.eq_refl); clear e. *)
(*         cbn. *)
(*   Admitted. *)

(*   Program Definition LaterObj (X : tree) : tree := *)
(*     {| *)
(*       FO A := LaterSetoid X A; *)
(*       functor.fmap A B := LaterFmap X B A; *)
(*     |}. *)
(*   Next Obligation. *)
(*   Admitted. *)
(*   Next Obligation. *)
(*   Admitted. *)

(*   Program Definition Later : tree [⇒] tree := *)
(*     {| *)
(*       FO A := LaterObj A; *)
(*       functor.fmap A B := _; *)
(*     |}. *)
(*   Next Obligation. *)
(*   Admitted. *)
(*   Next Obligation. *)
(*   Admitted. *)
(*   Next Obligation. *)
(*   Admitted. *)

(*   Notation "'▶'" := (Later) (at level 0) : logic_scope. *)

(*   Program Definition NextFun (X : tree) : ∀ (i : OrdCat SI), (X i) [→] ▶ X i *)
(*   := λ i, λₛ T, (functor.fmap (▶ X) (step_arrow_nat _) _). *)
(*   Next Obligation. *)
(*     intros X i T; simpl. *)
(*     unfold LaterSetoid. *)
(*     rewrite index_rec_succ. *)
(*     apply T. *)
(*   Defined. *)
(*   Next Obligation. *)
(*     intros; simpl. *)
(*     f_equiv. *)
(*   Admitted. *)

(*   Program Definition next {X : tree} : X [↣] (▶ X) *)
(*     := λₙ n, NextFun X n. *)
(*   Next Obligation. *)
(*   Admitted. *)

(*   Definition Contractive (X Y : tree) (ϕ : X [↣] Y) := *)
(*     sigT (λ g : ▶ X [↣] Y, ϕ ≡ g ∘ next). *)

(*   Local Opaque has_limits. *)
(*   Local Opaque has_terminal. *)

(*   (* sheaf condition here *) *)
(*   Program Definition FixPointwise (X : tree) *)
(*     (ϕ : X [↣] X) *)
(*     (g : ▶ X [↣] X) *)
(*     (H : ϕ ≡ g ∘ next) *)
(*     (i : OrdCat SI) : (𝟙 @ tree)%cat i [~>] X i. *)
(*   Proof. *)
(*     unshelve eapply (index_rec (λ i, (𝟙 @ tree) i [~>] X i) _ _ _ i); simpl. *)
(*     - unshelve econstructor. *)
(*       + intros ?. *)
(*         pose proof (g zero) as T. *)
(*         simpl in T. *)
(*         unfold LaterSetoid in T. *)
(*         rewrite index_rec_zero in T. *)
(*         apply (T tt). *)
(*       + intros; simpl. *)
(*         admit. *)
(*     - intros α Xα. *)
(*       unshelve econstructor. *)
(*       + intros ?. *)
(*         apply (g (succ α)). *)
(*         simpl. *)
(*         unfold LaterSetoid. *)
(*         rewrite index_rec_succ. *)
(*         apply Xα. *)
(*         apply Point. *)
(*       + intros; simpl. *)
(*         admit. *)
(*     - intros α G. *)
(*       unshelve econstructor. *)
(*       + intros ?. *)
(*         (* ω op -> Set *) *)
(*         (* Sh(ω + 1, Grothendick site) *) *)
(*         (* i.e. *) *)
(*         (* i can find amalgamation of (toSh (F : ω op -> Set)) *) *)
(*         (* β < α is a cover of α *) *)
(*         (* G is a matching family *) *)
(*         (* strenghthen induction hypothesis *) *)
(*         pose proof (g (limit_index α)). *)
(*         (* apply (g (limit_index α)). *) *)
(*         (* simpl. *) *)
(*         (* unfold LaterSetoid. *) *)
(*       (* rewrite index_rec_lim.         *) *)
(*         admit. *)
(*       + admit. *)
(*   Admitted. *)

(*   Program Definition FixPointwise' (X : tree) *)
(*     (ϕ : X [↣] X) *)
(*     (g : ▶ X [↣] X) *)
(*     (H : ϕ ≡ g ∘ next) *)
(*     : {f : ∀ i, (𝟙 @ tree)%cat i [~>] X i & *)
(*                   ((∀ i j (p : i [~>] j), functor.fmap X p (f i Point) ≡ f j Point) ∧ (∀ i, ϕ i ∘ f i ≡ f i))}. *)
(*   Proof. *)
(*   Admitted. *)

(* End ToposOfTrees. *)
