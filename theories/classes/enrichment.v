From category Require Import
  base
  setoid
  category
  sets
  terminal
  functor
  limit
  prod
  classes.limits
  classes.exp
  exp.

Section Enrichment.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Class SelfEnrichment (C : Category)
    `{!hasBinaryProducts C}
    `{!hasExp C}
    `{!hasTerminal C}
    :=
    {
      HOM_ID {A : C} : 𝟙 @ C [~>] (A ⇒ A @ C);
      HOM_COMP {A B D : C} : (B ⇒ D @ C) ×ₒ (A ⇒ B @ C) @ C [~>] (A ⇒ D @ C);
      HOM_ID_L {A B : C} {f : 𝟙 @ C [~>] (A ⇒ B @ C)} : (HOM_COMP ∘ ⟨HOM_ID , f⟩) ≡ f;
      HOM_ID_R {A B : C} {f : 𝟙 @ C [~>] (A ⇒ B @ C)} : (HOM_COMP ∘ ⟨f, HOM_ID⟩) ≡ f;
      HOM_ASSOC {A B D E : C} {f : 𝟙 @ C [~>] (A ⇒ B @ C)} {g : 𝟙 @ C [~>] (B ⇒ D @ C)} {h : 𝟙 @ C [~>] (D ⇒ E @ C)}
      : HOM_COMP ∘ (⟨ HOM_COMP ∘ (⟨ h, g ⟩), f ⟩) ≡ HOM_COMP ∘ (⟨ h, HOM_COMP ∘ (⟨ g, f ⟩) ⟩);
      quote {A B : C} (f : A [~>] B) : 𝟙 @ C [~>] (A ⇒ B @ C);
      unquote {A B : C} (f : 𝟙 @ C [~>] (A ⇒ B @ C)) : (A [~>] B);
      unquote_quote {A B : C} (f : 𝟙 @ C [~>] (A ⇒ B @ C)) : quote (unquote f) ≡ f;
      quote_unquote {A B : C} (f : A [~>] B) : unquote (quote f) ≡ f;
    }.

  Arguments HOM_ID {_ _ _ _ _}.
  Arguments HOM_COMP {_ _ _ _ _ _ _ _}.
  Arguments HOM_ID_L {_ _ _ _ _ _ _}.
  Arguments HOM_ID_R {_ _ _ _ _ _ _}.
  Arguments HOM_ASSOC {_ _ _ _ _ _ _ _ _}.

  Local Opaque ArrBinUnrec.

  Program Definition EnrichmentCat (C : Category) `{SelfEnrichment C} : Category :=
    {|
      Obj := C;
      Arr A B := 𝟙 @ C [~>] (A ⇒ B @ C);
      arrow_id A := (HOM_ID A);
      arrow_comp A B D := λₛ f, λₛ g, (HOM_COMP ∘ ⟨f, g⟩);
    |}.
  Next Obligation.
    intros; simpl.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now do 3 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    simpl in f.
    apply HOM_ID_L.
  Qed.
  Next Obligation.
    intros; simpl.
    simpl in f.
    apply HOM_ID_R.
  Qed.
  Next Obligation.
    intros; simpl.
    simpl in *.
    apply HOM_ASSOC.
  Qed.
End Enrichment.

Arguments HOM_ID {_ _ _ _ _}.
Arguments HOM_COMP {_ _ _ _ _ _ _ _}.
Arguments HOM_ID_L {_ _ _ _ _ _ _}.
Arguments HOM_ID_R {_ _ _ _ _ _ _}.
Arguments HOM_ASSOC {_ _ _ _ _ _ _ _ _}.
