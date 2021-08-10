Require Import init.

Require Import set_base.
Require Import relation.
Require Import order_def.
Require Import nat.

#[universes(template)]
Record set_type {U} (S : U → Prop) := make_set_type_val {
    set_value : U;
    set_proof : S set_value;
}.
Arguments make_set_type_val {U} {S}.
Arguments set_value {U} {S}.
Arguments set_proof {U} {S}.

Notation "[ x | P ]" := (make_set_type_val x P).
Notation "[ a | ]" := (set_value a).
Notation "[ | a ]" := (set_proof a).

Theorem set_type_eq {U} {S : U → Prop} : ∀ (a b : set_type S),
        [a|] = [b|] → a = b.
    intros a b eq.
    destruct a as [a a_in], b as [b b_in].
    cbn in *.
    subst.
    rewrite (proof_irrelevance a_in b_in).
    reflexivity.
Qed.

Theorem eq_set_type {U} {S : U → Prop} : ∀ (a b : set_type S),
        a = b → [a|] = [b|].
    intros a b eq.
    subst.
    reflexivity.
Qed.

Theorem set_type_simpl {U} {S : U → Prop} : ∀ a (P : S a), [[a|P]|] = a.
    intros a P.
    reflexivity.
Qed.

Definition to_set_type {U} (X : U → Prop) (S : U → Prop) :=
    λ x : set_type X, S [x|].
Definition from_set_type {U} {X : U → Prop} (S : set_type X → Prop) :=
    λ x, ∃ x', x = [x'|] ∧ S x'.

Theorem to_set_type_in {U} : ∀ (X A : U → Prop) (sub : A ⊆ X),
        ∀ x (Ax : A x), to_set_type X A [x|sub x Ax].
    intros X A sub x Ax.
    exact Ax.
Qed.

Theorem from_set_type_in {U} {X : U → Prop} : ∀ (A : set_type X → Prop),
        ∀ x, A x → from_set_type A [x|].
    intros A x Ax.
    exists x.
    split; trivial.
Qed.

Theorem to_from_set_type {U} (X : U → Prop) : ∀ A : set_type X → Prop,
        to_set_type X (from_set_type A) = A.
    intros A.
    apply antisym.
    -   intros x [x' [eq Ax']].
        apply set_type_eq in eq.
        rewrite eq.
        exact Ax'.
    -   intros x Ax.
        exists x.
        split; trivial.
Qed.

Theorem from_to_set_type {U} : ∀ X A : U → Prop, A ⊆ X →
        from_set_type (to_set_type X A) = A.
    intros X A sub.
    apply antisym.
    -   intros x [x' [eq x_in]].
        rewrite eq.
        exact x_in.
    -   intros x Ax.
        exists [x|sub x Ax].
        split; trivial.
Qed.

Theorem to_set_type_inter {U} : ∀ (X A : U → Prop),
        to_set_type X A = to_set_type X (A ∩ X).
    intros X A.
    apply antisym.
    -   intros x Ax.
        split.
        +   exact Ax.
        +   exact [|x].
    -   intros x [Ax Xx].
        exact Ax.
Qed.

Theorem to_set_type_sub {U} : ∀ (X A B : U → Prop),
        A ⊆ B → to_set_type X A ⊆ to_set_type X B.
    intros X A B sub x Ax.
    apply sub.
    exact Ax.
Qed.

Theorem to_from_set_type_sub {U} : ∀ (X A : U → Prop) (B : set_type X → Prop),
        A ⊆ X → to_set_type X A ⊆ B → A ⊆ from_set_type B.
    intros X A B sub sub2 x Ax.
    exists [x|sub x Ax].
    split.
    -   reflexivity.
    -   apply sub2.
        exact Ax.
Qed.

Theorem from_set_type_sub_X {U} : ∀ (X : U → Prop) (A : set_type X → Prop),
        from_set_type A ⊆ X.
    intros X A x [[x' Xx'] [x_eq Ax]].
    rewrite x_eq.
    exact Xx'.
Qed.

Theorem from_set_type_union {U} : ∀ (X : U → Prop) (A B : set_type X → Prop),
        A ∪ B = all → from_set_type A ∪ from_set_type B = X.
    intros X A B eq.
    apply antisym.
    -   intros x [Cx|Dx].
        +   destruct Cx as [x' [x'_eq Cx']]; subst.
            apply x'.
        +   destruct Dx as [x' [x'_eq Dx']]; subst.
            apply x'.
    -   intros x Bx.
        assert (all [x|Bx]) as x_in by exact true.
        rewrite <- eq in x_in.
        destruct x_in as [Cx|Dx].
        +   left.
            exists [x|Bx].
            split; trivial.
        +   right.
            exists [x|Bx].
            split; trivial.
Qed.
(* begin hide *)
Section SetTypeOrder.

Context {U} {S : U → Prop}.
Context `{
    Order U,
    Connex U le,
    Antisymmetric U le,
    Transitive U le,
    Reflexive U le,
    WellFounded U le,
    SupremumComplete U le
}.

Global Instance set_type_order : Order (set_type S) := {
    le a b := [a|] <= [b|]
}.

Lemma set_type_le_connex : ∀ a b : set_type S, {a <= b} + {b <= a}.
    intros a b.
    unfold le; cbn.
    apply connex.
Qed.
Global Instance set_type_le_connex_class : Connex le := {
    connex := set_type_le_connex
}.

Lemma set_type_le_antisym : ∀ a b : set_type S, a <= b → b <= a → a = b.
    intros a b ab ba.
    apply set_type_eq.
    apply antisym; assumption.
Qed.
Global Instance set_type_le_antisym_class : Antisymmetric le := {
    antisym := set_type_le_antisym
}.

Lemma set_type_le_trans : ∀ a b c : set_type S, a <= b → b <= c → a <= c.
    intros a b c.
    unfold le; cbn.
    apply trans.
Qed.
Global Instance set_type_le_trans_class : Transitive le := {
    trans := set_type_le_trans
}.

Lemma set_type_le_refl : ∀ a : set_type S, a <= a.
    intros a.
    unfold le; cbn.
    apply refl.
Qed.
Global Instance set_type_le_refl_class : Reflexive le := {
    refl := set_type_le_refl
}.

Lemma set_type_le_wf : ∀ S' : set_type S → Prop, (∃x, S' x) → has_minimal le S'.
    intros S' [[x Sx] S'x].
    pose (S'' x := ∃ y, [y|] = x ∧ S' y).
    assert (∃ x, S'' x) as S''_nempty.
    {
        exists x.
        exists [x|Sx].
        split; auto.
    }
    pose proof (well_founded _ S''_nempty) as [y [[x' [x'_eq S'x']] y_min]].
    exists x'.
    split; try assumption.
    intros y' S'y' y'_eq y'_leq.
    apply (y_min [y'|]).
    -   exists y'.
        split; try assumption.
        reflexivity.
    -   intro contr.
        subst y.
        apply set_type_eq in contr.
        contradiction.
    -   subst y.
        unfold le in y'_leq; cbn in y'_leq.
        exact y'_leq.
Qed.
Global Instance set_type_le_wf_class : WellFounded le := {
    well_founded := set_type_le_wf
}.

End SetTypeOrder.
(* end hide *)
