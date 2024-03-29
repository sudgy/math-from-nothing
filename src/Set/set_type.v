Require Import init.

Require Import set_base.

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

Theorem set_value_simpl : ∀ {U} {S : U → Prop} x (P : S x), [[x|P]|] = x.
Proof.
    reflexivity.
Qed.

Theorem set_proof_simpl : ∀ {U} {S : U → Prop} x (P : S x), [|[x|P]] = P.
Proof.
    reflexivity.
Qed.

Theorem set_type_simpl : ∀ {U} {S : U → Prop} (x : set_type S) (H : S [x|]),
    [[x|] | H] = x.
Proof.
    intros U S x H.
    destruct x as [x Sx].
    cbn.
    rewrite (proof_irrelevance Sx H).
    reflexivity.
Qed.

Theorem set_type_eq {U} {S : U → Prop} : ∀ {a b : set_type S},
    [a|] = [b|] ↔ a = b.
Proof.
    intros a b.
    split; intros eq.
    -   destruct a as [a a_in], b as [b b_in].
        do 2 rewrite set_value_simpl in eq.
        subst b.
        apply f_equal.
        apply proof_irrelevance.
    -   rewrite eq.
        reflexivity.
Qed.

Theorem set_type_eq2 {U} {S : U → Prop} : ∀ {a b : U} {H1 : S a} {H2 : S b}, [a|H1] = [b|H2] ↔ a = b.
Proof.
    intros a b H1 H2.
    rewrite <- set_type_eq.
    reflexivity.
Qed.

Theorem set_type_refl {U} {S : U → Prop} : ∀ a (H1 H2 : S a), [a|H1] = [a|H2].
Proof.
    intros a H1 H2.
    rewrite set_type_eq2.
    reflexivity.
Qed.

Theorem ex_set_type {U} {S : U → Prop} : (∃ x, S x) → set_type S.
Proof.
    intros x_ex.
    apply indefinite_description.
    destruct x_ex as [x Sx].
    split.
    exact [x|Sx].
Qed.

Theorem set_type_rewrite_eq {U} {S : U → Prop} : ∀ {a b} {H : S a}, a = b → S b.
Proof.
    intros a b H eq.
    subst.
    exact H.
Qed.

Theorem set_type_inj {U} {S : U → Prop} : Injective (@set_value _ S).
Proof.
    split.
    intros a b eq.
    rewrite set_type_eq in eq.
    exact eq.
Qed.

Theorem singleton_set_type : ∀ {U} {S : U → Prop},
    (∃ a, S a ∧ ∀ b, S b → b = a) → Singleton (set_type S).
Proof.
    intros U S [a [Sa eq]].
    split.
    exists [a|Sa].
    intros [b Sb].
    rewrite set_type_eq2.
    apply eq.
    exact Sb.
Qed.

Theorem set_type_singleton : ∀ {U} {S : U → Prop},
    Singleton (set_type S) → ∀ a b, S a → S b → a = b.
Proof.
    intros U S S_single a b Sa Sb.
    pose proof (singleton_unique2 [a|Sa] [b|Sb]) as eq.
    rewrite set_type_eq2 in eq.
    exact eq.
Qed.

Tactic Notation "st_proof_simpl" constr(a) simple_intropattern(H) :=
    let go H1 H2 :=
        pose proof (H1 H2) as H;
        rewrite (proof_irrelevance (H1 H2) H) in *
    in
    match goal with
    | |- context [[a|?H1 ?H2]] => go H1 H2
    | K: context [[a|?H1 ?H2]] |- _ => go H1 H2
    end.

Tactic Notation "st_proof_simpl" constr(a) :=
    let H := fresh in st_proof_simpl a H.

Tactic Notation "st_proof_simpl_anon" simple_intropattern(H) :=
    let go H1 H2 :=
        pose proof (H1 H2) as H;
        rewrite (proof_irrelevance (H1 H2) H) in *
    in
    match goal with
    | |- context [[?a|?H1 ?H2]] => go H1 H2
    | K: context [[?a|?H1 ?H2]] |- _ => go H1 H2
    end.

Tactic Notation "st_proof_simpl" := let H := fresh in st_proof_simpl_anon H.

Theorem set_type_rewrite {U} {S : U → Prop} : ∀ a b (H : S a) (eq : a = b),
    [a|H] = [b|set_type_rewrite_eq (H := H) eq].
Proof.
    intros a b H eq.
    subst.
    apply set_type_refl.
Qed.

(** This converts a set S : U → Prop to a set S : set_type X → Prop *)
Definition to_set_type {U} (X : U → Prop) (S : U → Prop) :=
    λ x : set_type X, S [x|].
(** This converts a set S : set_type X → Prop to a set S : U → Prop *)
Definition from_set_type {U} {X : U → Prop} (S : set_type X → Prop) :=
    λ x, X x ⋏ λ H, S [x|H].

Theorem to_set_type_in {U} : ∀ (X A : U → Prop) (sub : A ⊆ X),
    ∀ x (Ax : A x), to_set_type X A [x|sub x Ax].
Proof.
    intros X A sub x Ax.
    exact Ax.
Qed.

Theorem from_set_type_in {U} {X : U → Prop} : ∀ (A : set_type X → Prop),
    ∀ x, A x → from_set_type A [x|].
Proof.
    intros A x Ax.
    unfold from_set_type.
    split with [|x].
    rewrite set_type_simpl.
    exact Ax.
Qed.

Theorem to_from_set_type {U} (X : U → Prop) : ∀ A : set_type X → Prop,
    to_set_type X (from_set_type A) = A.
Proof.
    intros A.
    apply antisym.
    -   intros x [Xx' Ax].
        applys_eq Ax.
        symmetry; apply set_type_simpl.
    -   intros x Ax.
        apply from_set_type_in.
        exact Ax.
Qed.

Theorem from_to_set_type {U} : ∀ X A : U → Prop, A ⊆ X →
    from_set_type (to_set_type X A) = A.
Proof.
    intros X A sub.
    apply antisym.
    -   intros x [Xx Ax].
        exact Ax.
    -   intros x Ax.
        split with (sub x Ax).
        exact Ax.
Qed.

Theorem to_set_type_inter {U} : ∀ (X A : U → Prop),
    to_set_type X A = to_set_type X (A ∩ X).
Proof.
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
Proof.
    intros X A B sub x Ax.
    apply sub.
    exact Ax.
Qed.

Theorem to_from_set_type_sub {U} : ∀ (X A : U → Prop) (B : set_type X → Prop),
    A ⊆ X → to_set_type X A ⊆ B → A ⊆ from_set_type B.
Proof.
    intros X A B sub sub2 x Ax.
    split with (sub x Ax).
    apply sub2.
    exact Ax.
Qed.

Theorem from_set_type_sub_X {U} : ∀ (X : U → Prop) (A : set_type X → Prop),
    from_set_type A ⊆ X.
Proof.
    intros X A x [Xx Ax].
    exact Xx.
Qed.

Theorem from_set_type_union {U} : ∀ (X : U → Prop) (A B : set_type X → Prop),
    A ∪ B = all → from_set_type A ∪ from_set_type B = X.
Proof.
    intros X A B eq.
    apply antisym.
    -   intros x [Xx|Xx]; apply Xx.
    -   intros x Xx.
        assert (all [x|Xx]) as x_in by exact true.
        rewrite <- eq in x_in.
        destruct x_in as [Ax|Bx].
        +   left.
            split with Xx.
            exact Ax.
        +   right.
            split with Xx.
            exact Bx.
Qed.
(* begin hide *)
Section SetTypeOrder.

Context {U} {S : U → Prop}.
Context `{WellOrder U}.

Global Instance set_type_order : Order (set_type S) := {
    le a b := [a|] ≤ [b|]
}.

Global Instance set_type_le_connex_class : Connex le.
Proof.
    split.
    intros a b.
    unfold le; cbn.
    apply connex.
Qed.

Global Instance set_type_le_antisym_class : Antisymmetric le.
Proof.
    split.
    intros a b ab ba.
    apply set_type_eq.
    apply antisym; assumption.
Qed.

Global Instance set_type_le_trans_class : Transitive le.
Proof.
    split.
    intros a b c.
    unfold le; cbn.
    apply trans.
Qed.

Global Instance set_type_le_refl_class : Reflexive le.
Proof.
    split.
    intros a.
    unfold le; cbn.
    apply refl.
Qed.

Global Instance set_type_le_wo_class : WellOrdered le.
Proof.
    split.
    intros T T_ex.
    assert (∃ x, from_set_type T x) as T'_nempty.
    {
        destruct T_ex as [[x Sx] Tx].
        exists x.
        apply (from_set_type_in _ _ Tx).
    }
    pose proof (well_ordered _ T'_nempty) as [x [[Sx Tx] x_min]].
    exists [x|Sx].
    split; [>exact Tx|].
    intros y Ty.
    apply x_min.
    split with [|y].
    rewrite set_type_simpl.
    exact Ty.
Qed.

Theorem set_type_lt : ∀ a b, [a|] < [b|] ↔ a < b.
Proof.
    intros a b.
    unfold strict.
    unfold le at 2; cbn.
    rewrite set_type_eq.
    reflexivity.
Qed.

End SetTypeOrder.
(* end hide *)
