Require Import init.

Require Export list_base.
Require Import list_in.

Require Import set.

Fixpoint list_filter {U} (S : U → Prop) (l : list U) :=
    match l with
    | [] => []
    | x ꞉ l' => If S x then x ꞉ list_filter S l' else list_filter S l'
    end.
Arguments list_filter : simpl never.

Fixpoint list_prop {U} (S : U → Prop) (l : list U) :=
    match l with
    | [] => True
    | a ꞉ l' => S a ∧ list_prop S l'
    end.
Arguments list_prop : simpl never.

(** Note that this only checks all pairs from left to right and doesn't evaluate
S on an element with itself.  If you want both directions, give an S that
manually checks both directions, and if you want to check an element with
itself, use list_prop. *)
Fixpoint list_prop2 {U} (S : U → U → Prop) (l : list U) :=
    match l with
    | [] => True
    | a ꞉ l' => list_prop (S a) l' ∧ list_prop2 S l'
    end.
Arguments list_prop2 : simpl never.

Theorem list_filter_end {U} : ∀ (S : U → Prop), list_filter S [] = [].
Proof.
    reflexivity.
Qed.

Theorem list_filter_add_in {U} : ∀ {S : U → Prop} {a l},
    S a → list_filter S (a ꞉ l) = a ꞉ list_filter S l.
Proof.
    intros S a l Sa.
    unfold list_filter; fold (list_filter (U := U)).
    rewrite (if_true Sa).
    reflexivity.
Qed.

Theorem list_filter_add_nin {U} : ∀ {S : U → Prop} {a l},
    ¬S a → list_filter S (a ꞉ l) = list_filter S l.
Proof.
    intros S a l Sa.
    unfold list_filter; fold (list_filter (U := U)).
    rewrite (if_false Sa).
    reflexivity.
Qed.

Theorem list_filter_single_in {U} : ∀ (S : U → Prop) a,
    S a → list_filter S [a] = [a].
Proof.
    intros S a Sa.
    rewrite (list_filter_add_in Sa).
    rewrite list_filter_end.
    reflexivity.
Qed.

Theorem list_filter_single_nin {U} : ∀ (S : U → Prop) a,
    ¬S a → list_filter S [a] = [].
Proof.
    intros S a Sa.
    rewrite (list_filter_add_nin Sa).
    rewrite list_filter_end.
    reflexivity.
Qed.

Theorem list_filter_conc {U} : ∀ (S : U → Prop) l1 l2,
    list_filter S (l1 + l2) = list_filter S l1 + list_filter S l2.
Proof.
    intros S l1 l2.
    induction l1 as [|a l1].
    -   rewrite list_filter_end.
        do 2 rewrite list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        classic_case (S a) as [Sa|Sa].
        +   do 2 rewrite (list_filter_add_in Sa).
            rewrite IHl1.
            rewrite list_conc_add.
            reflexivity.
        +   do 2 rewrite (list_filter_add_nin Sa).
            exact IHl1.
Qed.

Lemma list_filter_in_both {U} : ∀ S (l : list U) x,
    in_list (list_filter S l) x → in_list l x ∧ S x.
Proof.
    intros S l x x_in.
    induction l.
    -   rewrite list_filter_end in x_in.
        contradiction x_in.
    -   rewrite in_list_add_eq.
        classic_case (S a) as [Sa|Sa].
        +   rewrite (list_filter_add_in Sa) in x_in.
            rewrite in_list_add_eq in x_in.
            destruct x_in as [x_eq|x_in].
            *   subst a.
                split; [>|exact Sa].
                left; reflexivity.
            *   specialize (IHl x_in).
                split; [>|apply IHl].
                right; apply IHl.
        +   rewrite (list_filter_add_nin Sa) in x_in.
            specialize (IHl x_in).
            split; [>|apply IHl].
            right; apply IHl.
Qed.

Theorem list_filter_in {U} : ∀ S (l : list U) x,
    in_list (list_filter S l) x → in_list l x.
Proof.
    intros S l x x_in.
    apply (list_filter_in_both S l x x_in).
Qed.

Theorem list_filter_in_set {U} : ∀ S (l : list U) x,
    in_list (list_filter S l) x → S x.
Proof.
    intros S l x x_in.
    apply (list_filter_in_both S l x x_in).
Qed.

Theorem list_filter_unique {U} : ∀ S (l : list U),
    list_unique l → list_unique (list_filter S l).
Proof.
    intros S l l_uni.
    list_unique_induction l l_uni as a a_nin IHl.
    -   rewrite list_filter_end.
        apply list_unique_end.
    -   classic_case (S a) as [Sa|Sa].
        +   rewrite (list_filter_add_in Sa).
            rewrite list_unique_add.
            split.
            *   contrapositive a_nin.
                apply list_filter_in.
            *   exact IHl.
        +   rewrite (list_filter_add_nin Sa).
            exact IHl.
Qed.

Theorem list_filter_image_in {U V} : ∀ S (f : U → V) (l : list U) x,
    in_list (list_image f (list_filter S l)) x → in_list (list_image f l) x.
Proof.
    intros S f l y y_in.
    apply image_in_list in y_in as [x [x_eq x_in]].
    subst y.
    apply in_list_image.
    exact (list_filter_in _ _ _ x_in).
Qed.

Theorem list_filter_image_unique {U V} : ∀ S (f : U → V) (l : list U),
    list_unique (list_image f l) →
    list_unique (list_image f (list_filter S l)).
Proof.
    intros S f l l_uni.
    induction l as [|a l].
    -   rewrite list_filter_end, list_image_end.
        apply list_unique_end.
    -   rewrite list_image_add, list_unique_add in l_uni.
        destruct l_uni as [fa_nin l_uni].
        specialize (IHl l_uni).
        classic_case (S a) as [Sa|Sa].
        +   rewrite (list_filter_add_in Sa).
            rewrite list_image_add, list_unique_add.
            split.
            *   contrapositive fa_nin.
                apply list_filter_image_in.
            *   exact IHl.
        +   rewrite (list_filter_add_nin Sa).
            exact IHl.
Qed.

Theorem list_filter_inter {U} : ∀ S T (l : list U),
    list_filter S (list_filter T l) = list_filter (S ∩ T) l.
Proof.
    intros S T l.
    induction l.
    -   do 2 rewrite list_filter_end.
        reflexivity.
    -   classic_case (T a) as [Ta|Ta]; [>classic_case (S a) as [Sa|Sa]|].
        +   rewrite (list_filter_add_in Ta).
            rewrite (list_filter_add_in Sa).
            rewrite (list_filter_add_in ((make_and Sa Ta) : (S ∩ T) a)).
            apply f_equal.
            exact IHl.
        +   assert (¬(S ∩ T) a) as STa by (intros [Sa' Ta']; contradiction).
            rewrite (list_filter_add_in Ta).
            rewrite (list_filter_add_nin Sa).
            rewrite (list_filter_add_nin STa).
            exact IHl.
        +   assert (¬(S ∩ T) a) as STa by (intros [Sa' Ta']; contradiction).
            rewrite (list_filter_add_nin Ta).
            rewrite (list_filter_add_nin STa).
            exact IHl.
Qed.

Theorem list_filter_filter {U} : ∀ S (l : list U),
    list_filter S (list_filter S l) = list_filter S l.
Proof.
    intros S l.
    rewrite list_filter_inter.
    rewrite inter_idemp.
    reflexivity.
Qed.

Theorem list_prop_end {U} : ∀ S : U → Prop, list_prop S [].
Proof.
    intros S.
    exact true.
Qed.

Theorem list_prop_add {U} : ∀ S (a : U) l,
    list_prop S (a ꞉ l) ↔ S a ∧ list_prop S l.
Proof.
    reflexivity.
Qed.

Theorem list_prop_single {U} : ∀ S (a : U), list_prop S [a] ↔ S a.
Proof.
    intros S a.
    rewrite list_prop_add.
    rewrite (prop_is_true (list_prop_end S)).
    apply and_rtrue.
Qed.

Tactic Notation "list_prop_induction" ident(l) ident(P) "as"
    simple_intropattern(a) simple_intropattern(nin) simple_intropattern(IHl) :=
    move P before l;
    induction l as [|a l IHl];
    [>|
        rewrite list_prop_add in P;
        specialize (IHl (rand P));
        destruct P as [nin P]
    ].

Theorem list_prop_conc {U} : ∀ S (l1 l2 : list U),
    list_prop S (l1 + l2) ↔ list_prop S l1 ∧ list_prop S l2.
Proof.
    intros S l1 l2.
    induction l1.
    -   rewrite list_conc_lid.
        rewrite (prop_is_true (list_prop_end S)).
        rewrite and_ltrue.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite list_prop_add.
        rewrite IHl1.
        rewrite and_assoc.
        reflexivity.
Qed.

Theorem list_prop_sub {U} : ∀ (l : list U) S T, S ⊆ T →
    list_prop S l → list_prop T l.
Proof.
    intros l S T sub Sl.
    list_prop_induction l Sl as a Sa IHl.
    -   apply list_prop_end.
    -   rewrite list_prop_add.
        apply sub in Sa.
        split; assumption.
Qed.

Theorem list_prop_filter {U} : ∀ (l : list U) S, list_prop S (list_filter S l).
Proof.
    intros l S.
    induction l.
    -   rewrite list_filter_end.
        apply list_prop_end.
    -   classic_case (S a) as [Sa|Sa].
        +   rewrite (list_filter_add_in Sa).
            rewrite list_prop_add.
            split; assumption.
        +   rewrite (list_filter_add_nin Sa).
            exact IHl.
Qed.

Theorem list_prop_in {U} : ∀ (a : list U) S, list_prop S a →
    ∀ x, in_list a x → S x.
Proof.
    intros a S a_in x x_in.
    list_prop_induction a a_in as y Sy IHl.
    -   contradiction x_in.
    -   rewrite in_list_add_eq in x_in.
        destruct x_in as [eq|x_in].
        +   subst.
            exact Sy.
        +   exact (IHl x_in).
Qed.

Theorem list_in_prop {U} : ∀ (a : list U) (S : U → Prop),
    (∀ x, in_list a x → S x) → list_prop S a.
Proof.
    intros a S x_in.
    induction a as [|x a].
    -   apply list_prop_end.
    -   rewrite list_prop_add.
        split.
        +   apply x_in.
            apply in_list_add.
        +   apply IHa.
            intros y y_in.
            apply x_in.
            rewrite in_list_add_eq.
            right; exact y_in.
Qed.

Theorem list_prop_in_sub {U} : ∀ {a b : list U} {S},
    list_prop S b → (∀ x, in_list a x → in_list b x) → list_prop S a.
Proof.
    intros a b S b_in sub.
    induction a as [|x a].
    -   apply list_prop_end.
    -   rewrite list_prop_add.
        split.
        +   apply (list_prop_in _ _ b_in).
            apply sub.
            rewrite in_list_add_eq.
            left; reflexivity.
        +   apply IHa.
            intros y y_in.
            apply sub.
            rewrite in_list_add_eq.
            right; exact y_in.
Qed.

Theorem list_prop_other_filter {U} : ∀ (l : list U) S T,
    list_prop S l → list_prop S (list_filter T l).
Proof.
    intros l S T Sl.
    apply (list_prop_in_sub Sl).
    apply list_filter_in.
Qed.

Theorem list_prop_image {U V} : ∀ S T (f : U → V) l,
    list_prop S l → (∀ x, S x → T (f x)) → list_prop T (list_image f l).
Proof.
    intros S T f l l_in sub.
    list_prop_induction l l_in as x x_in IHl.
    -   rewrite list_image_end.
        apply list_prop_end.
    -   rewrite list_image_add, list_prop_add.
        split; [>|exact IHl].
        apply sub.
        exact x_in.
Qed.

Theorem list_prop2_end {U} : ∀ S : U → U → Prop, list_prop2 S [].
Proof.
    intros S.
    exact true.
Qed.

Theorem list_prop2_add {U} : ∀ S (a : U) l,
    list_prop2 S (a ꞉ l) ↔ list_prop (S a) l ∧ list_prop2 S l.
Proof.
    reflexivity.
Qed.

Theorem list_prop2_single {U} : ∀ S (a : U), list_prop2 S [a].
Proof.
    intros S a.
    rewrite list_prop2_add.
    split.
    -   apply list_prop_end.
    -   apply list_prop2_end.
Qed.
