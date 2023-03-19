Require Import init.

Require Export list_base.

Require Import relation.
Require Import set.

Fixpoint in_list {U : Type} (l : list U) (x : U) :=
    match l with
    | [] => False
    | a ꞉ l' => a = x ∨ in_list l' x
    end.
Arguments in_list : simpl never.

Fixpoint list_unique {U : Type} (l : list U) :=
    match l with
    | [] => True
    | a ꞉ l' => ¬in_list l' a ∧ list_unique l'
    end.
Arguments list_unique : simpl never.

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

Theorem in_list_end {U} : ∀ a : U, ¬in_list [] a.
Proof.
    intros a.
    unfold in_list; cbn.
    rewrite not_false.
    exact true.
Qed.

Theorem in_list_single {U} : ∀ a b : U, in_list [a] b ↔ a = b.
Proof.
    intros a b.
    unfold in_list.
    rewrite or_rfalse.
    reflexivity.
Qed.

Theorem in_list_add {U} : ∀ (a b : U) l,
    in_list (a ꞉ l) b ↔ a = b ∨ in_list l b.
Proof.
    reflexivity.
Qed.

Theorem in_list_conc {U} : ∀ {l1 l2 : list U} {x : U},
    in_list (l1 + l2) x → in_list l1 x ∨ in_list l2 x.
Proof.
    intros l1 l2 x in12.
    apply or_left.
    intros x_nin.
    induction l1.
    -   rewrite list_conc_lid in in12.
        contradiction (x_nin in12).
    -   rewrite in_list_add.
        rewrite list_conc_add in in12.
        rewrite in_list_add in in12.
        destruct in12 as [eq|in12].
        +   left; exact eq.
        +   right; exact (IHl1 in12).
Qed.

Theorem in_list_rconc {U : Type} : ∀ (l1 l2 : list U) {x : U},
    in_list l2 x → in_list (l1 + l2) x.
Proof.
    intros l1 l2 x x_in.
    induction l1.
    -   rewrite list_conc_lid.
        exact x_in.
    -   rewrite list_conc_add.
        rewrite in_list_add.
        right.
        exact IHl1.
Qed.

Theorem in_list_lconc {U : Type} : ∀ (l1 l2 : list U) {x : U},
    in_list l1 x → in_list (l1 + l2) x.
Proof.
    intros l1 l2 x x_in.
    induction l1.
    -   contradiction x_in.
    -   rewrite in_list_add in x_in.
        rewrite list_conc_add.
        rewrite in_list_add.
        destruct x_in as [x_eq|x_in].
        +   left.
            exact x_eq.
        +   right.
            exact (IHl1 x_in).
Qed.

Theorem in_list_comm {U} : ∀ {l1 l2 : list U} {x : U},
    in_list (l1 + l2) x → in_list (l2 + l1) x.
Proof.
    intros l1 l2 x x_in.
    apply in_list_conc in x_in as [x_in|x_in].
    -   exact (in_list_rconc _ _ x_in).
    -   exact (in_list_lconc _ _ x_in).
Qed.

Theorem in_list_split {U : Type} :
    ∀ {l} {x : U}, in_list l x → ∃ l1 l2, l = l1 + x ꞉ l2.
Proof.
    intros l x x_in.
    induction l.
    -   contradiction x_in.
    -   rewrite in_list_add in x_in.
        destruct x_in as [x_eq|x_in].
        +   subst a.
            exists [], l.
            rewrite list_conc_lid.
            reflexivity.
        +   specialize (IHl x_in) as [l1 [l2 l_eq]].
            subst l.
            exists (a ꞉ l1), l2.
            rewrite list_conc_add.
            reflexivity.
Qed.

Theorem in_list_image {U V} : ∀ {l a} (f : U → V),
    in_list l a → in_list (list_image f l) (f a).
Proof.
    intros l a f a_in.
    induction l as [|b l].
    -   contradiction a_in.
    -   rewrite list_image_add, in_list_add.
        rewrite in_list_add in a_in.
        destruct a_in as [eq|a_in].
        +   left.
            rewrite eq.
            reflexivity.
        +   right.
            exact (IHl a_in).
Qed.

Theorem image_in_list {U V} : ∀ {l y} {f : U → V},
    in_list (list_image f l) y → ∃ x, f x = y ∧ in_list l x.
Proof.
    intros l y f y_in.
    induction l.
    -   rewrite list_image_end in y_in.
        contradiction y_in.
    -   rewrite list_image_add, in_list_add in y_in.
        destruct y_in as [y_eq|y_in].
        +   exists a.
            split.
            *   exact y_eq.
            *   rewrite in_list_add.
                left.
                reflexivity.
        +   specialize (IHl y_in) as [x [x_eq x_in]].
            exists x.
            split.
            *   exact x_eq.
            *   rewrite in_list_add.
                right.
                exact x_in.
Qed.

Theorem list_unique_end {U} : list_unique (U := U) [].
Proof.
    exact true.
Qed.

Theorem list_unique_single {U} : ∀ a : U, list_unique [a].
Proof.
    intros a.
    split.
    -   exact (in_list_end a).
    -   exact true.
Qed.

Theorem list_unique_add {U} : ∀ (a : U) l,
    list_unique (a ꞉ l) ↔ ¬in_list l a ∧ list_unique l.
Proof.
    reflexivity.
Qed.

Tactic Notation "list_unique_induction" ident(l) ident(uni) "as"
    simple_intropattern(a) simple_intropattern(nin) simple_intropattern(IHl) :=
    move uni before l;
    induction l as [|a l IHl];
    [>|
        rewrite list_unique_add in uni;
        specialize (IHl (rand uni));
        destruct uni as [nin uni]
    ].

Theorem list_unique_comm_add {U} : ∀ (l : list U) a,
    list_unique (a ꞉ l) → list_unique (l + [a]).
Proof.
    intros l a.
    rewrite list_unique_add.
    intros [a_nin l_uni].
    list_unique_induction l l_uni as b b_nin IHl.
    -   rewrite list_conc_lid.
        apply list_unique_single.
    -   rewrite in_list_add in a_nin.
        rewrite not_or in a_nin.
        destruct a_nin as [neq a_nin].
        rewrite list_conc_add, list_unique_add.
        split.
        +   intros contr.
            apply in_list_conc in contr as [b_in|b_eq].
            *   contradiction (b_nin b_in).
            *   rewrite in_list_single in b_eq.
                symmetry in b_eq; contradiction (neq b_eq).
        +   exact (IHl a_nin).
Qed.

Lemma list_unique_comm' {U} : ∀ l1 l2 : list U,
    list_unique (l1 + l2) → list_unique (l2 + l1).
Proof.
    induction l1; intros l2 uni.
    -   rewrite list_conc_lid in uni.
        rewrite list_conc_rid.
        exact uni.
    -   rewrite list_conc_add in uni.
        apply list_unique_comm_add in uni.
        rewrite <- plus_assoc in uni.
        apply IHl1 in uni.
        rewrite <- plus_assoc in uni.
        rewrite list_conc_single in uni.
        exact uni.
Qed.

Theorem list_unique_comm {U} : ∀ l1 l2 : list U,
    list_unique (l1 + l2) ↔ list_unique (l2 + l1).
Proof.
    intros l1 l2.
    split; apply list_unique_comm'.
Qed.

Theorem list_unique_lconc {U} : ∀ (l1 l2 : list U),
    list_unique (l1 + l2) → list_unique l1.
Proof.
    intros l1 l2 uni.
    induction l1.
    -   exact list_unique_end.
    -   rewrite list_conc_add, list_unique_add in uni.
        destruct uni as [a_nin uni].
        rewrite list_unique_add.
        split.
        +   intros contr.
            apply (in_list_lconc l1 l2) in contr.
            contradiction (a_nin contr).
        +   exact (IHl1 uni).
Qed.

Theorem list_unique_rconc {U} : ∀ (l1 l2 : list U),
    list_unique (l1 + l2) → list_unique l2.
Proof.
    intros l1 l2.
    rewrite list_unique_comm.
    apply list_unique_lconc.
Qed.

Theorem list_unique_conc {U} : ∀ (l1 l2 : list U),
    list_unique (l1 + l2) → (∀ x, in_list l1 x → ¬in_list l2 x).
Proof.
    intros l1 l2 uni x x_in1 x_in2.
    induction l1.
    -   contradiction x_in1.
    -   rewrite list_conc_add, list_unique_add in uni.
        destruct uni as [a_nin uni].
        rewrite in_list_add in x_in1.
        destruct x_in1 as [eq|x_in1].
        +   subst a.
            apply (in_list_rconc l1 l2) in x_in2.
            contradiction (a_nin x_in2).
        +   exact (IHl1 uni x_in1).
Qed.

Theorem list_image_unique {U V} : ∀ (l : list U) (f : U → V),
    list_unique (list_image f l) → list_unique l.
Proof.
    intros l f l_uni.
    induction l.
    -   exact list_unique_end.
    -   rewrite list_image_add in l_uni.
        rewrite list_unique_add in l_uni.
        rewrite list_unique_add.
        destruct l_uni as [fa_nin l_uni].
        specialize (IHl l_uni).
        split.
        +   contrapositive fa_nin.
            apply in_list_image.
        +   exact IHl.
Qed.

Theorem list_filter_end {U} : ∀ (S : U → Prop), list_filter S [] = [].
Proof.
    reflexivity.
Qed.

Theorem list_filter_single_in {U} : ∀ (S : U → Prop) a,
    S a → list_filter S [a] = [a].
Proof.
    intros S a Sa.
    unfold list_filter.
    exact (if_true Sa).
Qed.

Theorem list_filter_single_nin {U} : ∀ (S : U → Prop) a,
    ¬S a → list_filter S [a] = [].
Proof.
    intros S a Sa.
    unfold list_filter.
    exact (if_false Sa).
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

Theorem list_filter_in {U} : ∀ S (l : list U) x,
    in_list (list_filter S l) x → in_list l x.
Proof.
    intros S l x x_in.
    induction l.
    -   rewrite list_filter_end in x_in.
        contradiction x_in.
    -   rewrite in_list_add.
        classic_case (S a) as [Sa|Sa].
        +   rewrite (list_filter_add_in Sa) in x_in.
            rewrite in_list_add in x_in.
            destruct x_in as [x_eq|x_in].
            *   subst a.
                left; reflexivity.
            *   right; exact (IHl x_in).
        +   rewrite (list_filter_add_nin Sa) in x_in.
            right; exact (IHl x_in).
Qed.

Theorem list_filter_in_set {U} : ∀ S (l : list U) x,
    in_list (list_filter S l) x → S x.
Proof.
    intros S l x x_in.
    induction l.
    -   rewrite list_filter_end in x_in.
        contradiction x_in.
    -   classic_case (S a) as [Sa|Sa].
        +   rewrite (list_filter_add_in Sa) in x_in.
            rewrite in_list_add in x_in.
            destruct x_in as [eq|x_in].
            *   subst x.
                exact Sa.
            *   exact (IHl x_in).
        +   rewrite (list_filter_add_nin Sa) in x_in.
            exact (IHl x_in).
Qed.

Theorem list_filter_unique {U} : ∀ S (l : list U),
    list_unique l → list_unique (list_filter S l).
Proof.
    intros S l l_uni.
    list_unique_induction l l_uni as a a_nin IHl.
    -   rewrite list_filter_end.
        exact list_unique_end.
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
        exact list_unique_end.
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

Theorem list_prop_single {U} : ∀ S (a : U), list_prop S [a] ↔ S a.
Proof.
    intros S a.
    unfold list_prop.
    rewrite and_rtrue.
    reflexivity.
Qed.

Theorem list_prop_add {U} : ∀ S (a : U) l,
    list_prop S (a ꞉ l) ↔ S a ∧ list_prop S l.
Proof.
    reflexivity.
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

Theorem list_prop_filter {U} : ∀ (l : list U) S T,
    list_prop S l → list_prop S (list_filter T l).
Proof.
    intros l S T Sl.
    list_prop_induction l Sl as a Sa IHl.
    -   rewrite list_filter_end.
        apply list_prop_end.
    -   classic_case (T a) as [Ta|Ta].
        +   rewrite (list_filter_add_in Ta).
            rewrite list_prop_add.
            split; assumption.
        +   rewrite (list_filter_add_nin Ta).
            exact IHl.
Qed.

Theorem list_prop2_end {U} : ∀ S : U → U → Prop, list_prop2 S [].
Proof.
    intros S.
    exact true.
Qed.

Theorem list_prop2_single {U} : ∀ S (a : U), list_prop2 S [a].
Proof.
    intros S a.
    unfold list_prop2.
    rewrite and_rtrue.
    apply list_prop_end.
Qed.

Theorem list_prop2_add {U} : ∀ S (a : U) l,
    list_prop2 S (a ꞉ l) ↔ list_prop (S a) l ∧ list_prop2 S l.
Proof.
    reflexivity.
Qed.
