Require Import init.

Require Export list_base.

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

Fixpoint list_make_unique {U : Type} (l : list U) :=
    match l with
    | [] => []
    | a ꞉ l' => If in_list l' a
        then list_make_unique l'
        else a ꞉ list_make_unique l'
    end.
Arguments list_make_unique : simpl never.

Theorem in_list_end {U} : ∀ a : U, ¬in_list [] a.
Proof.
    intros a.
    unfold in_list; cbn.
    apply not_false.
Qed.

Theorem in_list_add_eq {U} : ∀ (a b : U) l,
    in_list (a ꞉ l) b ↔ a = b ∨ in_list l b.
Proof.
    reflexivity.
Qed.

Theorem in_list_add {U} : ∀ (a : U) l, in_list (a ꞉ l) a.
Proof.
    intros a l.
    rewrite in_list_add_eq.
    left; reflexivity.
Qed.

Theorem in_list_single_eq {U} : ∀ a b : U, in_list [a] b ↔ a = b.
Proof.
    intros a b.
    rewrite in_list_add_eq.
    rewrite (prop_is_false (in_list_end b)).
    rewrite or_rfalse.
    reflexivity.
Qed.

Theorem in_list_single {U} : ∀ a : U, in_list [a] a.
Proof.
    intros a.
    rewrite in_list_single_eq.
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
    -   rewrite in_list_add_eq.
        rewrite list_conc_add in in12.
        rewrite in_list_add_eq in in12.
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
        rewrite in_list_add_eq.
        right.
        exact IHl1.
Qed.

Theorem in_list_lconc {U : Type} : ∀ (l1 l2 : list U) {x : U},
    in_list l1 x → in_list (l1 + l2) x.
Proof.
    intros l1 l2 x x_in.
    induction l1.
    -   contradiction x_in.
    -   rewrite in_list_add_eq in x_in.
        rewrite list_conc_add.
        rewrite in_list_add_eq.
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
    -   rewrite in_list_add_eq in x_in.
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
    -   rewrite list_image_add, in_list_add_eq.
        rewrite in_list_add_eq in a_in.
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
    -   rewrite list_image_add, in_list_add_eq in y_in.
        destruct y_in as [y_eq|y_in].
        +   exists a.
            split.
            *   exact y_eq.
            *   rewrite in_list_add_eq.
                left.
                reflexivity.
        +   specialize (IHl y_in) as [x [x_eq x_in]].
            exists x.
            split.
            *   exact x_eq.
            *   rewrite in_list_add_eq.
                right.
                exact x_in.
Qed.

Theorem in_list_flatten {U} : ∀ (a : U) l, in_list (list_flatten l) a →
    ∃ al, in_list l al ∧ in_list al a.
Proof.
    intros a l a_in.
    induction l as [|al l].
    -   rewrite list_flatten_end in a_in.
        apply in_list_end in a_in.
        contradiction.
    -   rewrite list_flatten_add in a_in.
        apply in_list_conc in a_in.
        destruct a_in as [a_in|a_in].
        +   exists al.
            split.
            *   apply in_list_add.
            *   exact a_in.
        +   specialize (IHl a_in) as [al' [al'_in a_in']].
            exists al'.
            split.
            *   rewrite in_list_add_eq.
                right.
                exact al'_in.
            *   exact a_in'.
Qed.

Theorem list_unique_end U : list_unique (U := U) [].
Proof.
    exact true.
Qed.

Theorem list_unique_add {U} : ∀ (a : U) l,
    list_unique (a ꞉ l) ↔ ¬in_list l a ∧ list_unique l.
Proof.
    reflexivity.
Qed.

Theorem list_unique_single {U} : ∀ a : U, list_unique [a].
Proof.
    intros a.
    rewrite list_unique_add.
    split.
    -   exact (in_list_end a).
    -   exact true.
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
    -   rewrite in_list_add_eq in a_nin.
        rewrite not_or in a_nin.
        destruct a_nin as [neq a_nin].
        rewrite list_conc_add, list_unique_add.
        split.
        +   intros contr.
            apply in_list_conc in contr as [b_in|b_eq].
            *   contradiction (b_nin b_in).
            *   rewrite in_list_single_eq in b_eq.
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
    -   apply list_unique_end.
    -   rewrite list_conc_add, list_unique_add in uni.
        destruct uni as [a_nin uni].
        rewrite list_unique_add.
        split.
        +   contrapositive a_nin.
            apply in_list_lconc.
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
        rewrite in_list_add_eq in x_in1.
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
    -   apply list_unique_end.
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

Theorem list_image_unique_inj {U V} : ∀ (l : list U) (f : U → V),
    Injective f → list_unique l → list_unique (list_image f l).
Proof.
    intros l f f_inj l_uni.
    list_unique_induction l l_uni as a a_nin IHl.
    -   rewrite list_image_end.
        apply list_unique_end.
    -   rewrite list_image_add, list_unique_add.
        split; [>|exact IHl].
        intros contr.
        apply image_in_list in contr as [x [x_eq x_in]].
        apply inj in x_eq.
        subst x.
        contradiction.
Qed.

Theorem list_make_unique_end {U} : list_make_unique (U := U) [] = [].
Proof.
    reflexivity.
Qed.

Theorem list_make_unique_add_in {U} : ∀ {a : U} {l},
    in_list l a → list_make_unique (a ꞉ l) = list_make_unique l.
Proof.
    intros a l a_in.
    unfold list_make_unique at 1; fold (list_make_unique (U := U)).
    rewrite (if_true a_in).
    reflexivity.
Qed.

Theorem list_make_unique_add_nin {U} : ∀ {a : U} {l},
    ¬in_list l a → list_make_unique (a ꞉ l) = a ꞉ list_make_unique l.
Proof.
    intros a l a_in.
    unfold list_make_unique at 1; fold (list_make_unique (U := U)).
    rewrite (if_false a_in).
    reflexivity.
Qed.

Theorem list_make_unique_single {U} : ∀ a : U, list_make_unique [a] = [a].
Proof.
    intros a.
    rewrite list_make_unique_add_nin by apply in_list_end.
    rewrite list_make_unique_end.
    reflexivity.
Qed.

Theorem list_make_unique_in {U} : ∀ l (a : U),
    in_list l a ↔ in_list (list_make_unique l) a.
Proof.
    intros l a.
    induction l as [|b l].
    -   rewrite list_make_unique_end.
        reflexivity.
    -   rewrite in_list_add_eq.
        split.
        +   intros [eq|a_in].
            *   subst.
                classic_case (in_list l a) as [a_in|a_nin].
                --  rewrite (list_make_unique_add_in a_in).
                    apply IHl.
                    exact a_in.
                --  rewrite (list_make_unique_add_nin a_nin).
                    apply in_list_add.
            *   apply IHl in a_in.
                classic_case (in_list l b) as [b_in|b_nin].
                --  rewrite (list_make_unique_add_in b_in).
                    exact a_in.
                --  rewrite (list_make_unique_add_nin b_nin).
                    apply in_list_add_eq.
                    right.
                    exact a_in.
        +   intros a_in.
            classic_case (in_list l b) as [b_in|b_nin].
            *   rewrite (list_make_unique_add_in b_in) in a_in.
                apply IHl in a_in.
                right; exact a_in.
            *   rewrite (list_make_unique_add_nin b_nin) in a_in.
                rewrite in_list_add_eq in a_in.
                rewrite IHl.
                exact a_in.
Qed.

Theorem list_make_unique_unique {U} :
    ∀ l : list U, list_unique (list_make_unique l).
Proof.
    intros l.
    induction l as [|a l].
    -   rewrite list_make_unique_end.
        apply list_unique_end.
    -   classic_case (in_list l a) as [a_in|a_nin].
        +   rewrite (list_make_unique_add_in a_in).
            exact IHl.
        +   rewrite (list_make_unique_add_nin a_nin).
            apply list_unique_add.
            rewrite <- list_make_unique_in.
            split; assumption.
Qed.
