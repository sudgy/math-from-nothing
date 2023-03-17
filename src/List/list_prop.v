Require Import init.

Require Export list_base.

Require Import relation.
Require Import set.

Set Implicit Arguments.

Fixpoint in_list (A : Type) (l : list A) (x : A) :=
    match l with
    | list_end => False
    | a ꞉ l' => a = x ∨ in_list l' x
    end.

Fixpoint list_unique {A : Type} (l : list A) :=
    match l with
    | a ꞉ l' => ¬in_list l' a ∧ list_unique l'
    | _ => True
    end.

Fixpoint list_filter {U} (S : U → Prop) (l : list U) :=
    match l with
    | list_end => list_end
    | x ꞉ l' => If S x then x ꞉ list_filter S l' else list_filter S l'
    end.

Fixpoint list_prop {U} (S : U → Prop) (l : list U) :=
    match l with
    | list_end => True
    | a ꞉ l' => S a ∧ list_prop S l'
    end.

(** Note that this only checks all pairs from left to right and doesn't evaluate
S on an element with itself.  If you want both directions, give an S that
manually checks both directions, and if you want to check an element with
itself, use list_prop. *)
Fixpoint list_prop2 {U} (S : U → U → Prop) (l : list U) :=
    match l with
    | list_end => True
    | a ꞉ l' => list_prop (S a) l' ∧ list_prop2 S l'
    end.

Theorem in_list_conc (A : Type) : ∀ (l1 l2 : list A) (x : A),
        in_list (l1 + l2) x → in_list l1 x ∨ in_list l2 x.
    intros l1 l2 x in12.
    induction l1.
    -   right.
        cbn in in12.
        exact in12.
    -   cbn in in12.
        destruct in12 as [ax|in12].
        +   left.
            left.
            exact ax.
        +   specialize (IHl1 in12) as [in1|in2].
            *   left; right.
                exact in1.
            *   right.
                exact in2.
Qed.

Theorem in_list_rconc {U : Type} : ∀ (l1 l2 : list U) (x : U),
        in_list l2 x → in_list (l1 + l2) x.
    intros l1 l2 x x_in.
    induction l1.
    -   cbn.
        exact x_in.
    -   right.
        exact IHl1.
Qed.

Theorem in_list_lconc {U : Type} : ∀ (l1 l2 : list U) (x : U),
        in_list l1 x → in_list (l1 + l2) x.
    intros l1 l2 x x_in.
    induction l1.
    -   contradiction x_in.
    -   destruct x_in as [x_eq|x_in].
        +   left.
            exact x_eq.
        +   right.
            exact (IHl1 x_in).
Qed.

Theorem in_list_split {U : Type} :
        ∀ l (x : U), in_list l x → ∃ l1 l2, l = l1 + x ꞉ l2.
    intros l x x_in.
    induction l.
    -   contradiction x_in.
    -   destruct x_in as [x_eq|x_in].
        +   subst a.
            exists list_end, l.
            cbn.
            reflexivity.
        +   specialize (IHl x_in).
            destruct IHl as [l1 [l2 l_eq]].
            rewrite l_eq; clear l_eq.
            exists (a ꞉ l1), l2.
            cbn.
            reflexivity.
Qed.

Theorem in_list_image {U V} : ∀ l a (f : U → V),
        in_list l a → in_list (list_image f l) (f a).
    intros l a f a_in.
    induction l as [|b l].
    -   contradiction a_in.
    -   cbn.
        cbn in a_in.
        destruct a_in as [eq|a_in].
        +   left.
            rewrite eq.
            reflexivity.
        +   right.
            exact (IHl a_in).
Qed.

Theorem image_in_list {U V} : ∀ l y (f : U → V),
        in_list (list_image f l) y → ∃ x, f x = y ∧ in_list l x.
    intros l y f y_in.
    induction l.
    -   contradiction y_in.
    -   destruct y_in as [y_eq|y_in].
        +   exists a.
            split.
            *   exact y_eq.
            *   left.
                reflexivity.
        +   specialize (IHl y_in) as [x [x_eq x_in]].
            exists x.
            split.
            *   exact x_eq.
            *   right.
                exact x_in.
Qed.

Theorem list_unique_add {U} : ∀ (l : list U) a,
        list_unique (a ꞉ l) → list_unique (l + (a ꞉ list_end)).
    intros l a [a_nin a_uni].
    induction l.
    -   rewrite list_conc_lid.
        cbn.
        rewrite not_false.
        split; exact true.
    -   cbn in a_nin.
        rewrite not_or in a_nin.
        destruct a_nin as [neq a_nin].
        split.
        +   intros contr.
            apply in_list_conc in contr as [a0_in|a0_eq].
            *   destruct a_uni; contradiction.
            *   cbn in a0_eq.
                rewrite neq_sym in neq.
                destruct a0_eq as [eq|contr]; contradiction.
        +   exact (IHl a_nin (rand a_uni)).
Qed.

Theorem list_unique_conc {U} : ∀ l1 l2 : list U,
        list_unique (l1 + l2) → list_unique (l2 + l1).
    induction l1; intros l2 uni.
    -   rewrite list_conc_lid in uni.
        rewrite list_conc_rid.
        exact uni.
    -   change ((a ꞉ l1) + l2) with (a ꞉ (l1 + l2)) in uni.
        apply list_unique_add in uni.
        rewrite <- plus_assoc in uni.
        specialize (IHl1 _ uni).
        rewrite <- plus_assoc in IHl1.
        rewrite list_conc_single in IHl1.
        exact IHl1.
Qed.

Lemma list_filter_conc {U} : ∀ (S : U → Prop) l1 l2,
    list_filter S (l1 + l2) = list_filter S l1 + list_filter S l2.
Proof.
    intros S l1 l2.
    induction l1 as [|a l1].
    -   cbn.
        do 2 rewrite list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        cbn.
        rewrite IHl1.
        case_if [Sa|nSa].
        +   apply list_conc_add.
        +   reflexivity.
Qed.

Theorem list_filter_in_S {U} : ∀ S (l : list U) x,
        in_list (list_filter S l) x → S x.
    intros S l x x_in.
    induction l.
    -   contradiction x_in.
    -   cbn in x_in.
        case_if.
        +   destruct x_in as [eq|x_in].
            *   subst.
                exact s.
            *   exact (IHl x_in).
        +   exact (IHl x_in).
Qed.

Theorem list_filter_in {U} : ∀ S (l : list U) x,
        in_list (list_filter S l) x → in_list l x.
    intros S l x x_in.
    induction l.
    -   contradiction x_in.
    -   cbn in x_in.
        case_if.
        +   cbn in x_in.
            destruct x_in as [x_eq|x_in].
            *   subst a.
                left.
                reflexivity.
            *   right.
                exact (IHl x_in).
        +   right.
            exact (IHl x_in).
Qed.

Theorem list_filter_unique {U} : ∀ S (l : list U),
        list_unique l → list_unique (list_filter S l).
    intros S l l_uni.
    induction l.
    -   cbn.
        exact true.
    -   cbn in *.
        case_if.
        +   cbn.
            split.
            *   intros contr.
                apply l_uni.
                apply list_filter_in with S.
                exact contr.
            *   apply IHl.
                apply l_uni.
        +   apply IHl.
            apply l_uni.
Qed.

Theorem list_filter_image_in {U V} : ∀ S (f : U → V) (l : list U) x,
        in_list (list_image f (list_filter S l)) x → in_list (list_image f l) x.
    intros S f l x x_in.
    induction l.
    -   contradiction x_in.
    -   cbn in x_in.
        case_if.
        +   cbn in x_in.
            destruct x_in as [x_eq|x_in].
            *   subst x.
                left.
                reflexivity.
            *   right.
                exact (IHl x_in).
        +   right.
            exact (IHl x_in).
Qed.

Theorem list_filter_image_unique {U V} : ∀ S (f : U → V) (l : list U),
        list_unique (list_image f l) →
        list_unique (list_image f (list_filter S l)).
    intros S f l l_uni.
    induction l.
    -   cbn.
        exact true.
    -   cbn in *.
        case_if.
        +   cbn.
            split.
            *   intros contr.
                apply l_uni.
                apply list_filter_image_in with S.
                exact contr.
            *   apply IHl.
                apply l_uni.
        +   apply IHl.
            apply l_uni.
Qed.

Theorem list_filter_filter {U} : ∀ S (l : list U),
        list_filter S l = list_filter S (list_filter S l).
    intros S l.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        case_if.
        +   cbn.
            case_if.
            *   rewrite IHl at 1.
                reflexivity.
            *   contradiction.
        +   exact IHl.
Qed.

Theorem list_image_unique {U V} : ∀ (l : list U) (f : U → V),
        list_unique (list_image f l) → list_unique l.
    intros l f l_uni.
    induction l.
    -   exact true.
    -   cbn in *.
        split.
        +   intros contr.
            apply l_uni.
            clear l_uni IHl.
            apply in_list_image.
            exact contr.
        +   apply IHl.
            apply l_uni.
Qed.

Theorem list_prop_sub {U} : ∀ (l : list U) S T, S ⊆ T →
        list_prop S l → list_prop T l.
    intros l S T sub Sl.
    induction l.
    -   exact true.
    -   cbn.
        split.
        +   apply sub.
            apply Sl.
        +   apply IHl.
            apply Sl.
Qed.

Theorem list_prop_filter {U} : ∀ (l : list U) S T,
        list_prop S l → list_prop S (list_filter T l).
    intros l S T Sl.
    induction l.
    -   cbn.
        exact true.
    -   destruct Sl as [Sa Sl].
        specialize (IHl Sl).
        cbn.
        case_if.
        +   cbn.
            split; assumption.
        +   exact IHl.
Qed.
