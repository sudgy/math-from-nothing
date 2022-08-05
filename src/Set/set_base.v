Require Import init.

Require Export relation.
Require Export op.

Unset Keyed Unification.

Declare Scope set_scope.
Delimit Scope set_scope with set.

(* begin hide *)
Open Scope set_scope.
(* end hide *)

Definition subset {U : Type} (S T : U → Prop) := ∀ x, S x → T x.
Infix "⊆" := subset.
Definition strict_subset {U : Type} (A B : U → Prop) := A ⊆ B ∧ A ≠ B.
Infix "⊂" := strict_subset (at level 50, no associativity).

Definition empty {U : Type} := λ x : U, False.
Definition all {U : Type} := λ x : U, True.
Notation "∅" := empty.

Definition singleton {U : Type} (x : U) := λ y, x = y.

Definition union {U : Type} (S T : U → Prop) := λ x, S x ∨ T x.
Infix "∪" := union.
Definition intersection {U : Type} (S T : U → Prop) := λ x, S x ∧ T x.
Infix "∩" := intersection.
Definition set_minus {U : Type} (S T : U → Prop) := λ x, S x ∧ ¬T x.
Infix "-" := set_minus : set_scope.
Definition symmetric_difference {U : Type} (S T : U → Prop) := (S-T) ∪ (T-S).
Infix "+" := symmetric_difference : set_scope.
Definition complement {U : Type} (S : U → Prop) := λ x, ¬S x.

Definition cartesian_product {U V : Type} (S : U → Prop) (T : V → Prop) :=
    λ (x : U * V), S (fst x) ∧ T (snd x).
Infix "*" := cartesian_product : set_scope.

Definition disjoint {U : Type} (S T : U → Prop) := S ∩ T = ∅.
Definition intersects {U : Type} (S T : U → Prop) := S ∩ T ≠ ∅.

(* begin hide *)
Section SetBase.

Context {U : Type}.

Lemma subset_refl_ : ∀ S : U → Prop, S ⊆ S.
    intros S x Sx.
    exact Sx.
Qed.
Global Instance subset_refl : Reflexive subset := {
    refl := subset_refl_
}.

Lemma subset_trans_ : ∀ R S T : U → Prop, R ⊆ S → S ⊆ T → R ⊆ T.
    intros R S T RS ST x Rx.
    apply ST.
    apply RS.
    exact Rx.
Qed.
Global Instance subset_trans : Transitive subset := {
    trans := subset_trans_
}.

Lemma subset_antisym_ : ∀ S T : U → Prop, S ⊆ T → T ⊆ S → S = T.
    intros S T ST TS.
    apply predicate_ext.
    intro x.
    split.
    -   apply ST.
    -   apply TS.
Qed.
Global Instance subset_antisym : Antisymmetric subset := {
    antisym := subset_antisym_
}.
(* end hide *)
Theorem empty_sub : ∀ S : U → Prop, ∅ ⊆ S.
    intros S x contr.
    contradiction contr.
Qed.
Theorem sub_all : ∀ S : U → Prop, S ⊆ all.
    intros S x Sx.
    unfold all.
    trivial.
Qed.

Theorem not_ex_empty : ∀ S : U → Prop, (∀ x, ¬S x) → S = ∅.
    intros S all_not.
    apply antisym.
    -   intros x Sx.
        specialize (all_not x).
        contradiction.
    -   apply empty_sub.
Qed.

Theorem not_empty_ex : ∀ S : U → Prop, S ≠ ∅ → ∃ x, S x.
    intros S S_neq.
    classic_contradiction contr.
    rewrite not_ex in contr.
    apply not_ex_empty in contr.
    contradiction.
Qed.

Theorem ex_not_empty : ∀ S : U → Prop, (∃ x, S x) → S ≠ ∅.
    intros S [x Sx] contr.
    rewrite contr in Sx.
    contradiction Sx.
Qed.

Theorem empty_not_ex : ∀ S : U → Prop, S = ∅ → (∀ x, ¬S x).
    intros S eq x Sx.
    rewrite eq in Sx.
    contradiction Sx.
Qed.

Theorem not_all_not_ex : ∀ S : U → Prop, S ≠ all → (∃ x, ¬S x).
    intros S S_neq.
    classic_contradiction contr.
    apply S_neq.
    apply antisym.
    -   intros x Sx; exact true.
    -   intros x C; clear C.
        rewrite not_ex in contr.
        specialize (contr x).
        rewrite not_not in contr.
        exact contr.
Qed.

Theorem all_is_all : ∀ S : U → Prop, (∀ x, S x) → S = all.
    intros S all_x.
    apply antisym.
    -   intros x Sx.
        exact true.
    -   intros x Ax.
        apply all_x.
Qed.

Theorem not_in_empty : ∀ x : U, ¬∅ x.
    intros x contr.
    contradiction contr.
Qed.

Theorem set_comm_base : ∀ (op : (U → Prop) → (U → Prop) → (U → Prop)),
        (∀ A B, op A B ⊆ op B A) → (∀ A B, op A B = op B A).
    intros op sub A B.
    apply antisym; apply sub.
Qed.
Theorem set_assoc_base: ∀ (op : (U → Prop) → (U → Prop) → (U → Prop)), Comm op →
        (∀ A B C, op A (op B C) ⊆ op (op A B) C) →
        (∀ A B C, op A (op B C) = op (op A B) C).
    intros op H sub A B C.
    apply antisym.
    -   apply sub.
    -   destruct H.
        do 2 rewrite (comm A).
        do 2 rewrite (comm _ C).
        apply sub.
Qed.

Lemma union_comm : ∀ S T : U → Prop, S ∪ T = T ∪ S.
    apply set_comm_base.
    intros S T x [Sx|Tx].
    -   right; exact Sx.
    -   left; exact Tx.
Qed.

(* begin hide *)
Global Instance union_comm_class : Comm union := {
    comm := union_comm
}.
(* end hide *)
Lemma union_assoc : ∀ R S T : U → Prop, R ∪ (S ∪ T) = (R ∪ S) ∪ T.
    apply set_assoc_base; try exact union_comm_class.
    intros R S T x [Rx|[Sx|Tx]].
    -   left; left; exact Rx.
    -   left; right; exact Sx.
    -   right; exact Tx.
Qed.

(* begin hide *)
Global Instance union_assoc_class : Assoc union := {
    assoc := union_assoc
}.

Global Instance union_id : Id union := {
    id := @empty U
}.
(* end hide *)
Lemma union_lid : ∀ S : U → Prop, ∅ ∪ S = S.
    intros S.
    apply antisym.
    -   intros x [x_contr|x_in].
        +   contradiction x_contr.
        +   exact x_in.
    -   intros x x_in.
        right; exact x_in.
Qed.

(* begin hide *)
Global Instance union_lid_class : Lid union := {
    lid := union_lid
}.

Global Instance union_ani : Anni union := {
    anni := @all U
}.
(* end hide *)
Lemma union_lanni : ∀ S : U → Prop, all ∪ S = all.
    intros S.
    apply antisym.
    -   intros x x_in.
        unfold all.
        trivial.
    -   intros x x_in.
        left.
        exact x_in.
Qed.

(* begin hide *)
Global Instance union_lanni_class : Lanni union := {
    lanni := union_lanni
}.
(* end hide *)
Theorem union_lsub : ∀ S T : U → Prop, S ⊆ S ∪ T.
    intros S T x Sx.
    left; exact Sx.
Qed.
Theorem union_rsub : ∀ S T : U → Prop, T ⊆ S ∪ T.
    intros S T.
    rewrite comm.
    apply union_lsub.
Qed.

Theorem union_compl_all : ∀ S : U → Prop, S ∪ complement S = all.
    intros S.
    apply antisym.
    -   intros x x_in.
        unfold all.
        trivial.
    -   intros x C; clear C.
        exact (excluded_middle (S x)).
Qed.

Lemma union_idemp : ∀ S : U → Prop, S ∪ S = S.
    intros S.
    apply antisym.
    -   intros x [Sx|Sx]; exact Sx.
    -   intros x Sx; left; exact Sx.
Qed.

(* begin hide *)
Global Instance union_idemp_class : Idempotent union := {
    idemp := union_idemp
}.
(* end hide *)
Lemma inter_comm : ∀ S T : U → Prop, S ∩ T = T ∩ S.
    apply set_comm_base.
    intros S T x [Sx Tx].
    split; assumption.
Qed.

(* begin hide *)
Global Instance inter_comm_class : Comm intersection := {
    comm := inter_comm
}.
(* end hide *)
Lemma inter_assoc : ∀ R S T : U → Prop, R ∩ (S ∩ T) = (R ∩ S) ∩ T.
    apply set_assoc_base; try exact inter_comm_class.
    intros R S T.
    intros x [Rx [Sx Tx]].
    repeat split; assumption.
Qed.

(* begin hide *)
Global Instance inter_assoc_class : Assoc intersection := {
    assoc := inter_assoc
}.

Global Instance inter_id : Id intersection := {
    id := @all U
}.
(* end hide *)
Lemma inter_lid : ∀ S : U → Prop, all ∩ S = S.
    intros S.
    apply antisym.
    -   intros x [x_all Sx].
        exact Sx.
    -   intros x Sx.
        split.
        +   unfold all; trivial.
        +   exact Sx.
Qed.

(* begin hide *)
Global Instance inter_lid_class : Lid intersection := {
    lid := inter_lid
}.

Global Instance inter_ani : Anni intersection := {
    anni := @empty U
}.
(* end hide *)
Lemma inter_lanni : ∀ S : U → Prop, ∅ ∩ S = ∅.
    intros S.
    apply not_ex_empty.
    intros x [contr Sx].
    contradiction contr.
Qed.

(* begin hide *)
Global Instance inter_lanni_class : Lanni intersection := {
    lanni := inter_lanni
}.
(* end hide *)
Theorem inter_lsub : ∀ S T : U → Prop, S ∩ T ⊆ S.
    intros S T x [Sx Tx].
    exact Sx.
Qed.
Theorem inter_rsub : ∀ S T : U → Prop, S ∩ T ⊆ T.
    intros S T.
    rewrite comm.
    apply inter_lsub.
Qed.

Theorem lsub_inter_equal : ∀ S T : U → Prop, S ⊆ T → S ∩ T = S.
    intros S T sub.
    apply antisym.
    -   intros x [Sx Tx].
        exact Sx.
    -   intros x Sx.
        split.
        +   exact Sx.
        +   exact (sub x Sx).
Qed.

Theorem rsub_inter_equal : ∀ S T : U → Prop, T ⊆ S → S ∩ T = T.
    intros S T sub.
    rewrite comm.
    apply lsub_inter_equal.
    exact sub.
Qed.

Theorem inter_compl_empty : ∀ S : U → Prop, S ∩ complement S = ∅.
    intros S.
    apply not_ex_empty.
    intros x [Sx nSx].
    contradiction.
Qed.

Lemma inter_idemp : ∀ S : U → Prop, S ∩ S = S.
    intros S.
    apply antisym.
    -   intros x [Sx Sx']; exact Sx.
    -   intros x Sx; split; exact Sx.
Qed.

(* begin hide *)
Global Instance inter_idemp_class : Idempotent intersection := {
    idemp := inter_idemp
}.
(* end hide *)
Theorem union_ldist : ∀ R S T : U → Prop, R ∪ (S ∩ T) = (R ∪ S) ∩ (R ∪ T).
    intros R S T.
    apply antisym.
    -   intros x [Rx|[Sx Tx]].
        +   split; left; exact Rx.
        +   split; right; assumption.
    -   intros x [[Rx|Sx] [Rx2|Tx]].
        +   left; apply Rx.
        +   left; apply Rx.
        +   left; apply Rx2.
        +   right; split; assumption.
Qed.
Theorem union_rdist : ∀ R S T : U → Prop, (R ∩ S) ∪ T = (R ∪ T) ∩ (S ∪ T).
    intros R S T.
    do 3 rewrite (union_comm _ T).
    apply union_ldist.
Qed.
Theorem inter_ldist : ∀ R S T : U → Prop, R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T).
    intros R S T.
    apply antisym.
    -   intros x [Rx [Sx|Tx]].
        +   left; split; assumption.
        +   right; split; assumption.
    -   intros x [[Rx Sx]|[Rx Tx]]; split; try assumption.
        +   left; exact Sx.
        +   right; exact Tx.
Qed.
Theorem inter_rdist : ∀ R S T : U → Prop, (R ∪ S) ∩ T = (R ∩ T) ∪ (S ∩ T).
    intros R S T.
    do 3 rewrite (inter_comm _ T).
    apply inter_ldist.
Qed.

Theorem union_inter_self : ∀ A B : U → Prop, A ∪ (A ∩ B) = A.
    intros A B.
    apply antisym.
    -   intros x [Ax|[Ax Bx]]; exact Ax.
    -   intros x Ax.
        left; exact Ax.
Qed.
Theorem inter_union_self : ∀ A B : U → Prop, A ∩ (A ∪ B) = A.
    intros A B.
    apply antisym.
    -   intros x [Ax Bx]; exact Ax.
    -   intros x Ax.
        split; try left; exact Ax.
Qed.

Theorem compl_compl : ∀ A : U → Prop, complement (complement A) = A.
    intros A.
    unfold complement.
    apply antisym.
    -   intros x x_in.
        rewrite not_not in x_in.
        exact x_in.
    -   intros x x_in.
        rewrite not_not.
        exact x_in.
Qed.

Theorem compl_empty : @complement U ∅ = all.
    apply antisym.
    -   intros x x_in.
        unfold all.
        trivial.
    -   intros x x_in contr.
        contradiction.
Qed.

Theorem compl_all : @complement U all = ∅.
    apply not_ex_empty.
    intros x x_in.
    contradiction x_in.
    unfold all; trivial.
Qed.

Theorem union_compl : ∀ A B : U → Prop,
        complement (A ∪ B) = complement A ∩ complement B.
    intros A B.
    unfold complement, union, intersection.
    apply antisym.
    -   intros x x_in.
        rewrite not_or in x_in.
        exact x_in.
    -   intros x x_in.
        rewrite not_or.
        exact x_in.
Qed.

Theorem inter_compl : ∀ A B : U → Prop,
        complement (A ∩ B) = complement A ∪ complement B.
    intros A B.
    unfold complement, union, intersection.
    apply antisym.
    -   intros x x_in.
        rewrite not_and in x_in.
        exact x_in.
    -   intros x x_in.
        rewrite not_and.
        exact x_in.
Qed.

Theorem compl_eq : ∀ A B : U → Prop, complement A = complement B → A = B.
    intros A B eq.
    apply predicate_ext; intros x; split; intros H1; classic_contradiction H2.
    -   assert (complement B x) as Bx by exact H2.
        rewrite <- eq in Bx.
        contradiction.
    -   assert (complement A x) as Ax by exact H2.
        rewrite eq in Ax.
        contradiction.
Qed.

(* begin hide *)
Global Instance set_minus_id : Id set_minus := {
    id := @empty U
}.
(* end hide *)
Lemma set_minus_rid : ∀ S : U → Prop, S - ∅ = S.
    intros S.
    apply antisym.
    -   intros x [Sx C].
        exact Sx.
    -   intros x Sx.
        split.
        +   exact Sx.
        +   apply not_in_empty.
Qed.

(* begin hide *)
Global Instance set_minus_rid_class : Rid set_minus := {
    rid := set_minus_rid
}.
(* end hide *)
Theorem set_minus_lid : ∀ S : U → Prop, ∅ - S = ∅.
    intros S.
    apply not_ex_empty.
    intros x [contr Sx].
    contradiction contr.
Qed.

(* begin hide *)
Global Instance set_minus_inv_class : Inv set_minus := {
    inv (S : U → Prop) := S
}.
(* end hide *)
Lemma set_minus_inv : ∀ S : U → Prop, S - S = ∅.
    intros S.
    apply not_ex_empty.
    intros x [Sx nSx].
    contradiction.
Qed.

(* begin hide *)
Global Instance set_minus_linv : Linv set_minus := {
    linv := set_minus_inv
}.
Global Instance set_minus_rinv : Rinv set_minus := {
    rinv := set_minus_inv
}.
(* end hide *)
Theorem set_minus_twice : ∀ S T : U → Prop, S - T - T = S - T.
    intros S T.
    apply antisym.
    -   intros x [[Sx Tx] Tx'].
        split; assumption.
    -   intros x [Sx Tx].
        split; [>split|]; assumption.
Qed.

Theorem symdif_formula : ∀ S T : U → Prop, S + T = (S ∪ T) - (S ∩ T).
    intros S T.
    unfold symmetric_difference.
    apply antisym.
    -   intros x [[Sx nTx]|[Tx nSx]].
        +   split.
            *   left; exact Sx.
            *   intros [C Tx]; contradiction.
        +   split.
            *   right; exact Tx.
            *   intros [Sx C]; contradiction.
    -   intros x [[Sx|Tx] nST];
            unfold intersection in nST;
            rewrite not_and in nST;
            destruct nST as [nSx|nTx].
        +   contradiction.
        +   left; split; assumption.
        +   right; split; assumption.
        +   contradiction.
Qed.

Lemma symdif_comm : ∀ S T : U → Prop, S + T = T + S.
    apply set_comm_base.
    intros S T x [[Sx nTx]|[Tx nSx]].
    -   right; split; assumption.
    -   left; split; assumption.
Qed.

(* begin hide *)
Global Instance symdif_comm_class : Comm symmetric_difference := {
    comm := symdif_comm
}.
(* end hide *)
Lemma symdif_assoc : ∀ R S T : U → Prop, R + (S + T) = (R + S) + T.
    apply set_assoc_base; try exact symdif_comm_class.
    intros R S T x x_in.
    destruct x_in as [[Rx nSTx]|[STx nRx]].
    -   unfold symmetric_difference, union in nSTx.
        unfold set_minus in nSTx.
        rewrite not_or in nSTx.
        do 2 rewrite not_and, not_not in nSTx.
        destruct nSTx as [[nSx|Tx] [nTx|Sx]]; try contradiction.
        +   left.
            split; try assumption.
            left.
            split; assumption.
        +   right.
            split; try assumption.
            unfold symmetric_difference, union, set_minus.
            rewrite not_or.
            do 2 rewrite not_and, not_not.
            split; right; assumption.
    -   destruct STx as [[Sx nTx]|[Tx nSx]].
        +   left.
            split; try assumption.
            right.
            split; assumption.
        +   right.
            split; try assumption.
            unfold symmetric_difference, union, set_minus.
            rewrite not_or.
            do 2 rewrite not_and, not_not.
            split; left; assumption.
Qed.

(* begin hide *)
Global Instance symdif_assoc_class : Assoc symmetric_difference := {
    assoc := symdif_assoc
}.

Global Instance symdif_id : Id symmetric_difference := {
    id := @empty U
}.
(* end hide *)
Lemma symdif_lid : ∀ S : U → Prop, ∅ + S = S.
    intros S.
    apply antisym.
    -   intros x [[x1 x2]|[x1 x2]].
        +   contradiction.
        +   exact x1.
    -   intros x x_in.
        right; split.
        +   exact x_in.
        +   apply not_in_empty.
Qed.

(* begin hide *)
Global Instance symdif_lid_class : Lid symmetric_difference := {
    lid := symdif_lid
}.

Global Instance symdif_inv : Inv symmetric_difference := {
    inv (S : U → Prop) := S
}.
(* end hide *)
Lemma symdif_linv : ∀ S : U → Prop, S + S = ∅.
    intros S.
    apply not_ex_empty.
    intros x x_in.
    destruct x_in; destruct H; contradiction.
Qed.
(* begin hide *)
Global Instance symdif_linv_class : Linv symmetric_difference := {
    linv := symdif_linv
}.

End SetBase.

Close Scope set_scope.
(* end hide *)
