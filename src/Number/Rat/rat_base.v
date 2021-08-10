Require Import init.

Require Import nat1.
Require Import int.
Require Import set.

Declare Scope rat_scope.
Delimit Scope rat_scope with rat.

(* begin hide *)
Section RatEquiv.
(* end hide *)
Let rat_eq (a b : int * nat1) :=
    fst a * nat1_to_int (snd b) = fst b * nat1_to_int (snd a).
Local Infix "~" := rat_eq.

(* begin hide *)
Lemma rat_eq_reflexive : ∀ a, a ~ a.
    intros [a1 a2].
    unfold rat_eq; cbn.
    reflexivity.
Qed.
Instance rat_eq_reflexive_class : Reflexive _ := {
    refl := rat_eq_reflexive
}.

Lemma rat_eq_symmetric : ∀ a b, a ~ b → b ~ a.
    intros [a1 a2] [b1 b2] ab.
    unfold rat_eq in *; cbn in *.
    symmetry.
    exact ab.
Qed.
Instance rat_eq_symmetric_class : Symmetric _ := {
    sym := rat_eq_symmetric
}.

Lemma rat_eq_transitive : ∀ a b c, a ~ b → b ~ c → a ~ c.
    intros [a1 a2] [b1 b2] [c1 c2] ab bc.
    unfold rat_eq in *; cbn in *.
    classic_case (0 = b1) as [bz|bnz].
    -   subst.
        rewrite mult_lanni in bc.
        rewrite mult_lanni in ab.
        symmetry in ab.
        apply int_mult_0 in ab as [ab|ab].
        +   apply int_mult_0 in bc as [bc|bc].
            *   subst.
                do 2 rewrite mult_lanni.
                reflexivity.
            *   contradiction (nat1_nz_int _ bc).
        +   contradiction (nat1_nz_int _ ab).
    -   pose proof (lrmult ab bc) as eq; clear ab bc.
        pose proof (nat1_nz_int b2) as nz.
        mult_cancel_left (nat1_to_int b2) in eq; try exact nz.
        mult_cancel_left b1 in eq; try exact bnz.
        rewrite (mult_comm c1).
        exact eq.
Qed.
Instance rat_eq_transitive_class : Transitive _ := {
    trans := rat_eq_transitive
}.

End RatEquiv.
(* end hide *)
Definition rat_equiv := make_equiv _
    rat_eq_reflexive_class rat_eq_symmetric_class rat_eq_transitive_class.
Notation "a ~ b" := (eq_equal rat_equiv a b) : rat_scope.

Notation "'rat'" := (equiv_type rat_equiv).

Definition int_to_rat a := to_equiv_type rat_equiv (a, 1).
Definition nat0_to_rat a := int_to_rat (nat0_to_int a).
Definition nat1_to_rat a := int_to_rat (nat1_to_int a).

Theorem int_to_rat_eq : ∀ a b, int_to_rat a = int_to_rat b → a = b.
    intros a b eq.
    unfold int_to_rat in eq.
    equiv_simpl in eq.
    rewrite nat1_to_int_one in eq.
    do 2 rewrite mult_rid in eq.
    exact eq.
Qed.

Theorem nat0_to_rat_eq : ∀ a b, nat0_to_rat a = nat0_to_rat b → a = b.
    intros a b eq.
    apply nat0_to_int_eq.
    apply int_to_rat_eq.
    exact eq.
Qed.

Theorem nat1_to_rat_eq : ∀ a b, nat1_to_rat a = nat1_to_rat b → a = b.
    intros a b eq.
    apply nat1_to_int_eq.
    apply int_to_rat_eq.
    exact eq.
Qed.
