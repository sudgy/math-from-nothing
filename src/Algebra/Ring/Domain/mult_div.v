Require Import init.

Require Export mult_ring.
Require Import relation.

Definition divides {U} `{Mult U} a b := ∃ c, c * a = b.
(** Note that this is the unicode symbol '∣', not '|'!  It is the LaTeX \mid.
The reason for this is that using the normal '|' causes issues with things like
pattern matching.
*)
Infix "∣" := divides (at level 50).

Definition unit {U} `{Mult U, One U} a := a ∣ 1.
Definition associates {U} `{Mult U} a b := a ∣ b ∧ b ∣ a.
Definition irreducible {U} `{Zero U, Mult U, One U} p
    := 0 ≠ p ∧ ¬unit p ∧ ∀ a b, ¬unit a → ¬unit b → p ≠ a * b.
Definition prime {U} `{Zero U, Mult U, One U} p
    := 0 ≠ p ∧ ¬unit p ∧ ∀ a b, p ∣ (a * b) → p ∣ a ∨ p ∣ b.

Definition even {U} `{Plus U, Mult U, One U} a := 2 ∣ a.
Definition odd {U} `{Plus U, Mult U, One U} a := ¬(2 ∣ a).

(* begin hide *)
Section Div.

Context {U} `{Up : Plus U,
                  @PlusAssoc U Up,
                  @PlusComm U Up,
              Uz : Zero U,
                  @PlusLid U Up Uz,
              Un : Neg U,
                  @PlusLinv U Up Uz Un,
              Um : Mult U,
                  @MultAssoc U Um,
                  @MultComm U Um,
                  @Ldist U Up Um,
                  @Rdist U Up Um,
                  @MultLanni U Uz Um,
                  @MultRanni U Uz Um,
              Uo : One U,
                  @MultLid U Um Uo,
                  @MultRid U Um Uo,
                  @MultLcancel U Uz Um,
                  @MultRcancel U Uz Um,
              Ul : Order U,
                  @Connex U le,
                  @Antisymmetric U le,
                  @Transitive U le
              }.

Lemma divides_refl : ∀ a, a ∣ a.
    intros a.
    exists 1.
    apply mult_lid.
Qed.
(* end hide *)
Global Instance divides_refl_class : Reflexive divides := {
    refl := divides_refl
}.

(* begin hide *)
Lemma divides_trans : ∀ a b c, a ∣ b → b ∣ c → a ∣ c.
    intros a b c [d eq1] [e eq2].
    exists (e * d).
    rewrite <- mult_assoc.
    rewrite eq1.
    rewrite eq2.
    reflexivity.
Qed.
(* end hide *)
Global Instance divides_trans_class : Transitive divides := {
    trans := divides_trans
}.

Theorem one_divides : ∀ n, 1 ∣ n.
    intros n.
    exists n.
    apply mult_rid.
Qed.

Theorem divides_zero : ∀ a, a ∣ 0.
    intros a.
    exists 0.
    apply mult_lanni.
Qed.

Theorem divides_neg : ∀ a b, a ∣ b → a ∣ -b.
    intros a b [c eq].
    exists (-c).
    rewrite mult_lneg.
    apply f_equal.
    exact eq.
Qed.

Theorem plus_stays_divides : ∀ p a b, p ∣ a → p ∣ b → p ∣ (a + b).
    intros p a b [c c_eq] [d d_eq].
    exists (c + d).
    rewrite <- c_eq, <- d_eq.
    apply rdist.
Qed.

Theorem plus_changes_divides : ∀ p a b,
                               p ∣ a → ¬(p ∣ b) → ¬(p ∣ (a + b)).
    intros p a b [c c_eq] not [d d_eq].
    rewrite <- c_eq in d_eq.
    apply lplus with (-(c * p)) in d_eq.
    rewrite plus_assoc, plus_linv, plus_lid in d_eq.
    rewrite <- mult_lneg in d_eq.
    rewrite <- rdist in d_eq.
    unfold divides in not.
    rewrite not_ex in not.
    specialize (not (-c + d)).
    contradiction.
Qed.

Theorem mult_factors_extend : ∀ p a b, p ∣ a → p ∣ a * b.
    intros p a b [c eq].
    exists (b * c).
    rewrite (mult_comm a).
    rewrite <- eq.
    symmetry; apply mult_assoc.
Qed.

Theorem mult_factors_back : ∀ a b c, a * b = c → a ∣ c ∧ b ∣ c.
    intros a b c eq.
    split.
    -   exists b.
        rewrite mult_comm.
        exact eq.
    -   exists a.
        exact eq.
Qed.

Theorem mult_div_lself : ∀ a b, a ∣ a * b.
    intros a b.
    exists b.
    apply mult_comm.
Qed.

Theorem mult_div_rself : ∀ a b, a ∣ b * a.
    intros a b.
    exists b.
    reflexivity.
Qed.

Theorem div_rcancel : ∀ a b c, 0 ≠ c → a * c ∣ b * c → a ∣ b.
    intros a b c c_nz [x eq].
    exists x.
    rewrite mult_assoc in eq.
    apply mult_rcancel in eq; [>|exact c_nz].
    exact eq.
Qed.

Theorem div_lcancel : ∀ a b c, 0 ≠ a → a * b ∣ a * c → b ∣ c.
    intros a b c a_nz.
    do 2 rewrite (mult_comm a).
    apply div_rcancel.
    exact a_nz.
Qed.

Theorem div_mult_unit : ∀ a b, 0 ≠ a → a * b ∣ a → unit b.
    intros a b a_nz eq.
    destruct eq as [c eq].
    exists c.
    rewrite (mult_comm a b) in eq.
    rewrite mult_assoc in eq.
    rewrite <- (mult_lid a) in eq at 2.
    apply mult_rcancel in eq; [>|exact a_nz].
    exact eq.
Qed.

Theorem prime_irreducible : ∀ p, prime p → irreducible p.
    intros p [p_nz [p_nu p_prime]].
    repeat split; [>exact p_nz|exact p_nu|].
    intros a b a_nu b_nu.
    intros contr.
    subst p.
    assert (0 ≠ a) as a_nz.
    {
        intros contr.
        subst a.
        rewrite mult_lanni in p_nz.
        contradiction.
    }
    assert (0 ≠ b) as b_nz.
    {
        intros contr.
        subst b.
        rewrite mult_ranni in p_nz.
        contradiction.
    }
    specialize (p_prime a b (refl (a * b))) as [d1|d2].
    -   apply div_mult_unit in d1; [>|exact a_nz].
        contradiction.
    -   rewrite mult_comm in d2.
        apply div_mult_unit in d2; [>|exact b_nz].
        contradiction.
Qed.

(* begin hide *)
End Div.
(* end hide *)
