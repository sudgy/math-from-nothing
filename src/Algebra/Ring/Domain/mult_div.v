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

Section Div.

Context {U} `{AllMultClass U}.

Global Instance divides_refl : Reflexive divides.
Proof.
    split.
    intros a.
    exists 1.
    apply mult_lid.
Qed.

Global Instance divides_trans : Transitive divides.
Proof.
    split.
    intros a b c [d eq1] [e eq2].
    exists (e * d).
    rewrite <- mult_assoc.
    rewrite eq1.
    exact eq2.
Qed.

Theorem one_divides : ∀ n, 1 ∣ n.
Proof.
    intros n.
    exists n.
    apply mult_rid.
Qed.

Theorem divides_zero : ∀ a, a ∣ 0.
Proof.
    intros a.
    exists 0.
    apply mult_lanni.
Qed.

Theorem divides_neg : ∀ a b, a ∣ b → a ∣ -b.
Proof.
    intros a b [c eq].
    exists (-c).
    rewrite mult_lneg.
    apply f_equal.
    exact eq.
Qed.

Theorem plus_stays_divides : ∀ p a b, p ∣ a → p ∣ b → p ∣ (a + b).
Proof.
    intros p a b [c c_eq] [d d_eq].
    exists (c + d).
    rewrite <- c_eq, <- d_eq.
    apply rdist.
Qed.

Theorem plus_divides_back : ∀ p a b, p ∣ a → p ∣ (a + b) → p ∣ b.
Proof.
    intros p a b [c c_eq] [d d_eq].
    exists (-c + d).
    rewrite rdist.
    rewrite mult_lneg.
    rewrite c_eq, d_eq.
    apply plus_llinv.
Qed.

Theorem mult_factors_extend : ∀ p a b, p ∣ a → p ∣ a * b.
Proof.
    intros p a b [c eq].
    exists (b * c).
    rewrite <- mult_assoc.
    rewrite eq.
    apply mult_comm.
Qed.

Theorem mult_factors_back : ∀ a b c, a * b = c → a ∣ c ∧ b ∣ c.
Proof.
    intros a b c eq.
    split.
    -   exists b.
        rewrite mult_comm.
        exact eq.
    -   exists a.
        exact eq.
Qed.

Theorem mult_div_lself : ∀ a b, a ∣ a * b.
Proof.
    intros a b.
    exists b.
    apply mult_comm.
Qed.

Theorem mult_div_rself : ∀ a b, a ∣ b * a.
Proof.
    intros a b.
    exists b.
    reflexivity.
Qed.

Theorem div_rcancel : ∀ a b c, 0 ≠ c → a * c ∣ b * c → a ∣ b.
Proof.
    intros a b c c_nz [x eq].
    exists x.
    rewrite mult_assoc in eq.
    apply mult_rcancel in eq; [>|exact c_nz].
    exact eq.
Qed.

Theorem div_lcancel : ∀ a b c, 0 ≠ a → a * b ∣ a * c → b ∣ c.
Proof.
    intros a b c a_nz.
    do 2 rewrite (mult_comm a).
    apply div_rcancel.
    exact a_nz.
Qed.

Theorem unit_div : ∀ a b, unit a → a ∣ b.
Proof.
    intros a b [c a_eq].
    exists (b * c).
    rewrite <- mult_assoc.
    rewrite a_eq.
    apply mult_rid.
Qed.

Theorem div_zero : ∀ a, 0 ∣ a → 0 = a.
Proof.
    intros a [b b_eq].
    rewrite mult_ranni in b_eq.
    exact b_eq.
Qed.

Theorem one_unit : unit 1.
Proof.
    exists 1.
    apply mult_lid.
Qed.

Theorem zero_not_unit : ¬unit 0.
Proof.
    intros [a eq].
    rewrite mult_ranni in eq.
    contradiction (not_trivial_one eq).
Qed.

Theorem unit_mult : ∀ a b, unit a → unit b → unit (a * b).
Proof.
    intros a b [c a_eq] [d b_eq].
    exists (d * c).
    rewrite <- mult_assoc.
    rewrite (mult_assoc c).
    rewrite a_eq.
    rewrite mult_lid.
    exact b_eq.
Qed.

Theorem div_mult_unit : ∀ a b, 0 ≠ a → a * b ∣ a → unit b.
Proof.
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
Proof.
    intros p [p_nz [p_nu p_prime]].
    split; [>exact p_nz|].
    split; [>exact p_nu|].
    intros a b a_nu b_nu.
    intros contr.
    subst p.
    apply nz_mult in p_nz as [a_nz b_nz].
    specialize (p_prime a b (refl (a * b))) as [d1|d2].
    -   apply (div_mult_unit _ _ a_nz) in d1.
        contradiction.
    -   rewrite mult_comm in d2.
        apply (div_mult_unit _ _ b_nz) in d2.
        contradiction.
Qed.

Global Instance associates_refl : Reflexive associates.
Proof.
    split.
    intros a.
    split; apply refl.
Qed.

Global Instance associates_sym : Symmetric associates.
Proof.
    split.
    intros a b [ab ba].
    split; assumption.
Qed.

Global Instance associates_trans : Transitive associates.
Proof.
    split.
    intros a b c [ab ba] [bc cb].
    split.
    -   exact (trans ab bc).
    -   exact (trans cb ba).
Qed.

Theorem unit_associates : ∀ a b, unit a → unit b → associates a b.
Proof.
    intros a b a_unit b_unit.
    split.
    -   apply (unit_div _ _ a_unit).
    -   apply (unit_div _ _ b_unit).
Qed.

Theorem associates_zero : ∀ a, associates 0 a → 0 = a.
Proof.
    intros a [div1 div2].
    apply div_zero.
    exact div1.
Qed.

Theorem associates_unit : ∀ a b, associates a b → ∃ c, unit c ∧ c * a = b.
Proof.
    intros a b [[c c_eq] [d d_eq]].
    classic_case (0 = b) as [b_z|b_nz].
    -   destruct b_z.
        exists 1.
        split; [>exact one_unit|].
        rewrite mult_lid.
        rewrite mult_ranni in d_eq.
        symmetry; exact d_eq.
    -   exists c.
        split; [>|exact c_eq].
        rewrite <- d_eq in c_eq.
        rewrite mult_assoc in c_eq.
        rewrite <- (mult_lid b) in c_eq at 2.
        apply (mult_rcancel _ b_nz) in c_eq.
        exists d.
        rewrite mult_comm.
        exact c_eq.
Qed.

End Div.
