Require Import init.

Require Export mult_ring.
Require Export relation.
Require Export set.

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

Theorem div_lmult : ∀ {a b} c, a ∣ b → c * a ∣ c * b.
Proof.
    intros a b c [d eq].
    exists d.
    rewrite (mult_comm c a), mult_assoc.
    rewrite eq.
    apply mult_comm.
Qed.

Theorem div_rmult : ∀ {a b} c, a ∣ b → a * c ∣ b * c.
Proof.
    intros a b c.
    do 2 rewrite (mult_comm _ c).
    apply div_lmult.
Qed.

Theorem div_lrmult : ∀ {a b c d}, a ∣ b → c ∣ d → a * c ∣ b * d.
Proof.
    intros a b c d ab cd.
    apply (div_lmult b) in cd.
    apply (div_rmult c) in ab.
    exact (trans ab cd).
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

Theorem unit_nz : ∀ a, unit a → 0 ≠ a.
Proof.
    intros a a_uni contr.
    subst a.
    contradiction (zero_not_unit a_uni).
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

Theorem lmult_unit : ∀ a b, unit (a * b) → unit a.
Proof.
    intros a b.
    unfold unit.
    intros [c c_eq].
    exists (c * b).
    rewrite (mult_comm a b), mult_assoc in c_eq.
    exact c_eq.
Qed.

Theorem rmult_unit : ∀ a b, unit (a * b) → unit b.
Proof.
    intros a b.
    rewrite mult_comm.
    apply lmult_unit.
Qed.

Theorem div_unit_mult : ∀ a b c, unit a → b ∣ c → a * b ∣ c.
Proof.
    intros a b c [a' a_eq] [d d_eq].
    exists (d * a').
    rewrite mult_assoc, <- (mult_assoc d).
    rewrite a_eq, mult_rid.
    exact d_eq.
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

Theorem unit_ex : ∀ a, unit a → ∃ b, unit b ∧ b * a = 1.
Proof.
    intros a [b eq].
    exists b.
    split; [>|exact eq].
    exists a.
    rewrite mult_comm.
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

Theorem nz_unit : ∀ a b, unit a → 0 ≠ b → 0 ≠ a * b.
Proof.
    intros a b a_uni b_nz.
    apply mult_nz.
    -   apply unit_nz.
        exact a_uni.
    -   exact b_nz.
Qed.

Theorem not_unit_mult : ∀ a b, ¬unit b → ¬unit (a * b).
Proof.
    intros a b b_nuni ab_uni.
    apply rmult_unit in ab_uni.
    contradiction.
Qed.

Theorem irreducible_unit : ∀ a b, unit a → irreducible b → irreducible (a * b).
Proof.
    intros a b a_uni [b_nz [b_nuni b_irr]].
    split; [>|split].
    1: exact (nz_unit _ _ a_uni b_nz).
    1: exact (not_unit_mult _ _ b_nuni).
    intros x y x_nuni y_nuni.
    apply unit_ex in a_uni as [c [c_uni ca]].
    specialize (b_irr _ _ (not_unit_mult c x x_nuni) y_nuni).
    intros contr.
    apply (lmult c) in contr.
    do 2 rewrite mult_assoc in contr.
    rewrite ca, mult_lid in contr.
    contradiction.
Qed.

Theorem prime_unit : ∀ a b, unit a → prime b → prime (a * b).
Proof.
    intros a b a_uni [b_nz [b_nuni b_prime]].
    split; [>|split].
    1: exact (nz_unit _ _ a_uni b_nz).
    1: exact (not_unit_mult _ _ b_nuni).
    intros x y div.
    pose proof (unit_ex _ a_uni) as [c [c_uni ca]].
    apply (div_lmult c) in div.
    do 2 rewrite mult_assoc in div.
    rewrite ca, mult_lid in div.
    specialize (b_prime _ _ div).
    destruct b_prime as [b_prime|b_prime].
    -   left.
        apply (div_lmult a) in b_prime.
        rewrite mult_assoc in b_prime.
        rewrite (mult_comm a c) in b_prime.
        rewrite ca, mult_lid in b_prime.
        exact b_prime.
    -   right.
        apply div_unit_mult; assumption.
Qed.

Theorem prime_back : ∀ a b c, prime b → a ∣ b * c → ¬(b ∣ a) → a ∣ c.
Proof.
    intros a b c b_prime [d eq] ba.
    assert (b ∣ d * a) as bda.
    {
        exists c.
        rewrite mult_comm.
        symmetry; exact eq.
    }
    apply b_prime in bda as [bd|ba'].
    2: contradiction.
    destruct bd as [e e_eq].
    subst d.
    rewrite (mult_comm e b) in eq.
    rewrite <- mult_assoc in eq.
    apply mult_lcancel in eq; [>|apply b_prime].
    exists e.
    exact eq.
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

Theorem associates_one : ∀ a, associates a 1 ↔ unit a.
Proof.
    intros a.
    split.
    -   intro a_assoc.
        apply a_assoc.
    -   intros a_uni.
        split.
        +   exact a_uni.
        +   apply one_divides.
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

Definition div_equiv := make_equiv associates _ _ _.
Notation "'div_type'" := (equiv_type div_equiv).
Definition to_div := to_equiv div_equiv : U → div_type.
Local Infix "~" := (eq_equal div_equiv).

Lemma div_mult_wd : ∀ a b c d, a ~ b → c ~ d → a * c ~ b * d.
Proof.
    intros a b c d [ab ba] [cd dc].
    split.
    -   apply (div_rmult c) in ab.
        apply (div_lmult b) in cd.
        exact (trans ab cd).
    -   apply (div_rmult d) in ba.
        apply (div_lmult a) in dc.
        exact (trans ba dc).
Qed.

Global Instance div_zero_class : Zero div_type := {
    zero := to_div 0
}.

Global Instance div_one_class : One div_type := {
    one := to_div 1
}.

Global Instance div_mult_class : Mult div_type := {
    mult := binary_op (binary_self_wd div_mult_wd)
}.

Global Instance div_mult_comm : MultComm div_type.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold mult; equiv_simpl.
    rewrite mult_comm.
    apply refl.
Qed.

Global Instance div_mult_assoc : MultAssoc div_type.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold mult; equiv_simpl.
    rewrite mult_assoc.
    apply refl.
Qed.

Global Instance div_mult_lid : MultLid div_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold one, mult; equiv_simpl.
    rewrite mult_lid.
    apply refl.
Qed.

Global Instance div_mult_lanni : MultLanni div_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold zero, mult; equiv_simpl.
    rewrite mult_lanni.
    apply refl.
Qed.

Global Instance div_mult_lcancel : MultLcancel div_type.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold mult, zero; equiv_simpl.
    intros c_nz_base [eq1 eq2].
    assert (0 ≠ c) as c_nz.
    {
        intros contr; subst c.
        apply c_nz_base.
        apply refl.
    }
    split.
    -   exact (div_lcancel _ _ _ c_nz eq1).
    -   exact (div_lcancel _ _ _ c_nz eq2).
Qed.

#[refine]
Global Instance div_not_trivial : NotTrivial div_type := {
    not_trivial_a := to_div 0;
    not_trivial_b := to_div 1;
}.
Proof.
    equiv_simpl.
    intros contr.
    apply associates_zero in contr.
    contradiction (not_trivial_one contr).
Qed.

Global Instance to_div_zero : HomomorphismZero to_div.
Proof.
    split; reflexivity.
Qed.

Global Instance to_div_one : HomomorphismOne to_div.
Proof.
    split; reflexivity.
Qed.

Global Instance to_div_mult : HomomorphismMult to_div.
Proof.
    split.
    intros a b.
    unfold mult at 2; equiv_simpl.
    apply refl.
Qed.

Global Instance to_div_suc : Surjective to_div.
Proof.
    split.
    intros y.
    equiv_get_value y.
    exists y.
    reflexivity.
Qed.

Theorem div_equiv_div : ∀ a b, a ∣ b ↔ to_div a ∣ to_div b.
Proof.
    intros a b.
    split.
    -   intros [c eq].
        exists (to_div c).
        rewrite <- homo_mult.
        rewrite eq.
        reflexivity.
    -   intros [c' eq].
        pose proof (sur to_div c') as [c c_eq]; subst c'.
        rewrite <- homo_mult in eq.
        equiv_simpl in eq.
        apply associates_unit in eq as [d [d_uni d_eq]].
        exists (d * c).
        rewrite mult_assoc in d_eq.
        exact d_eq.
Qed.

Theorem div_equiv_unit : ∀ a : div_type, unit a ↔ a = 1.
Proof.
    intros a.
    split; [>|intro; subst; exists 1; apply mult_lid].
    intros a_uni.
    unfold unit in a_uni.
    pose proof (sur to_div a) as [b b_eq]; subst a.
    rewrite <- homo_one in a_uni.
    apply div_equiv_div in a_uni.
    unfold one; equiv_simpl.
    rewrite associates_one.
    exact a_uni.
Qed.

Theorem div_equiv_unit2 : ∀ a, unit a ↔ unit (to_div a).
Proof.
    intros a.
    apply div_equiv_div.
Qed.

Theorem div_equiv_zero : ∀ a, 0 = a ↔ 0 = to_div a.
Proof.
    intros a.
    split.
    -   intro; subst; reflexivity.
    -   unfold zero at 1; equiv_simpl.
        intros a0.
        apply div_zero.
        apply a0.
Qed.

Theorem div_equiv_irreducible : ∀ a, irreducible a ↔ irreducible (to_div a).
Proof.
    intros a.
    unfold irreducible.
    rewrite <- div_equiv_zero.
    rewrite <- div_equiv_unit2.
    do 2 apply iff_land.
    split.
    -   intros a_irr c' d' c_nuni d_nuni.
        pose proof (sur to_div c') as [c c_eq]; subst c'.
        pose proof (sur to_div d') as [d d_eq]; subst d'.
        rewrite <- div_equiv_unit2 in c_nuni, d_nuni.
        unfold mult; equiv_simpl.
        intros contr.
        apply sym in contr.
        apply associates_unit in contr as [u [u_uni u_eq]].
        symmetry in u_eq.
        rewrite mult_assoc in u_eq.
        contradiction (a_irr _ _ (not_unit_mult u c c_nuni) d_nuni u_eq).
    -   intros a_irr c d c_nuni d_nuni.
        rewrite div_equiv_unit2 in c_nuni, d_nuni.
        specialize (a_irr (to_div c) (to_div d) c_nuni d_nuni).
        intros contr; subst a.
        rewrite <- homo_mult in a_irr.
        contradiction.
Qed.

Theorem div_equiv_prime : ∀ a, prime a ↔ prime (to_div a).
Proof.
    intros a.
    unfold prime.
    rewrite <- div_equiv_zero.
    rewrite <- div_equiv_unit2.
    do 2 apply iff_land.
    split.
    -   intros a_prime.
        intros c' d' div.
        pose proof (sur to_div c') as [c c_eq]; subst c'.
        pose proof (sur to_div d') as [d d_eq]; subst d'.
        rewrite <- homo_mult in div.
        do 2 rewrite <- div_equiv_div.
        rewrite <- div_equiv_div in div.
        exact (a_prime c d div).
    -   intros a_prime c d cd.
        rewrite div_equiv_div in cd.
        rewrite homo_mult in cd.
        specialize (a_prime _ _ cd).
        do 2 rewrite <- div_equiv_div in a_prime.
        exact a_prime.
Qed.

Theorem div_unit_eq : ∀ a x, unit a → to_div (a * x) = to_div x.
Proof.
    intros a x [b ab].
    equiv_simpl.
    split.
    -   exists b.
        rewrite mult_assoc, ab.
        apply mult_lid.
    -   apply mult_div_rself.
Qed.

End Div.

Notation "'div_type' U" := (equiv_type (div_equiv (U := U))) (at level 200).
