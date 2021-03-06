Require Import init.

Require Export relation.
Require Export plus_group.

Class OrderLplus U `{Plus U, Order U} := {
    le_lplus : ∀ {a b} c, a <= b → c + a <= c + b
}.
Class OrderRplus U `{Plus U, Order U} := {
    le_rplus : ∀ {a b} c, a <= b → a + c <= b + c
}.
Class OrderPlusLcancel U `{Plus U, Order U} := {
    le_plus_lcancel : ∀ {a b} c, c + a <= c + b → a <= b
}.
Class OrderPlusRcancel U `{Plus U, Order U} := {
    le_plus_rcancel : ∀ {a b} c, a + c <= b + c → a <= b
}.

(* begin hide *)
Section OrderPlusImply.

Context {U} `{
    p : Plus U,
    @PlusAssoc U p,
    @PlusComm U p,
    z : Zero U,
    @PlusLid U p z,
    @PlusRid U p z,
    n : Neg U,
    @PlusLinv U p z n,
    @PlusRinv U p z n,
    o : Order U,
    @OrderLplus U p o,
    @OrderRplus U p o,
    @OrderPlusLcancel U p o
}.

Lemma le_lplus_rplus_ : ∀ a b c, a <= b → a + c <= b + c.
    intros a b c eq.
    do 2 rewrite (plus_comm _ c).
    apply le_lplus.
    exact eq.
Qed.

Lemma le_plus_lcancel_rcancel_ : ∀ a b c, a + c <= b + c → a <= b.
    intros a b c eq.
    do 2 rewrite (plus_comm _ c) in eq.
    apply le_plus_lcancel in eq.
    exact eq.
Qed.

Lemma le_plus_linv_lcancel : ∀ a b c, c + a <= c + b → a <= b.
    intros a b c eq.
    apply le_lplus with (-c) in eq.
    do 2 rewrite plus_assoc in eq.
    rewrite plus_linv in eq.
    do 2 rewrite plus_lid in eq.
    exact eq.
Qed.
Lemma le_plus_rinv_rcancel : ∀ a b c, a + c <= b + c → a <= b.
    intros a b c eq.
    apply le_rplus with (-c) in eq.
    do 2 rewrite <- plus_assoc in eq.
    rewrite plus_rinv in eq.
    do 2 rewrite plus_rid in eq.
    exact eq.
Qed.

Global Instance le_lplus_rplus : OrderRplus U := {
    le_rplus := le_lplus_rplus_
}.

Global Instance le_lcancel_rcancel : OrderPlusRcancel U := {
    le_plus_rcancel := le_plus_lcancel_rcancel_
}.

Global Instance le_plus_linv_lcancel_class : OrderPlusLcancel U := {
    le_plus_lcancel := le_plus_linv_lcancel
}.
Global Instance le_plus_rinv_rcancel_class : OrderPlusRcancel U := {
    le_plus_rcancel := le_plus_rinv_rcancel
}.

End OrderPlusImply.


Section OrderPlus.

Context {U} `{
    p : Plus U,
    @PlusAssoc U p,
    @PlusComm U p,
    z : Zero U,
    @PlusLid U p z,
    @PlusRid U p z,
    @PlusLcancel U p,
    @PlusRcancel U p,
    n : Neg U,
    @PlusLinv U p z n,
    @PlusRinv U p z n,

    o : Order U,
    Connex U le,
    Antisymmetric U le,
    Transitive U le,
    Reflexive U le,
    @OrderLplus U p o,
    @OrderRplus U p o,
    @OrderPlusLcancel U p o,
    @OrderPlusRcancel U p o
}.
(* end hide *)
Theorem le_lrplus : ∀ {a b c d}, a <= b → c <= d → a + c <= b + d.
    intros a b c d ab cd.
    apply le_rplus with c in ab.
    apply le_lplus with b in cd.
    exact (trans ab cd).
Qed.

Theorem lt_lplus : ∀ {a b} c, a < b → c + a < c + b.
    intros a b c [leq neq].
    split.
    -   apply le_lplus.
        exact leq.
    -   intro contr.
        apply plus_lcancel in contr.
        contradiction.
Qed.

Theorem lt_rplus : ∀ {a b} c, a < b → a + c < b + c.
    intros a b c [leq neq].
    split.
    -   apply le_rplus.
        exact leq.
    -   intro contr.
        apply plus_rcancel in contr.
        contradiction.
Qed.

Theorem lt_lrplus : ∀ {a b c d}, a < b → c < d → a + c < b + d.
    intros a b c d ab cd.
    apply lt_rplus with c in ab.
    apply lt_lplus with b in cd.
    exact (trans ab cd).
Qed.

Theorem le_lt_lrplus : ∀ {a b c d}, a <= b → c < d → a + c < b + d.
    intros a b c d ab cd.
    apply le_rplus with c in ab.
    apply lt_lplus with b in cd.
    exact (le_lt_trans ab cd).
Qed.

Theorem lt_le_lrplus : ∀ {a b c d}, a < b → c <= d → a + c < b + d.
    intros a b c d ab cd.
    apply lt_rplus with c in ab.
    apply le_lplus with b in cd.
    exact (lt_le_trans ab cd).
Qed.

Theorem lt_plus_lcancel : ∀ {a b} c, c + a < c + b → a < b.
    intros a b c [leq neq].
    split.
    -   apply le_plus_lcancel in leq.
        exact leq.
    -   intro contr.
        rewrite contr in neq.
        contradiction.
Qed.

Theorem lt_plus_rcancel : ∀ {a b} c, a + c < b + c → a < b.
    intros a b c [leq neq].
    split.
    -   apply le_plus_rcancel in leq.
        exact leq.
    -   intro contr.
        rewrite contr in neq.
        contradiction.
Qed.

Theorem neg_pos : ∀ a, a <= 0 → 0 <= -a.
    intros a a_pos.
    apply le_rplus with (-a) in a_pos.
    rewrite plus_rinv, plus_lid in a_pos.
    exact a_pos.
Qed.
Theorem neg_pos2 : ∀ a, a < 0 → 0 < -a.
    intros a a_pos.
    apply lt_rplus with (-a) in a_pos.
    rewrite plus_rinv, plus_lid in a_pos.
    exact a_pos.
Qed.

Theorem pos_neg : ∀ a, 0 <= a → -a <= 0.
    intros a a_pos.
    apply le_rplus with (-a) in a_pos.
    rewrite plus_rinv, plus_lid in a_pos.
    exact a_pos.
Qed.
Theorem pos_neg2 : ∀ a, 0 < a → -a < 0.
    intros a a_pos.
    apply lt_rplus with (-a) in a_pos.
    rewrite plus_rinv, plus_lid in a_pos.
    exact a_pos.
Qed.

Theorem le_plus_llmove : ∀ a b c, a + b <= c ↔ b <= -a + c.
    intros a b c.
    split; intros eq.
    -   apply le_lplus with (-a) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply le_lplus with a in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem le_plus_lrmove : ∀ a b c, a + b <= c ↔ a <= c - b.
    intros a b c.
    split; intros eq.
    -   apply le_rplus with (-b) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply le_rplus with b in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.
Theorem le_plus_rlmove : ∀ a b c, a <= b + c ↔ -b + a <= c.
    intros a b c.
    split; intros eq.
    -   apply le_lplus with (-b) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply le_lplus with b in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem le_plus_rrmove : ∀ a b c, a <= b + c ↔ a - c <= b.
    intros a b c.
    split; intros eq.
    -   apply le_rplus with (-c) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply le_rplus with c in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.

Theorem le_plus_0_ab_na_b : ∀ a b, 0 <= a + b ↔ -a <= b.
    intros a b.
    rewrite le_plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem le_plus_0_ab_nb_a : ∀ a b, 0 <= a + b ↔ -b <= a.
    intros a b.
    rewrite le_plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem le_plus_ab_0_a_nb : ∀ a b, a + b <= 0 ↔ a <= -b.
    intros a b.
    rewrite le_plus_lrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem le_plus_ab_0_b_na : ∀ a b, a + b <= 0 ↔ b <= -a.
    intros a b.
    rewrite le_plus_llmove.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem le_plus_a_0_ab_b : ∀ a b, a <= 0 ↔ a + b <= b.
    intros a b.
    rewrite le_plus_lrmove.
    rewrite plus_rinv.
    reflexivity.
Qed.
Theorem le_plus_a_0_ba_b : ∀ a b, a <= 0 ↔ b + a <= b.
    intros a b.
    rewrite le_plus_llmove.
    rewrite plus_linv.
    reflexivity.
Qed.
Theorem le_plus_0_a_b_ab : ∀ a b, 0 <= a ↔ b <= a + b.
    intros a b.
    rewrite le_plus_rrmove.
    rewrite plus_rinv.
    reflexivity.
Qed.
Theorem le_plus_0_a_b_ba : ∀ a b, 0 <= a ↔ b <= b + a.
    intros a b.
    rewrite le_plus_rlmove.
    rewrite plus_linv.
    reflexivity.
Qed.

Theorem le_plus_0_nab_a_b : ∀ a b, 0 <= -a + b ↔ a <= b.
    intros a b.
    rewrite <- le_plus_llmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem le_plus_anb_0_a_b : ∀ a b, a - b <= 0 ↔ a <= b.
    intros a b.
    rewrite <- le_plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem le_plus_nab_0_b_a : ∀ a b, -a + b <= 0 ↔ b <= a.
    intros a b.
    rewrite <- le_plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem le_plus_0_anb_b_a : ∀ a b, 0 <= a - b ↔ b <= a.
    intros a b.
    rewrite <- le_plus_lrmove.
    rewrite plus_lid.
    reflexivity.
Qed.

Theorem lt_plus_llmove : ∀ a b c, a + b < c ↔ b < -a + c.
    intros a b c.
    split; intros eq.
    -   apply lt_lplus with (-a) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply lt_lplus with a in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem lt_plus_lrmove : ∀ a b c, a + b < c ↔ a < c - b.
    intros a b c.
    split; intros eq.
    -   apply lt_rplus with (-b) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply lt_rplus with b in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.
Theorem lt_plus_rlmove : ∀ a b c, a < b + c ↔ -b + a < c.
    intros a b c.
    split; intros eq.
    -   apply lt_lplus with (-b) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply lt_lplus with b in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem lt_plus_rrmove : ∀ a b c, a < b + c ↔ a - c < b.
    intros a b c.
    split; intros eq.
    -   apply lt_rplus with (-c) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply lt_rplus with c in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.

Theorem lt_plus_0_ab_na_b : ∀ a b, 0 < a + b ↔ -a < b.
    intros a b.
    rewrite lt_plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem lt_plus_0_ab_nb_a : ∀ a b, 0 < a + b ↔ -b < a.
    intros a b.
    rewrite lt_plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem lt_plus_ab_0_a_nb : ∀ a b, a + b < 0 ↔ a < -b.
    intros a b.
    rewrite lt_plus_lrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem lt_plus_ab_0_b_na : ∀ a b, a + b < 0 ↔ b < -a.
    intros a b.
    rewrite lt_plus_llmove.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem lt_plus_a_0_ab_b : ∀ a b, a < 0 ↔ a + b < b.
    intros a b.
    rewrite lt_plus_lrmove.
    rewrite plus_rinv.
    reflexivity.
Qed.
Theorem lt_plus_a_0_ba_b : ∀ a b, a < 0 ↔ b + a < b.
    intros a b.
    rewrite lt_plus_llmove.
    rewrite plus_linv.
    reflexivity.
Qed.
Theorem lt_plus_0_a_b_ab : ∀ a b, 0 < a ↔ b < a + b.
    intros a b.
    rewrite lt_plus_rrmove.
    rewrite plus_rinv.
    reflexivity.
Qed.
Theorem lt_plus_0_a_b_ba : ∀ a b, 0 < a ↔ b < b + a.
    intros a b.
    rewrite lt_plus_rlmove.
    rewrite plus_linv.
    reflexivity.
Qed.

Theorem lt_plus_0_nab_a_b : ∀ a b, 0 < -a + b ↔ a < b.
    intros a b.
    rewrite <- lt_plus_llmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem lt_plus_anb_0_a_b : ∀ a b, a - b < 0 ↔ a < b.
    intros a b.
    rewrite <- lt_plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem lt_plus_nab_0_b_a : ∀ a b, -a + b < 0 ↔ b < a.
    intros a b.
    rewrite <- lt_plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem lt_plus_0_anb_b_a : ∀ a b, 0 < a - b ↔ b < a.
    intros a b.
    rewrite <- lt_plus_lrmove.
    rewrite plus_lid.
    reflexivity.
Qed.

Theorem le_neg : ∀ a b, a <= b ↔ -b <= -a.
    intros a b.
    rewrite <- le_plus_0_anb_b_a.
    rewrite le_plus_0_ab_na_b.
    reflexivity.
Qed.
Theorem lt_neg : ∀ a b, a < b ↔ -b < -a.
    intros a b.
    rewrite <- lt_plus_0_anb_b_a.
    rewrite lt_plus_0_ab_na_b.
    reflexivity.
Qed.
(* begin hide *)
End OrderPlus.
(* end hide *)
