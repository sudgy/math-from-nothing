Require Import init.

Class Assoc {U} (op : U → U → U) := {
    assoc : ∀ a b c, op a (op b c) = op (op a b) c;
}.
Class Comm {U} (op : U → U → U) := {
    comm : ∀ a b, op a b = op b a;
}.
#[universes(template)]
Class Id {U} (op : U → U → U) := {
    id : U;
}.
Class Lid {U} (op : U → U → U) `{Id U op} := {
    lid : ∀ a, op id a = a;
}.
Class Rid {U} (op : U → U → U) `{Id U op} := {
    rid : ∀ a, op a id = a;
}.
Class Lcancel {U} (op : U → U → U) := {
    lcancel : ∀ {a b} c, op c a = op c b → a = b;
}.
Class Rcancel {U} (op : U → U → U) := {
    rcancel : ∀ {a b} c, op a c = op b c → a = b;
}.

#[universes(template)]
Class Anni {U} (op : U → U → U) := {
    anni : U;
}.
Class Lanni {U} (op : U → U → U) `{Anni U op} := {
    lanni : ∀ a, op anni a = anni;
}.
Class Ranni {U} (op : U → U → U) `{Anni U op} := {
    ranni : ∀ a, op a anni = anni;
}.

#[universes(template)]
Class Inv {U} (op : U → U → U) := {
    inv : U → U;
}.
Class Linv {U} (op : U → U → U) `{Id U op} `{Inv U op} := {
    linv : ∀ a, op (inv a) a = id;
}.
Class Rinv {U} (op : U → U → U) `{Id U op} `{Inv U op} := {
    rinv : ∀ a, op a (inv a) = id;
}.

Class Idempotent {U} (op : U → U → U) := {
    idemp : ∀ a, op a a = a;
}.

Arguments id : simpl never.
Arguments anni : simpl never.
Arguments inv : simpl never.


(* begin hide *)
Section OpMonoidImply.

Context {U} (op : U → U → U) `{
    ID : Id U op,
    @Lid U op ID,
    Lcancel U op,
    Comm U op,
    ANNI : Anni U op,
    @Lanni U op ANNI,
    INV : Inv U op,
    @Linv U op ID INV
}.

Local Infix "·" := op.
(* end hide *)

Lemma lid_rid_ : ∀ a, a · id = a.
    intros a.
    rewrite comm.
    apply lid.
Qed.

Lemma lcancel_rcancel_ : ∀ a b c, a · c = b · c → a = b.
    intros a b c eq.
    do 2 rewrite (comm _ c) in eq.
    apply lcancel with c.
    exact eq.
Qed.

Lemma lanni_ranni_ : ∀ a, a · anni = anni.
    intros a.
    rewrite comm.
    apply lanni.
Qed.

Lemma linv_rinv : ∀ a, a · inv a = id.
    intros a.
    rewrite comm.
    apply linv.
Qed.

Global Instance lid_rid : Rid op := {
    rid := lid_rid_;
}.

Global Instance lcancel_rcancel : Rcancel op := {
    rcancel := lcancel_rcancel_;
}.

Global Instance lanni_ranni : Ranni op := {
    ranni := lanni_ranni_;
}.

Global Instance linv_rinv_class : Rinv op := {
    rinv := linv_rinv;
}.

(* begin hide *)
End OpMonoidImply.


Section OpGroup.

Context {U} (op : U → U → U) `{
    Assoc U op,
    Comm U op,
    ID : Id U op,
    @Lid U op ID,
    @Rid U op ID,
    Lcancel U op,
    Rcancel U op,
    ANNI : Anni U op,
    @Lanni U op ANNI,
    @Ranni U op ANNI,
    INV : Inv U op,
    @Linv U op ID INV,
    @Rinv U op ID INV
}.
(* end hide *)

Infix "·" := op.

Theorem lop : ∀ {a b} c, a = b → c · a = c · b.
    intros a b c eq.
    rewrite eq.
    reflexivity.
Qed.

Theorem rop : ∀ {a b} c, a = b → a · c = b · c.
    intros a b c eq.
    rewrite eq.
    reflexivity.
Qed.

Theorem lrop : ∀ {a b c d}, a = b → c = d → a · c = b · d.
    intros a b c d ab cd.
    apply rop with c in ab.
    apply lop with b in cd.
    rewrite ab, <- cd.
    reflexivity.
Qed.

Lemma op_lcancel : ∀ a b c, c · a = c · b → a = b.
    intros a b c eq.
    apply lop with (inv c) in eq.
    do 2 rewrite assoc in eq.
    rewrite linv in eq.
    do 2 rewrite lid in eq.
    exact eq.
Qed.
Lemma op_rcancel : ∀ a b c, a · c = b · c → a = b.
    intros a b c eq.
    apply rop with (inv c) in eq.
    do 2 rewrite <- assoc in eq.
    rewrite rinv in eq.
    do 2 rewrite rid in eq.
    exact eq.
Qed.

Global Instance op_lcancel_class : Lcancel op := {
    lcancel := op_lcancel
}.
Global Instance op_rcancel_class : Rcancel op := {
    rcancel := op_rcancel
}.

Theorem inv_op : ∀ a b, inv (a · b) = inv b · inv a.
    intros a b.
    apply lcancel with (a · b).
    rewrite rinv.
    rewrite <- assoc.
    rewrite (assoc b).
    rewrite rinv, lid, rinv.
    reflexivity.
Qed.

Theorem inv_inv : ∀ a, inv (inv a) = a.
    intros a.
    apply lcancel with (inv a).
    rewrite linv, rinv.
    reflexivity.
Qed.

(* begin hide *)
End OpGroup.
(* end hide *)
