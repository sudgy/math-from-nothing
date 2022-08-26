Require Import init.

(* Comment out different lines to use a different construction *)
Require Import dedekind_real.
(*Require Import zorn_real.*)

Require Export order_plus.
Require Export order_mult.
Require Export order_def.

Record CompleteOrderedField := make_cof {
    cof_U : Type;

    cof_plus : Plus cof_U;
    cof_zero : Zero cof_U;
    cof_neg : Neg cof_U;
    cof_plus_assoc : @PlusAssoc cof_U cof_plus;
    cof_plus_comm : @PlusComm cof_U cof_plus;
    cof_plus_lid : @PlusLid cof_U cof_plus cof_zero;
    cof_plus_linv : @PlusLinv cof_U cof_plus cof_zero cof_neg;

    cof_mult : Mult cof_U;
    cof_one : One cof_U;
    cof_div : Div cof_U;
    cof_ldist : @Ldist cof_U cof_plus cof_mult;
    cof_mult_comm : @MultComm cof_U cof_mult;
    cof_mult_assoc : @MultAssoc cof_U cof_mult;
    cof_mult_lid : @MultLid cof_U cof_mult cof_one;
    cof_mult_linv : @MultLinv cof_U cof_zero cof_mult cof_one cof_div;
    cof_not_trivial : @NotTrivial cof_U;

    cof_order : @Order cof_U;
    cof_le_connex : @Connex cof_U le;
    cof_le_antisym : @Antisymmetric cof_U le;
    cof_le_trans : @Transitive cof_U le;
    cof_le_lplus : @OrderLplus cof_U cof_plus cof_order;
    cof_le_mult : @OrderMult cof_U cof_zero cof_mult cof_order;
    cof_complete : @SupremumComplete cof_U le;
}.

Theorem real_ex : inhabited CompleteOrderedField.
Proof.
    split.
    exact (make_cof real real_plus real_zero real_neg real_plus_assoc
        real_plus_comm real_plus_lid real_plus_linv real_mult real_one real_div
        real_ldist real_mult_comm real_mult_assoc real_mult_lid real_mult_linv
        real_not_trivial real_order real_le_connex real_le_antisym real_le_trans
        real_le_lplus real_le_mult real_sup_complete).
Qed.

Definition real_cof := indefinite_description real_ex.

Definition real := cof_U real_cof.

Definition real_plus := cof_plus real_cof.
Definition real_zero := cof_zero real_cof.
Definition real_neg := cof_neg real_cof.
Definition real_plus_assoc := cof_plus_assoc real_cof.
Definition real_plus_comm := cof_plus_comm real_cof.
Definition real_plus_lid := cof_plus_lid real_cof.
Definition real_plus_linv := cof_plus_linv real_cof.

Definition real_mult := cof_mult real_cof.
Definition real_one := cof_one real_cof.
Definition real_div := cof_div real_cof.
Definition real_ldist := cof_ldist real_cof.
Definition real_mult_comm := cof_mult_comm real_cof.
Definition real_mult_assoc := cof_mult_assoc real_cof.
Definition real_mult_lid := cof_mult_lid real_cof.
Definition real_mult_linv := cof_mult_linv real_cof.
Definition real_not_trivial := cof_not_trivial real_cof.

Definition real_order := cof_order real_cof.
Definition real_le_connex := cof_le_connex real_cof.
Definition real_le_antisym := cof_le_antisym real_cof.
Definition real_le_trans := cof_le_trans real_cof.
Definition real_le_lplus := cof_le_lplus real_cof.
Definition real_le_mult := cof_le_mult real_cof.
Definition real_complete := cof_complete real_cof.

Global Existing Instances real_plus real_zero real_neg real_plus_assoc
    real_plus_comm real_plus_lid real_plus_linv real_mult real_one real_div
    real_ldist real_mult_comm real_mult_assoc real_mult_lid real_mult_linv
    real_not_trivial real_order real_le_connex real_le_antisym real_le_trans
    real_le_lplus real_le_mult real_complete.
