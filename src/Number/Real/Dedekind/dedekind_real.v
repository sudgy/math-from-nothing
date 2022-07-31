Require Import init.

Require Import set.

Require Import dedekind_real_base.
Require Import dedekind_real_order.
Require Import dedekind_real_plus.
Require Import dedekind_real_mult1.
Require Import dedekind_real_mult2.
Require Import dedekind_real_mult3.

Notation "'real'" := (set_type dedekind_cut).

Export dedekind_real_plus (real_plus).
Export dedekind_real_plus (real_zero).
Export dedekind_real_plus (real_neg).
Export dedekind_real_plus (real_plus_comm).
Export dedekind_real_plus (real_plus_assoc).
Export dedekind_real_plus (real_plus_lid).
Export dedekind_real_plus (real_plus_linv).

Export dedekind_real_mult1 (real_mult).
Export dedekind_real_mult2 (real_one).
Export dedekind_real_mult3 (real_div).
Export dedekind_real_mult2 (real_ldist).
Export dedekind_real_mult1 (real_mult_comm).
Export dedekind_real_mult2 (real_mult_assoc).
Export dedekind_real_mult2 (real_mult_lid).
Export dedekind_real_mult3 (real_mult_linv).
Export dedekind_real_mult3 (real_not_trivial).

Export dedekind_real_order (real_order).
Export dedekind_real_order (real_le_connex).
Export dedekind_real_order (real_le_antisym).
Export dedekind_real_order (real_le_trans).
Export dedekind_real_plus (real_le_lplus).
Export dedekind_real_mult1 (real_le_mult).
Export dedekind_real_order (real_sup_complete).
