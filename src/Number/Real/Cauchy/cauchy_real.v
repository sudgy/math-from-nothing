Require Import init.

Require Import set.

Require Import cauchy_real_complete.

Notation "'real'" := (equiv_type real_equiv).

Export cauchy_real_plus (real_plus).
Export cauchy_real_plus (real_zero).
Export cauchy_real_plus (real_neg).
Export cauchy_real_plus (real_plus_comm).
Export cauchy_real_plus (real_plus_assoc).
Export cauchy_real_plus (real_plus_lid).
Export cauchy_real_plus (real_plus_linv).

Export cauchy_real_mult (real_mult).
Export cauchy_real_mult (real_one).
Export cauchy_real_mult (real_div).
Export cauchy_real_mult (real_ldist).
Export cauchy_real_mult (real_mult_comm).
Export cauchy_real_mult (real_mult_assoc).
Export cauchy_real_mult (real_mult_lid).
Export cauchy_real_mult (real_mult_linv).
Export cauchy_real_mult (real_not_trivial).

Export cauchy_real_order (real_order).
Export cauchy_real_order (real_le_connex).
Export cauchy_real_order (real_le_antisym).
Export cauchy_real_order (real_le_trans).
Export cauchy_real_order (real_le_lplus).
Export cauchy_real_order (real_le_mult).
Export cauchy_real_complete (real_sup_complete).
