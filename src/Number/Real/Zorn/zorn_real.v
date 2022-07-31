Require Import init.

Require Import set.

Require Import zorn_real_base.
Require Import zorn_real_zorn.
Require Import zorn_real_complete.

Notation "'real'" := (set_type (aof_set real_aof)).

Export zorn_real_zorn (real_plus).
Export zorn_real_zorn (real_zero).
Export zorn_real_zorn (real_neg).
Export zorn_real_zorn (real_plus_comm).
Export zorn_real_zorn (real_plus_assoc).
Export zorn_real_zorn (real_plus_lid).
Export zorn_real_zorn (real_plus_linv).

Export zorn_real_zorn (real_mult).
Export zorn_real_zorn (real_one).
Export zorn_real_zorn (real_div).
Export zorn_real_zorn (real_ldist).
Export zorn_real_zorn (real_mult_comm).
Export zorn_real_zorn (real_mult_assoc).
Export zorn_real_zorn (real_mult_lid).
Export zorn_real_zorn (real_mult_linv).
Export zorn_real_zorn (real_not_trivial).

Export zorn_real_zorn (real_order).
Export zorn_real_zorn (real_le_connex).
Export zorn_real_zorn (real_le_antisym).
Export zorn_real_zorn (real_le_trans).
Export zorn_real_zorn (real_le_lplus).
Export zorn_real_zorn (real_le_mult).
Export zorn_real_complete (real_sup_complete).
