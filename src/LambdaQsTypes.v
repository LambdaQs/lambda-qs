Inductive tp : Type :=
| qbit : tp
| qref : tp
| arr  : tp -> tp -> tp
| cmd  : tp -> tp
.
