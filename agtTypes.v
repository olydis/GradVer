
Inductive primitive_type : Set :=
| Int : primitive_type
| Bool : primitive_type.
Definition primitive_type_dec : ∀ n m : primitive_type, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance primitive_type_EqDec : EqDec primitive_type eq := primitive_type_dec.
Hint Resolve primitive_type_dec.