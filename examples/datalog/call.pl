main(X: field, Y: field, Z: u4) :- non_zero(X), non_zero(Y), to_field(Z) = Y.

non_zero(X: field) :- exists I: field. X * I = 1.
