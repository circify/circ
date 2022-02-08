bad_nz(X: field) :- exists I: field. X * I = 1, bad_nz(I).

main(X: field) :- bad_nz(X).
