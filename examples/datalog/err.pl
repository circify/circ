hash(X: u8[5], Y: u8[5], n: u8) :-
    n = 0, X = Y;
  exists Z: u8[5], B: bool.
    !(n = 0),
    X[0] + X[1] = Z[0] + B,
    X[1] - X[2] = Z[1],
    X[2] | X[3] = Z[2],
    X[3] ^ X[4] = Z[3],
    hash(Z, Y, n-1).

main(X: private u8[5], Y: public u8[5]) :-
  hash(X, Y, 5).
