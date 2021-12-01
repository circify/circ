hash(X: u8[5], Y: u8[5], decreasing n: u8) :-
    n = 0x00, X = Y;
  exists Z: u8[5].
    !(n = 0x00),
    X[0] + X[1] = Z[0],
    X[1] - X[2] = Z[1],
    X[2] | X[3] = Z[2],
    X[3] ^ X[4] = Z[3],
    hash(Z, Y, n).

main(X: private u8[5], Y: public u8[5]) :-
  hash(X, Y, 5).
