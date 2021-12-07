non_zero(Z: field) :- ((Z + Y) + Y) + ~!-Y + to_field(Y);
                      Z;
                      exists A: field. A * Z = 1;
                      exists B: field, C: bool. B * C * Z = 4.
