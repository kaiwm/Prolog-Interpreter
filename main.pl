eval(E, V):-
    V is E.

isnegative(-_).

isnegative(X/Y):-
    (isnegative(X) ; isnegative(Y)).

isnegative(X):- number(X), X < 0.


convert(X/Y, NewX/NewY) :-
    convert(X, NewX),
    convert(Y, NewY).

convert(-E, E).

convert(E, SE):-
    (   number(E) -> SE is -1 * E
    ;   SE = E
    ).   


isexponent(X ^ N, X, N):-
    number(N).

isfraction(_/_).

% Base cases

simplify(-C, S) :-
    number(C),
    S is -C.

simplify(E, S):- number(E), S is E.

simplify(E, E):- atom(E).

% Exponents first

simplify(X ^ Y, S):-
    simplify(X, X1),
    simplify(Y, Y1),
    (   number(Y1), number(X1) -> S is X1 ^ Y1
    ;   isexponent(X1, B, N), number(N), number(Y1) -> NewN is N * Y1, S = B ^ NewN
    ;   X1 = 0 -> S = 0
    ;   Y1 = 0 -> S = 1
    ;   X1 = 1 -> S = 1
    ;   Y1 = 1 -> S = X1
    ;   S = X1 ^ Y1
    ).

simplify(X / (X^N), S):-
    NewN is N - 1,
    simplify(1 / (X^NewN), S).

simplify(A * X / (X^N), S):-
    NewN is N - 1,
    simplify(A / (X^NewN), S).

simplify(X^N / X, S):-
    NewN is N - 1,
    simplify(X^NewN-1, S).

simplify((X^N1) / (X^N2), S):-
    NewN is N1 - N2,
    (   NewN =:= 1 -> simplify(X, S)
    ;   NewN > 0 -> simplify(X^NewN, S)
    ;   NewN < 0 -> RevN is N2 - N1, simplify(1 / (X^RevN), S)
    ).

simplify(A * (X^N1) / (X^N2), S):-
    NewN is N1 - N2,
    (   NewN =:= 1 -> simplify(A * X, S)
    ;   NewN > 0 -> simplify(A * X^NewN, S)
    ;   NewN < 0 -> RevN is N2 - N1, simplify(A / (X^RevN), S)
    ).

simplify((X^N1) / B * (X^N2), S):-
    NewN is N1 - N2,
    (   NewN =:= 1 -> simplify(X / B, S)
    ;   NewN > 0 -> simplify(X^NewN / B, S)
    ;   NewN < 0 -> RevN is N2 - N1, simplify(1 / B * (X^RevN), S)
    ).

simplify(A * (X^N1) / B * (X^N2), S):-
    NewN is N1 - N2,
    (   NewN =:= 1 -> simplify(A * X / B, S)
    ;   NewN > 0 -> simplify(A * X^NewN / B, S)
    ;   NewN < 0 -> RevN is N2 - N1, simplify(A / B * (X^RevN), S)
    ).

% Next Multiplication and division

simplify(-X * -Y, S):-
    simplify(X * Y, S).

simplify(X * (Y + Z), S):-
    simplify(X, X1),
    simplify(X1 * Y, Y1),
    simplify(X1 * Z, Z1),
    simplify(Y1 + Z1, S).

simplify((Y + Z) * X, S):-
    simplify(X, X1),
    simplify(X1 * Y, Y1),
    simplify(X1 * Z, Z1),
    simplify(Y1 + Z1, S).

simplify(X * (Y - Z), S):-
    simplify(X, X1),
    simplify(X1 * Y, Y1),
    simplify(X1 * Z, Z1),
    simplify(Y1 - Z1, S).

simplify((Y - Z) * X, S):-
    simplify(X, X1),
    simplify(X1 * Y, Y1),
    simplify(X1 * Z, Z1),
    simplify(Y1 - Z1, S).

simplify(X * (Y * Z), S):-
    simplify(X, X1),
    simplify(Y, Y1),
    simplify(Z, Z1),
    (number(X1), number(Y1) -> C is X1 * Y1, simplify(C * Z1, S)).

simplify(X * Y, S):-
    simplify(X, X1),
    simplify(Y, Y1),
    (   number(Y1), number(X1) -> S is X1 * Y1
    ;   X1 = 0 -> S = 0
    ;   Y1 = 0 -> S = 0
    ;   X1 = 1 -> S = Y1
    ;   Y1 = 1 -> S = X1
    ;   S = X1 * Y1
    ).

simplify((X * Y) / Y, S):-
    simplify(X, S).

simplify((Y * X) / Y, S):-
    simplify(X, S).

simplify(X / Y, S):-
    simplify(X, X1),
    simplify(Y, Y1),
    (   number(Y1), number(X1), Y1 =\= 0 -> S is X1 / Y1
    ;   X1 = 0 -> S = 0
    ;   Y1 = 0 -> !, fail
    ;   X1 = Y1 -> S = 1
    ;   S = X1 / Y1
    ).

% Addition and subtraction

simplify((A*X)+X, S):-
    simplify(A+1, C),
    S = C * X.

simplify(X+(A*X), S):-
    simplify(A+1, C),
    S = C * X.

simplify((A*X)+(B*X), S):-
    simplify(A, A1),
    simplify(B, B1),
    simplify(X, X1),
    (   number(A), number(B) -> C is A + B, S = C*X
    ;   S = A1*X1 + B1*X1
    ).

simplify(X + Y, S):-
    simplify(X, X1),
    simplify(Y, Y1),
    (   number(Y1), number(X1) -> S is X1 + Y1
    ;   isnegative(Y1) -> convert(Y1, Y2), simplify(X1 - Y2, S)
    ;   X1 = 0 -> S = Y1
    ;   Y1 = 0 -> S = X1
    ;   X1 = Y1 -> S = 2 * X1
    ;   S = X1 + Y1
    ).

simplify(-(-X), S):-
    simplify(X, S).

simplify(X- (-Y), S):-
    simplify(X + Y, S).

simplify((A*X)-X, S):-
    simplify(A-1, C),
    S = C * X.

simplify(X-(A*X), S):-
    simplify(1-A, C),
    S = C * X.

simplify((A*X)-(B*X), S):-
    simplify(A, A1),
    simplify(B, B1),
    simplify(X, X1),
    (   number(A), number(B) -> C is A - B, S = C*X1
    ;   S = A1*X1 - B1*X1
    ).

simplify(X - Y, S):-
    simplify(X, X1),
    simplify(Y, Y1),
    (   number(Y1), number(X1) -> S is X1 - Y1
    ;   isnegative(Y1) -> convert(Y1, Y2), simplify(X1 + Y2, S)
    ;   X1 = 0 -> S = -Y1
    ;   Y1 = 0 -> S = X1
    ;   X1 = Y1 -> S = 0
    ;   S = X1 - Y1
    ).

deriv(E, D):-
    simplify(E, SE),
    deriv_helper(SE, DS),
    simplify(DS, D).

% Base case: derivative of a constant is 0
deriv_helper(C, 0) :- number(C).

% Derivative of x is 1
deriv_helper(x, 1).

% Derivative of x^n is n*x^(n-1)
deriv_helper(X^N, N*NE) :-
    E = X ^ (N - 1),
    simplify(E, NE).

% Derivative of a sum is the sum of the derivatives
deriv_helper(A + B, DA + DB) :-
    deriv_helper(A, DA),
    deriv_helper(B, DB).

% Derivative of a difference is the difference of the derivatives
deriv_helper(A - B, DA - DB) :-
    deriv_helper(A, DA),
    deriv_helper(B, DB).

% Derivative of a product is (derivative of A) * B + A * (derivative of B)
deriv_helper(A * B, DA * B + A * DB) :-
    deriv_helper(A, DA),
    deriv_helper(B, DB).

% Derivative of a quotient is (derivative of A * B - A * (derivative of B)) / B^2
deriv_helper(A / B, (DA * B - A * DB) / (B^2)) :-
    deriv_helper(A, DA),
    deriv_helper(B, DB).

% Additional rule to handle division by a constant
deriv_helper(A / C, DA / C) :-
    deriv_helper(A, DA).

% Derivative of a unary minus is the unary minus of the derivative
deriv_helper(-A, (-D)) :-
    deriv_helper(A, D).

deriv_helper(-C, -1):-
    number(C).