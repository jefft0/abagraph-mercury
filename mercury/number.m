:- module number.
:- interface.

:- import_module constraints.

% number is a type class to allow math operations within a polymorphic definition,
% where the type T can be float, int, etc.
% (This is pretty basic. It seems like there should be an existing module somewhere.)
:- typeclass number(T) where [
  func T + T = T,
  func -(T) = T,
  func T - T = T,
  pred (T::in) == (T::in) is semidet,
  pred (T::in) \= (T::in) is semidet,
  pred (T::in) > (T::in) is semidet,
  pred (T::in) < (T::in) is semidet,
  pred (T::in) >= (T::in) is semidet,
  pred (T::in) =< (T::in) is semidet,
  func to_b_constraint(nb_constraint(T)) = b_constraint is det,
  func to_string(T) = string
].

:- instance number(float).
:- instance number(int).

:- implementation.

:- import_module float.
:- import_module int.
:- import_module list.
:- import_module string.

% TODO: Make this more generalized.
:- func f_tolerance = float is det.
:- func f_neg_tolerance = float is det.
f_tolerance =      0.00001.
f_neg_tolerance = -0.00001.

:- instance number(float) where [
    func((+)/2) is float.(+),
    func((-)/1) is float.(-),
    func((-)/2) is float.(-),
    (X == Y :- float.(float.(X - Y) =< f_tolerance), float.(float.(X - Y) >= f_neg_tolerance)),
    (X \= Y :- \+ X == Y),
    (X > Y :- float.(float.(X - Y) > f_tolerance)),
    (X < Y :- float.(float.(X - Y) < f_neg_tolerance)),
    (X >= Y :- float.(float.(X - Y) >= f_neg_tolerance)),
    (X =< Y :- float.(float.(X - Y) =< f_tolerance)),
    to_b_constraint(C) = f(C),
    to_string(X) = format("%f", [f(X)])
].
:- instance number(int) where [
    func((+)/2) is int.(+),
    func((-)/1) is int.(-),
    func((-)/2) is int.(-),
    (X == Y :- X = Y),
    (X \= Y :- X \= Y),
    pred((>)/2) is int.(>),
    pred((<)/2) is int.(<),
    pred((>=)/2) is int.(>=),
    pred((=<)/2) is int.(=<),
    to_b_constraint(C) = i(C),
    to_string(X) = format("%i", [i(X)])
].

