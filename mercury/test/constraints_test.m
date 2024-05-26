:- module constraints_test.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module constraints.
:- import_module list.
:- import_module maybe.
:- import_module string.

:- pred test1 is semidet.
:- pred test2 is semidet.
:- pred test3 is semidet.
:- pred test4 is semidet.
:- pred test5 is semidet.
:- pred test6 is semidet.
:- pred test7 is semidet.
:- pred test8 is semidet.
:- pred test9 is semidet.
:- pred test10 is semidet.
:- pred test11 is semidet.
% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.

main(!IO) :-
  (test1, test2, test3, test4, test5, test6, test7, test8, test9, test10, test11 -> 
    format("Pass\n", [])
  ;
    format("Fail\n", [])).

% Test int +
test1 :-
  Cs = constraints.init,
  unify(1, i('+'(var(2), 5)), Cs, Cs1, _),
  unify(1, i(':='(20)), Cs1, Cs2, _),
  i_get(2, Cs2) = yes(15).

% Test string \=
test2 :-
  Cs = constraints.init,
  unify(1, s('\\='("a")), Cs, Cs1, _),
  unify(1, s(':='("b")), Cs1, _, _).
test3 :-
  Cs = constraints.init,
  unify(1, s(':='("a")), Cs, Cs1, _),
  unify(1, s('\\='("b")), Cs1, _, _).
test4 :-
  Cs = constraints.init,
  unify(1, s('\\='("a")), Cs, Cs1, _),
  \+ unify(1, s(':='("a")), Cs1, _, _).
test5 :-
  Cs = constraints.init,
  unify(1, s(':='("a")), Cs, Cs1, _),
  \+ unify(1, s('\\='("a")), Cs1, _, _).

% Test string \==
test6 :-
  Cs = constraints.init,
  unify(1, s('\\=='(var(2))), Cs, Cs1, _),
  unify(1, s(':='("a")), Cs1, Cs2, _),
  unify(2, s(':='("b")), Cs2, _, _).
test7 :-
  Cs = constraints.init,
  unify(1, s(':='("a")), Cs, Cs1, _),
  unify(1, s('\\=='(var(2))), Cs1, Cs2, _),
  unify(2, s(':='("b")), Cs2, _, _).
test8 :-
  Cs = constraints.init,
  unify(1, s(':='("a")), Cs, Cs1, _),
  unify(2, s(':='("b")), Cs1, Cs2, _),
  unify(1, s('\\=='(var(2))), Cs2, _, _).
test9 :-
  Cs = constraints.init,
  unify(1, s('\\=='(var(2))), Cs, Cs1, _),
  unify(1, s(':='("a")), Cs1, Cs2, _),
  \+ unify(2, s(':='("a")), Cs2, _, _).
test10 :-
  Cs = constraints.init,
  unify(1, s(':='("a")), Cs, Cs1, _),
  format("Cs1\n%s", [s(to_string(Cs1))]),
  unify(1, s('\\=='(var(2))), Cs1, Cs2, _),
  format("Cs2\n%s", [s(to_string(Cs2))]),
  \+ unify(2, s(':='("a")), Cs2, _, _).
test11 :-
  Cs = constraints.init,
  unify(1, s(':='("a")), Cs, Cs1, _),
  unify(2, s(':='("a")), Cs1, Cs2, _),
  \+ unify(1, s('\\=='(var(2))), Cs2, _, _).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure],
"
fputs(S, stdout);
").

format(S, PolyTypes) :- puts(format(S, PolyTypes)).
