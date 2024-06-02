:- module constraints_test.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module constraints.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module string.

:- pred run_test(pred(constraint_store)).
:- mode run_test(pred(in) is semidet) is det.

% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.

main(!IO) :-
  Tests = [
    % Test int \=
    (pred(CS::in) is semidet :-
      unify(1, i('\\='(10)), CS, CS1, _),
      unify(1, i(':='(11)), CS1, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(10)), CS, CS1, _),
      unify(1, i('\\='(11)), CS1, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i('\\='(10)), CS, CS1, _),
      \+ unify(1, i(':='(10)), CS1, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(10)), CS, CS1, _),
      \+ unify(1, i('\\='(10)), CS1, _, _)),

    % Test int \==
    (pred(CS::in) is semidet :-
      unify(1, i('\\=='(var(2))), CS, CS1, _),
      unify(1, i(':='(10)), CS1, CS2, _),
      unify(2, i(':='(11)), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(10)), CS, CS1, _),
      unify(1, i('\\=='(var(2))), CS1, CS2, _),
      unify(2, i(':='(11)), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(2, i(':='(11)), CS, CS1, _),
      unify(1, i('\\=='(var(2))), CS1, CS2, _),
      unify(1, i(':='(10)), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(10)), CS, CS1, _),
      unify(2, i(':='(11)), CS1, CS2, _),
      unify(1, i('\\=='(var(2))), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i('\\=='(var(2))), CS, CS1, _),
      unify(1, i(':='(10)), CS1, CS2, _),
      \+ unify(2, i(':='(10)), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(10)), CS, CS1, _),
      unify(1, i('\\=='(var(2))), CS1, CS2, _),
      \+ unify(2, i(':='(10)), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(10)), CS, CS1, _),
      unify(2, i(':='(10)), CS1, CS2, _),
      \+ unify(1, i('\\=='(var(2))), CS2, _, _)),

    % Test int +
    (pred(CS::in) is semidet :-
      unify(1, i('+'(var(2), 5)), CS, CS1, _),
      unify(1, i(':='(20)), CS1, CS2, _),
      unify(2, i(':='(15)), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(20)), CS, CS1, _),
      unify(1, i('+'(var(2), 5)), CS1, CS2, _),
      unify(2, i(':='(15)), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(20)), CS, CS1, _),
      unify(2, i(':='(15)), CS1, CS2, _),
      unify(1, i('+'(var(2), 5)), CS2, _, _)),

    % Test int ++
    (pred(CS::in) is semidet :-
      unify(1, i('++'(var(2), var(3))), CS, CS1, _),
      unify(1, i(':='(20)), CS1, CS2, _),
      unify(2, i(':='(5)), CS2, CS3, _),
      unify(3, i(':='(15)), CS3, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(20)), CS, CS1, _),
      unify(1, i('++'(var(2), var(3))), CS1, CS2, _),
      unify(2, i(':='(5)), CS2, CS3, _),
      unify(3, i(':='(15)), CS3, _, _)),
    (pred(CS::in) is semidet :-
      unify(2, i(':='(5)), CS, CS1, _),
      format("CS1\n%s", [s(to_string(CS1))]),
      unify(1, i('++'(var(2), var(3))), CS1, CS2, _),
      format("CS2\n%s", [s(to_string(CS2))]),
      unify(1, i(':='(20)), CS2, CS3, _),
      format("CS3\n%s", [s(to_string(CS3))]),
      unify(3, i(':='(15)), CS3, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(20)), CS, CS1, _),
      unify(2, i(':='(5)), CS1, CS2, _),
      unify(1, i('++'(var(2), var(3))), CS2, CS3, _),
      unify(3, i(':='(15)), CS3, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, i(':='(20)), CS, CS1, _),
      unify(2, i(':='(5)), CS1, CS2, _),
      unify(3, i(':='(15)), CS2, CS3, _),
      unify(1, i('++'(var(2), var(3))), CS3, _, _)),

    % Test string \=
    (pred(CS::in) is semidet :-
      unify(1, s('\\='("a")), CS, CS1, _),
      unify(1, s(':='("b")), CS1, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, s(':='("a")), CS, CS1, _),
      unify(1, s('\\='("b")), CS1, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, s('\\='("a")), CS, CS1, _),
      \+ unify(1, s(':='("a")), CS1, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, s(':='("a")), CS, CS1, _),
      \+ unify(1, s('\\='("a")), CS1, _, _)),

    % Test string \==
    (pred(CS::in) is semidet :-
      unify(1, s('\\=='(var(2))), CS, CS1, _),
      unify(1, s(':='("a")), CS1, CS2, _),
      unify(2, s(':='("b")), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, s(':='("a")), CS, CS1, _),
      unify(1, s('\\=='(var(2))), CS1, CS2, _),
      unify(2, s(':='("b")), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(2, s(':='("b")), CS, CS1, _),
      unify(1, s('\\=='(var(2))), CS1, CS2, _),
      unify(1, s(':='("a")), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, s(':='("a")), CS, CS1, _),
      unify(2, s(':='("b")), CS1, CS2, _),
      unify(1, s('\\=='(var(2))), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, s('\\=='(var(2))), CS, CS1, _),
      unify(1, s(':='("a")), CS1, CS2, _),
      \+ unify(2, s(':='("a")), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, s(':='("a")), CS, CS1, _),
      unify(1, s('\\=='(var(2))), CS1, CS2, _),
      \+ unify(2, s(':='("a")), CS2, _, _)),
    (pred(CS::in) is semidet :-
      unify(1, s(':='("a")), CS, CS1, _),
      unify(2, s(':='("a")), CS1, CS2, _),
      \+ unify(1, s('\\=='(var(2))), CS2, _, _))
  ],

  Tests = [T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30],
  run_test(T1),
  run_test(T2),
  run_test(T3),
  run_test(T4),
  run_test(T5),
  run_test(T6),
  run_test(T7),
  run_test(T8),
  run_test(T9),
  run_test(T10),
  run_test(T11),
  run_test(T12),
  run_test(T13),
  run_test(T14),
  run_test(T15),
  run_test(T16),
  run_test(T17),
  run_test(T18),
  run_test(T19),
  run_test(T20),
  run_test(T21),
  run_test(T22),
  run_test(T23),
  run_test(T24),
  run_test(T25),
  run_test(T26),
  run_test(T27),
  run_test(T28),
  run_test(T29),
  run_test(T30).

run_test(Test) :- (Test(constraints.init) -> format("Pass\n", []) ; format("Fail\n", [])).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure],
"
fputs(S, stdout);
").

format(S, PolyTypes) :- puts(format(S, PolyTypes)).
