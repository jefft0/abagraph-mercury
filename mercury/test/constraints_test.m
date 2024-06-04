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

:- pred run_test(pred(constraint_store, constraint_store)).
:- mode run_test(pred(in, out) is semidet) is det.

% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.

main(!IO) :-
  % Test int \=
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('\\='(10)), !CS, _),
    unify(1, i(':='(11)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(10)), !CS, _),
    unify(1, i('\\='(11)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('\\='(10)), !CS, _),
    \+ unify(1, i(':='(10)), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(10)), !CS, _),
    \+ unify(1, i('\\='(10)), !.CS, _, _))),

  % Test int \==
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('\\=='(var(2))), !CS, _),
    unify(1, i(':='(10)), !CS, _),
    unify(2, i(':='(11)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(10)), !CS, _),
    unify(1, i('\\=='(var(2))), !CS, _),
    unify(2, i(':='(11)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(2, i(':='(11)), !CS, _),
    unify(1, i('\\=='(var(2))), !CS, _),
    unify(1, i(':='(10)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(10)), !CS, _),
    unify(2, i(':='(11)), !CS, _),
    unify(1, i('\\=='(var(2))), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('\\=='(var(2))), !CS, _),
    unify(1, i(':='(10)), !CS, _),
    \+ unify(2, i(':='(10)), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(10)), !CS, _),
    unify(1, i('\\=='(var(2))), !CS, _),
    \+ unify(2, i(':='(10)), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(10)), !CS, _),
    unify(2, i(':='(10)), !CS, _),
    \+ unify(1, i('\\=='(var(2))), !.CS, _, _))),

  % Test int +
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('+'(var(2), 5)), !CS, _),
    unify(1, i(':='(20)), !CS, _),
    unify(2, i(':='(15)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(20)), !CS, _),
    unify(1, i('+'(var(2), 5)), !CS, _),
    unify(2, i(':='(15)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(20)), !CS, _),
    unify(2, i(':='(15)), !CS, _),
    unify(1, i('+'(var(2), 5)), !CS, _))),

  % Test int ++
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('++'(var(2), var(3))), !CS, _),
    unify(1, i(':='(20)), !CS, _),
    unify(2, i(':='(5)), !CS, _),
    unify(3, i(':='(15)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(20)), !CS, _),
    unify(1, i('++'(var(2), var(3))), !CS, _),
    unify(2, i(':='(5)), !CS, _),
    unify(3, i(':='(15)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(2, i(':='(5)), !CS, _),
    unify(1, i('++'(var(2), var(3))), !CS, _),
    unify(1, i(':='(20)), !CS, _),
    unify(3, i(':='(15)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(20)), !CS, _),
    unify(2, i(':='(5)), !CS, _),
    unify(1, i('++'(var(2), var(3))), !CS, _),
    unify(3, i(':='(15)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(20)), !CS, _),
    unify(2, i(':='(5)), !CS, _),
    unify(3, i(':='(15)), !CS, _),
    unify(1, i('++'(var(2), var(3))), !CS, _))),

  % Test int -
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('-'(20, var(2))), !CS, _),
    unify(1, i(':='(15)), !CS, _),
    unify(2, i(':='(5)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(15)), !CS, _),
    unify(1, i('-'(20, var(2))), !CS, _),
    unify(2, i(':='(5)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(15)), !CS, _),
    unify(2, i(':='(5)), !CS, _),
    unify(1, i('-'(20, var(2))), !CS, _))),

  % Test int --
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('--'(var(2), var(3))), !CS, _),
    unify(1, i(':='(15)), !CS, _),
    unify(2, i(':='(20)), !CS, _),
    unify(3, i(':='(5)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(15)), !CS, _),
    unify(1, i('--'(var(2), var(3))), !CS, _),
    unify(2, i(':='(20)), !CS, _),
    unify(3, i(':='(5)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(3, i(':='(5)), !CS, _),
    unify(1, i('--'(var(2), var(3))), !CS, _),
    unify(1, i(':='(15)), !CS, _),
    unify(2, i(':='(20)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(2, i(':='(20)), !CS, _),
    unify(1, i('--'(var(2), var(3))), !CS, _),
    unify(1, i(':='(15)), !CS, _),
    unify(3, i(':='(5)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(15)), !CS, _),
    unify(2, i(':='(20)), !CS, _),
    unify(1, i('--'(var(2), var(3))), !CS, _),
    unify(3, i(':='(5)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(15)), !CS, _),
    unify(2, i(':='(20)), !CS, _),
    unify(3, i(':='(5)), !CS, _),
    unify(1, i('--'(var(2), var(3))), !CS, _))),

  % Test int =<
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('=<'(2)), !CS, _),
    unify(1, i(':='(1)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(1)), !CS, _),
    unify(1, i('=<'(2)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(2)), !CS, _),
    unify(1, i('=<'(2)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i(':='(3)), !CS, _),
    \+ unify(1, i('=<'(2)), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('=<'(5)), !CS, _),
    unify(1, i('=<'(2)), !CS, _), % Tighten
    \+ unify(1, i(':='(3)), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('=<'(2)), !CS, _),
    unify(1, i('=<'(5)), !CS, _), % Don't loosen.
    \+ unify(1, i(':='(3)), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('=<'(2)), !CS, _),
    unify(2, i('+'(var(1), 10)), !CS, _), % Adds (<= (var 2) 12)
    unify(2, i(':='(11)), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, i('=<'(2)), !CS, _),
    format("CS1\n%s", [s(to_string(!.CS))]),
    unify(2, i('+'(var(1), 10)), !CS, _), % Adds (<= (var 2) 12)
    format("CS2\n%s", [s(to_string(!.CS))]),
    \+ unify(2, i(':='(13)), !.CS, _, _))),

  % Test string \=
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s('\\='("a")), !CS, _),
    unify(1, s(':='("b")), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s(':='("a")), !CS, _),
    unify(1, s('\\='("b")), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s('\\='("a")), !CS, _),
    \+ unify(1, s(':='("a")), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s(':='("a")), !CS, _),
    \+ unify(1, s('\\='("a")), !.CS, _, _))),

  % Test string \==
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s('\\=='(var(2))), !CS, _),
    unify(1, s(':='("a")), !CS, _),
    unify(2, s(':='("b")), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s(':='("a")), !CS, _),
    unify(1, s('\\=='(var(2))), !CS, _),
    unify(2, s(':='("b")), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(2, s(':='("b")), !CS, _),
    unify(1, s('\\=='(var(2))), !CS, _),
    unify(1, s(':='("a")), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s(':='("a")), !CS, _),
    unify(2, s(':='("b")), !CS, _),
    unify(1, s('\\=='(var(2))), !CS, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s('\\=='(var(2))), !CS, _),
    unify(1, s(':='("a")), !CS, _),
    \+ unify(2, s(':='("a")), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s(':='("a")), !CS, _),
    unify(1, s('\\=='(var(2))), !CS, _),
    \+ unify(2, s(':='("a")), !.CS, _, _))),
  run_test((pred(!.CS::in, !:CS::out) is semidet :-
    unify(1, s(':='("a")), !CS, _),
    unify(2, s(':='("a")), !CS, _),
    \+ unify(1, s('\\=='(var(2))), !.CS, _, _))).

run_test(Test) :- (Test(constraints.init, _) -> format("pass\n", []) ; format("FAIL\n", [])).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure],
"
fputs(S, stdout);
").

format(S, PolyTypes) :- puts(format(S, PolyTypes)).
