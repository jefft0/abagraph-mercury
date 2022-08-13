:- module abagraph.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module pair.
:- import_module list.
:- import_module set.
:- import_module options.
:- import_module printing.

:- pred assumption(sentence::in) is semidet.
:- pred derive(sentence::in) is det.
:- pred initial_derivation_tuple(set(sentence)::in, step_tuple::out) is det.
%:- derivation(step_tuple::int, int::in, string::out, int::out) is det.

main(!IO) :-
  derive(fact("a")).

% TODO: this should be dynamic.
assumption(fact("a")).
assumption(fact("b")).

derive(S) :-
  %retractall(proving(_)),
  %assert(proving(S)),
  initial_derivation_tuple(make_singleton_set(S), InitTuple),
  (if verbose then
    print_step(0, InitTuple)
  else
    true),
  %retractall(sols(_)),
  %assert(sols(1)),
  %derivation(InitTuple, 1, _Result, _),
  %print_result(Result),
  %incr_sols.
  true.

initial_derivation_tuple(
    PropUnMrk,
    step_tuple(PropUnMrk-set.init-PropGr, % PropUnMrk-PropM-PropGr
               D0,                        % D
               set.init)) :-              % C
  % PropUnMrk is already a set. Instead of findall, use the set filter.
  %list_to_ord_set(PropUnMrk, O_PropUnMrk),
  %findall(A, (member(A, O_PropUnMrk),
  %            assumption(A)),
  %        D0),
  D0 = filter(assumption, PropUnMrk),
  %findall(V-[], member(V, O_PropUnMrk), PropGr).
  PropGr = map((func(V) = V-set.init), PropUnMrk).

%derivation(T, InN, Result, N) :-
%  T = step_tuple(N)
