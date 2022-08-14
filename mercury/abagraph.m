:- module abagraph.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module pair.
:- import_module list.
:- import_module set.
:- import_module int.
:- import_module options.
:- import_module printing.

:- pred assumption(sentence::in) is semidet.
:- pred derive(sentence::in) is det.
:- pred initial_derivation_tuple(set(sentence)::in, step_tuple::out) is det.
:- pred derivation(step_tuple::in, int::in, derive_result::out, int::out) is det.
:- pred derivation_step(step_tuple::in, step_tuple::out) is det.

main(!IO) :-
  derive(fact("a")).

% TODO: this should be dynamic.
assumption(fact("a")).
assumption(fact("b")).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: entry predicates

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
  derivation(InitTuple, 1, Result, _),
  print_result(Result),
  %incr_sols.
  true.

initial_derivation_tuple(
    PropUnMrk,
    step_tuple(PropUnMrk-set.init-PropGr, % PropUnMrk-PropM-PropGr
               set.init-set.init,         % OppUnMrk-OppM (members of each are Claim-UnMrk-Mrk-Graph)
               D0,                        % D
               set.init)) :-              % C
  % PropUnMrk is already a set. Instead of findall, use the set filter.
  %list_to_ord_set(PropUnMrk, O_PropUnMrk),
  %findall(A, (member(A, O_PropUnMrk),
  %            assumption(A)),
  %        D0),
  D0 = filter(assumption, PropUnMrk),
  PropGr = map((func(V) = V-set.init), PropUnMrk).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: basic control structure

derivation(T, InN, Result, N) :-
  (if T = step_tuple(set.init-PropMrk-PropG, set.init-OppM, D, C) then
    Result = derive_result(PropMrk-PropG, OppM, D, C),
    N = InN
  else
    derivation_step(T, T1),
    (if verbose then
      print_step(InN, T1)
    else
      true),
    OutN = InN + 1,
    derivation(T1, OutN, Result, N)).

derivation_step(T, T1) :-
  T1 = T.
