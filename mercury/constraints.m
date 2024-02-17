:- module constraints.
:- interface.

:- import_module map.

:- type variable(T) ---> var(int).

:- type constraint
   ---> s(string).

:- type constraints == map(int, constraint).

:- func init = constraints.
:- pred unify(int::in, constraint::in, constraints::in, constraints::out, string::out) is semidet.

:- implementation.

:- import_module list.
:- import_module options.
:- import_module string.

init = map.init.

% If there is no binding for V, add one for V and C and set Desc to a description string (only if verbose).
% If there is a binding for V, confirm the constraint and set Desc to "",
% else if the constraint is not confirmed then fail.
unify(V, C, Bs, BsOut, Desc) :-
  (search(Bs, V, BoundC) ->
    % TODO: Does this fail properly?
    C = BoundC,
    BsOut = Bs,
    Desc = ""
  ;
    % Add the binding.
    BsOut = insert(Bs, V, C),
    (verbose ->
      C = s(String),
      Desc = format("(var %i) = %s", [i(V), s(String)])
    ; 
      Desc = "")).
