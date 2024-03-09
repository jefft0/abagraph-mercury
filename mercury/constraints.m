:- module constraints.
:- interface.

:- import_module map.
:- import_module set.

:- type variable(T) ---> var(int).

:- type f_constraint
   ---> ':='(float)
   ;    '+'(variable(float), float)
   ;    '-'(variable(float), variable(float)).

:- type i_constraint
   ---> ':='(int)
   ;    '+'(variable(int), int)
   ;    '=<'(int).

:- type s_constraint
   ---> ':='(string).

:- type constraint
   ---> f(f_constraint)
   ;    i(i_constraint)
   ;    s(s_constraint).

:- type f_constraints == map(int, f_constraint).
:- type i_constraints == map(int, i_constraint).
:- type s_constraints == map(int, s_constraint).

:- type constraints ---> constraints(f_constraints, i_constraints, s_constraints).

:- func init = constraints.
% If there is no binding for V, add one for V and the constraint and set Descs to
% a set of description strings for the bindings (only if verbose).
% If there is a binding for V, confirm the constraint and set Descs to "",
% else if the constraint is not confirmed then fail.
:- pred unify(int::in, constraint::in, constraints::in, constraints::out, set(string)::out) is semidet.

:- implementation.

:- import_module float.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module options.
:- import_module pair.
:- import_module string.

:- pred f_unify(int::in, f_constraint::in, f_constraints::in, f_constraints::out, set(string)::out) is semidet.
:- pred i_unify(int::in, i_constraint::in, i_constraints::in, i_constraints::out, set(string)::out) is semidet.
:- pred s_unify(int::in, s_constraint::in, s_constraints::in, s_constraints::out, set(string)::out) is semidet.
:- pred f_new_value(int::in, float::in, f_constraints::in, f_constraints::out, set(string)::out) is det.
:- pred i_new_value(int::in, int::in, i_constraints::in, i_constraints::out, set(string)::out) is det.

init = constraints(map.init, map.init, map.init).

% Dispatch unify to f_unify, i_unify, etc.
unify(V, f(FC), constraints(FCs, ICs, SCs), constraints(FCsOut, ICs, SCs), Descs) :- f_unify(V, FC, FCs, FCsOut, Descs).
unify(V, i(IC), constraints(FCs, ICs, SCs), constraints(FCs, ICsOut, SCs), Descs) :- i_unify(V, IC, ICs, ICsOut, Descs).
unify(V, s(SC), constraints(FCs, ICs, SCs), constraints(FCs, ICs, SCsOut), Descs) :- s_unify(V, SC, SCs, SCsOut, Descs).

f_unify(V, ':='(Val), FCs, FCsOut, Descs) :-
  (search(FCs, V, C) ->
    C = ':='(BoundVal),
    Val = BoundVal,
    FCsOut = FCs,
    Descs = set.init
  ;
    % Add the binding.
    FCs1 = insert(FCs, V, ':='(Val)),
    f_new_value(V, Val, FCs1, FCsOut, Descs1),
    (verbose ->
      Descs = insert(Descs1, format("(var %i) = %f", [i(V), f(Val)]))
    ; 
      Descs = set.init)).
f_unify(V, var(X) + Y, FCs, FCsOut, Descs) :-
  (search(FCs, X, ':='(XVal)) ->
    Evaluated = yes(XVal + Y)
  ;
    Evaluated = no),

  (search(FCs, V, C) ->
    C = ':='(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    FCsOut = FCs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      FCsOut = insert(FCs, V, ':='(Val)),
      % TODO: Call f_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %f", [i(V), f(Val)]))
      ; 
        Descs = set.init)
    ;
      FCsOut = insert(FCs, V, var(X) + Y),
      Descs = set.init)).
f_unify(V, var(X) - var(Y), FCs, FCsOut, Descs) :-
  (search(FCs, X, ':='(XVal)), search(FCs, Y, ':='(YVal)) ->
    Evaluated = yes(XVal - YVal)
  ;
    Evaluated = no),

  (search(FCs, V, C) ->
    C = ':='(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    FCsOut = FCs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      FCsOut = insert(FCs, V, ':='(Val)),
      % TODO: Call f_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %f", [i(V), f(Val)]))
      ; 
        Descs = set.init)
    ;
      FCsOut = insert(FCs, V, var(X) - var(Y)),
      Descs = set.init)).
i_unify(V, ':='(Val), ICs, ICsOut, Descs) :-
  (search(ICs, V, ':='(BoundVal)) ->
    Val = BoundVal,
    ICsOut = ICs,
    Descs = set.init
  ;
    % Add the binding.
    ICs1 = insert(ICs, V, ':='(Val)),
    i_new_value(V, Val, ICs1, ICsOut, Descs1),
    (verbose ->
      Descs = insert(Descs1, format("(var %i) = %i", [i(V), i(Val)]))
    ; 
      Descs = set.init)).
i_unify(V, var(X) + Y, ICs, ICsOut, Descs) :-
  (search(ICs, X, ':='(XVal)) ->
    Evaluated = yes(XVal + Y)
  ;
    Evaluated = no),

  (search(ICs, V, C) ->
    C = ':='(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    ICsOut = ICs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      ICsOut = insert(ICs, V, ':='(Val)),
      % TODO: Call i_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %i", [i(V), i(Val)]))
      ; 
        Descs = set.init)
    ;
      ICsOut = insert(ICs, V, var(X) + Y),
      Descs = set.init)).
i_unify(V, '=<'(Val), ICs, ICsOut, Descs) :-
%  (search(ICs, V, ':='(BoundVal)) ->
%    BoundVal =< Val,
%    ICsOut = ICs,
%    Descs = set.init
%  ;
%    % TODO: Check for another constraint.
%    % Add the binding.
%    ICsOut = insert(ICs, V, '=<'(Val)),
%    (verbose ->
%      Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)]))
%    ; 
%      Descs = set.init)).
  ICsOut = ICs, Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)])).
s_unify(V, ':='(Val), SCs, SCsOut, Descs) :-
  (search(SCs, V, ':='(BoundVal)) ->
    Val = BoundVal,
    SCsOut = SCs,
    Descs = set.init
  ;
    % Add the binding.
    SCsOut = insert(SCs, V, ':='(Val)),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) = %s", [i(V), s(Val)]))
    ; 
      Descs = set.init)).

f_new_value(V, Val, FCs, FCsOut, Descs) :-
  FCsOut-Descs = foldl(
    (func(OtherV, C, FCsIn-DescsIn) = FCs1-Descs1 :-
      % Try to get the value of OtherV.
      (C = var(V) + Y1 ->
        OtherVal = yes(Val + Y1)
      ;(C = var(X) - var(V), search(FCsIn, X, ':='(XVal)) ->
        OtherVal = yes(XVal - Val)
      ;(C = var(V) - var(Y), search(FCsIn, Y, ':='(YVal)) ->
        OtherVal = yes(Val - YVal)
      ;
        % TODO: Check other expressions.
        OtherVal = no))),

      (OtherVal = yes(F) ->
        % Replace OtherV with evaluated value.
        (f_unify(OtherV, ':='(F), delete(FCsIn, OtherV), FCs2, Descs2) ->
          FCs1 = FCs2,
          Descs1 = union(DescsIn, Descs2)
        ;
          % This shouldn't happen.
          FCs1 = FCsIn,
          Descs1 = DescsIn)
      ;
        FCs1 = FCsIn,
        Descs1 = DescsIn)),
    FCs, FCs-set.init).

i_new_value(V, Val, ICs, ICsOut, Descs) :-
  ICsOut-Descs = foldl(
    (func(OtherV, C, ICsIn-DescsIn) = ICs1-Descs1 :-
      % Try to get the value of OtherV.
      (C = var(V) + Y1 ->
        OtherVal = yes(Val + Y1)
      ;
        % TODO: Check other expressions.
        OtherVal = no),

      (OtherVal = yes(I) ->
        % Replace OtherV with evaluated value.
        (i_unify(OtherV, ':='(I), delete(ICsIn, OtherV), ICs2, Descs2) ->
          ICs1 = ICs2,
          Descs1 = union(DescsIn, Descs2)
        ;
          % This shouldn't happen.
          ICs1 = ICsIn,
          Descs1 = DescsIn)
      ;
        ICs1 = ICsIn,
        Descs1 = DescsIn)),
    ICs, ICs-set.init).
