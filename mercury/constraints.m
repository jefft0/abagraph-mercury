:- module constraints.
:- interface.

:- import_module map.
:- import_module set.

:- type var(T) ---> var(int).

:- type f_constraint
   ---> ':='(float)
   ;    '+'(var(float), float)
   ;    '--'(var(float), var(float))
   ;    '=<'(float).

:- type i_constraint
   ---> ':='(int)
   ;    '+'(var(int), int)
   ;    '--'(var(int), var(int))
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

:- func f_constraint_to_string(int, f_constraint) = string is det.
:- func i_constraint_to_string(int, i_constraint) = string is det.
:- func s_constraint_to_string(int, s_constraint) = string is det.

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

f_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, C) ->
    C = ':='(BoundVal),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Set the binding as the only constraint.
    Cs1 = set(Cs, V, ':='(Val)),
    f_new_value(V, Val, Cs1, CsOut, Descs1),
    (verbose ->
      Descs = insert(Descs1, format("(var %i) = %f", [i(V), f(Val)]))
    ; 
      Descs = set.init)).
f_unify(V, var(X) + Y, Cs, CsOut, Descs) :-
  (search(Cs, X, ':='(XVal)) ->
    Evaluated = yes(XVal + Y)
  ;
    Evaluated = no),

  (search(Cs, V, C) ->
    C = ':='(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      % Set the binding as the only constraint.
      CsOut = set(Cs, V, ':='(Val)),
      % TODO: Call f_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %f", [i(V), f(Val)]))
      ; 
        Descs = set.init)
    ;
      CsOut = insert(Cs, V, var(X) + Y),
      Descs = set.init)).
f_unify(V, var(X) -- var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, ':='(XVal)), search(Cs, Y, ':='(YVal)) ->
    Evaluated = yes(XVal - YVal)
  ;
    Evaluated = no),

  (search(Cs, V, C) ->
    C = ':='(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      % Set the binding as the only constraint.
      CsOut = set(Cs, V, ':='(Val)),
      % TODO: Call f_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %f", [i(V), f(Val)]))
      ; 
        Descs = set.init)
    ;
      CsOut = insert(Cs, V, var(X) -- var(Y)),
      Descs = set.init)).
f_unify(V, '=<'(Val), Cs, CsOut, Descs) :-
%  (search(Cs, V, ':='(BoundVal)) ->
%    BoundVal =< Val,
%    CsOut = Cs,
%    Descs = set.init
%  ;
%    % TODO: Check for another constraint.
%    % Add the binding.
%    CsOut = insert(Cs, V, '=<'(Val)),
%    (verbose ->
%      Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)]))
%    ; 
%      Descs = set.init)).
  CsOut = Cs, Descs = make_singleton_set(format("(var %i) <= %f", [i(V), f(Val)])).
i_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, C) ->
    C = ':='(BoundVal),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Set the binding as the only constraint.
    Cs1 = set(Cs, V, ':='(Val)),
    i_new_value(V, Val, Cs1, CsOut, Descs1),
    (verbose ->
      Descs = insert(Descs1, format("(var %i) = %i", [i(V), i(Val)]))
    ; 
      Descs = set.init)).
i_unify(V, var(X) + Y, Cs, CsOut, Descs) :-
  (search(Cs, X, ':='(XVal)) ->
    Evaluated = yes(XVal + Y)
  ;
    Evaluated = no),

  (search(Cs, V, C) ->
    C = ':='(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      % Set the binding as the only constraint.
      CsOut = set(Cs, V, ':='(Val)),
      % TODO: Call i_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %i", [i(V), i(Val)]))
      ; 
        Descs = set.init)
    ;
      CsOut = insert(Cs, V, var(X) + Y),
      Descs = set.init)).
i_unify(V, var(X) -- var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, ':='(XVal)), search(Cs, Y, ':='(YVal)) ->
    Evaluated = yes(XVal - YVal)
  ;
    Evaluated = no),

  (search(Cs, V, C) ->
    C = ':='(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      % Set the binding as the only constraint.
      CsOut = set(Cs, V, ':='(Val)),
      % TODO: Call f_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %i", [i(V), i(Val)]))
      ; 
        Descs = set.init)
    ;
      CsOut = insert(Cs, V, var(X) -- var(Y)),
      Descs = set.init)).
i_unify(V, '=<'(Val), Cs, CsOut, Descs) :-
%  (search(Cs, V, ':='(BoundVal)) ->
%    BoundVal =< Val,
%    CsOut = Cs,
%    Descs = set.init
%  ;
%    % TODO: Check for another constraint.
%    % Add the binding.
%    CsOut = insert(Cs, V, '=<'(Val)),
%    (verbose ->
%      Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)]))
%    ; 
%      Descs = set.init)).
  CsOut = Cs, Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)])).
s_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, ':='(BoundVal)) ->
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Set the binding as the only constraint.
    CsOut = set(Cs, V, ':='(Val)),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) = %s", [i(V), s(Val)]))
    ; 
      Descs = set.init)).

f_new_value(V, Val, Cs, CsOut, Descs) :-
  CsOut-Descs = foldl(
    (func(OtherV, OtherC, CsIn-DescsIn) = Cs1-Descs1 :-
      % Try to get the value of OtherV.
      (OtherC = var(V) + Y1 ->
        OtherVal = yes(Val + Y1)
      ;(OtherC = var(X) -- var(V), search(CsIn, X, ':='(XVal)) ->
        OtherVal = yes(XVal - Val)
      ;(OtherC = var(V) -- var(Y), search(CsIn, Y, ':='(YVal)) ->
        OtherVal = yes(Val - YVal)
      ;
        % TODO: Check other expressions.
        OtherVal = no))),

      (OtherVal = yes(NewVal) ->
        % Replace OtherV with evaluated value.
        (f_unify(OtherV, ':='(NewVal), delete(CsIn, OtherV), Cs2, Descs2) ->
          Cs1 = Cs2,
          Descs1 = union(DescsIn, Descs2)
        ;
          % This shouldn't happen.
          Cs1 = CsIn,
          Descs1 = DescsIn)
      ;
        Cs1 = CsIn,
        Descs1 = DescsIn)),
    Cs, Cs-set.init).

i_new_value(V, Val, Cs, CsOut, Descs) :-
  CsOut-Descs = foldl(
    (func(OtherV, OtherC, CsIn-DescsIn) = Cs1-Descs1 :-
      % Try to get the value of OtherV.
      (OtherC = var(V) + Y1 ->
        OtherVal = yes(Val + Y1)
      ;(OtherC = var(X) -- var(V), search(CsIn, X, ':='(XVal)) ->
        OtherVal = yes(XVal - Val)
      ;(OtherC = var(V) -- var(Y), search(CsIn, Y, ':='(YVal)) ->
        OtherVal = yes(Val - YVal)
      ;
        % TODO: Check other expressions.
        OtherVal = no))),

      (OtherVal = yes(NewVal) ->
        % Replace OtherV with evaluated value.
        (i_unify(OtherV, ':='(NewVal), delete(CsIn, OtherV), Cs2, Descs2) ->
          Cs1 = Cs2,
          Descs1 = union(DescsIn, Descs2)
        ;
          % This shouldn't happen.
          Cs1 = CsIn,
          Descs1 = DescsIn)
      ;
        Cs1 = CsIn,
        Descs1 = DescsIn)),
    Cs, Cs-set.init).

f_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %f)", [i(V), f(Val)]).
f_constraint_to_string(V, var(X1) + X2) =       format("(= (var %i) (+ (var %i) %f)", [i(V), i(X1), f(X2)]).
f_constraint_to_string(V, var(X1) -- var(X2)) = format("(= (var %i) (- (var %i) (var %i))", [i(V), i(X1), i(X2)]).
f_constraint_to_string(V, '=<'(X)) =            format("(<= (var %i) %f)", [i(V), f(X)]).
i_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %i)", [i(V), i(Val)]).
i_constraint_to_string(V, var(X1) + X2) =       format("(= (var %i) (+ (var %i) %i)", [i(V), i(X1), i(X2)]).
i_constraint_to_string(V, var(X1) -- var(X2)) = format("(= (var %i) (- (var %i) (var %i))", [i(V), i(X1), i(X2)]).
i_constraint_to_string(V, '=<'(X)) =            format("(<= (var %i) %i)", [i(V), i(X)]).
s_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %s)", [i(V), s(Val)]).
