:- module constraints.
:- interface.

:- import_module map.
:- import_module set.

:- type var(T) ---> var(int).

:- type n_constraint(T)
   ---> ':='(T)
   ;    '+'(var(T), T)
   ;    '++'(var(T), var(T))
   ;    '--'(var(T), var(T))
   ;    '=<'(T).

:- type f_constraint == n_constraint(float).
:- type i_constraint == n_constraint(int).

:- type s_constraint
   ---> ':='(string).

:- type constraint
   ---> f(n_constraint(float))
   ;    i(n_constraint(int))
   ;    s(s_constraint).

% A variable is either the bound value val(X) or constraints cs.
% (We don't put the ':=' constraint in cs.)
:- type n_constraints(T)
   ---> val(T)
   ;    cs(set(n_constraint(T))).
:- type s_constraints
   ---> val(string)
   ;    cs(set(s_constraint)).

:- type constraints ---> constraints(map(int, n_constraints(float)), map(int, n_constraints(int)), map(int, s_constraints)).

:- func init = constraints.

% unify(V, C, Cs, CsOut, Descs).
% If there is no binding for V, add one for V and the constraint C and set Descs to
% a set of description strings for the bindings (only if verbose).
% If there is a binding for V, confirm the constraint and set Descs to "",
% else if the constraint is not confirmed then fail.
:- pred unify(int::in, constraint::in, constraints::in, constraints::out, set(string)::out) is semidet.

:- func f_constraint_to_string(int, n_constraint(float)) = string is det.
:- func i_constraint_to_string(int, n_constraint(int)) = string is det.
:- func s_constraint_to_string(int, s_constraint) = string is det.

:- implementation.

:- import_module bool.
:- import_module list.
:- import_module maybe.
:- import_module number.
:- import_module options.
:- import_module pair.
:- import_module string.

:- pred n_unify(int::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, set(string)::out) is semidet <= number(T).
:- pred s_unify(int::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, set(string)::out) is semidet.
:- pred n_add_constraint(int::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, bool::out) is det.
% n_new_value(Val, CSet, Cs, CsOut, Descs).
% Iterate the constraints in CSet and confirm boolean constraints with Val or maybe get a new value
% for another variable in the arithmetic expression.
:- pred n_new_value(T::in, set(n_constraint(T))::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, set(string)::out) is semidet <= number(T).
:- func n_constraint_to_string(int, n_constraint(T)) = string is det <= number(T).

init = constraints(map.init, map.init, map.init).

% Dispatch unify to n_unify, s_unify, etc.
unify(V, f(FC), constraints(FCs, ICs, SCs), constraints(FCsOut, ICs, SCs), Descs) :- n_unify(V, FC, FCs, FCsOut, Descs).
unify(V, i(IC), constraints(FCs, ICs, SCs), constraints(FCs, ICsOut, SCs), Descs) :- n_unify(V, IC, ICs, ICsOut, Descs).
unify(V, s(SC), constraints(FCs, ICs, SCs), constraints(FCs, ICs, SCsOut), Descs) :- s_unify(V, SC, SCs, SCsOut, Descs).

n_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, VCs) ->
    (VCs = val(BoundVal) ->
      % Just confirm with the existing value.
      Val = BoundVal,
      CsOut = Cs,
      Descs = set.init
    ;
      % Save the CSet.
      VCs = cs(CSet),
      % Set the binding as the only constraint.
      Cs1 = set(Cs, V, val(Val)),
      n_new_value(Val, CSet, Cs1, CsOut, Descs1),
      (verbose ->
        Descs = insert(Descs1, format("(var %i) = %s", [i(V), s(to_string(Val))]))
      ; 
        Descs = Descs1))
  ;
    % Create the entry for V.
    CsOut = set(Cs, V, val(Val)),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) = %s", [i(V), s(to_string(Val))]))
    ; 
      Descs = set.init)).
n_unify(V, var(X) + Y, Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    % We already know the value. Treat this like assignment.
    n_unify(V, ':='(XVal + Y), Cs, CsOut, Descs)
  ;
    n_add_constraint(V, var(X) + Y, Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(X, var(V) + (-Y), CsOut1, CsOut2, Descs1),

      % Add or tighten boolean constraints.
      (search(CsOut2, X, cs(XCSet)) ->
        foldl(
          (pred(XC::in, CsIn-DescsIn::in, CsOut3-Descs3::out) is semidet :-
            (XC = '=<'(XVal) ->
              % We have var(V) = var(X) + Y and also var(X) =< XVal, so add
              % var(V) =< XVal + Y.
              n_unify(V, '=<'(XVal + Y), CsIn, CsOut3, Descs2),
              Descs3 = union(DescsIn, Descs2)
            ;
              CsOut3 = CsIn,
              Descs3 = DescsIn)),
          XCSet, CsOut2-Descs1, CsOut-Descs)
      ;
        CsOut = CsOut2,
        Descs = Descs1)
    ;
      CsOut = CsOut1,
      Descs = set.init)).
n_unify(V, var(X) ++ var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)), search(Cs, Y, val(YVal)) ->
    % We already know the value. Treat this like assignment.
    n_unify(V, ':='(XVal + YVal), Cs, CsOut, Descs)
  ;
    n_add_constraint(V, var(X) ++ var(Y), Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(X, var(V) -- var(Y), CsOut1, CsOut2, Descs1),
      n_unify(Y, var(V) -- var(X), CsOut2, CsOut, Descs2),
      Descs = union(Descs1, Descs2)
    ;
      CsOut = CsOut1,
      Descs = set.init)).
n_unify(V, var(X) -- var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)), search(Cs, Y, val(YVal)) ->
    % We already know the value. Treat this like assignment.
    n_unify(V, ':='(XVal - YVal), Cs, CsOut, Descs)
  ;
    n_add_constraint(V, var(X) -- var(Y), Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(X, var(V) ++ var(Y), CsOut1, CsOut2, Descs1),
      n_unify(Y, var(X) -- var(V), CsOut2, CsOut, Descs2),
      Descs = union(Descs1, Descs2)
    ;
      CsOut = CsOut1,
      Descs = set.init)).
n_unify(V, '=<'(Val), Cs, CsOut, Descs) :-
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
  (search(Cs, V, cs(CSet)) ->  % Debug
    CsOut = set(Cs, V, cs(insert(CSet, '=<'(Val))))
  ;
    CsOut = set(Cs, V, cs(make_singleton_set('=<'(Val))))  
  ),
  Descs = make_singleton_set(format("(var %i) <= %s", [i(V), s(to_string(Val))])).
s_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, val(BoundVal)) ->
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Set the binding as the only constraint.
    CsOut = set(Cs, V, val(Val)),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) = %s", [i(V), s(Val)]))
    ; 
      Descs = set.init)).

% If the constraints for V already has C, then set AddTransformed no and do nothing.
% If the constraints for V already has a val, then set AddTransformed yes and do nothing.
% Otherwise, set AddTransformed yes and add C to the constraints for V.
% If AddTransformed is yes, then you should add the transformed constraint(s) to the other variable(s).
n_add_constraint(V, C, Cs, CsOut, AddTransformed) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = cs(CSet1) ->
      (member(C, CSet1) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        AddTransformed = no
      ;
        CsOut = set(Cs, V, cs(insert(CSet1, C))),
        AddTransformed = yes)
    ;
      % This is already val(X).
      CsOut = Cs,
      AddTransformed = yes)
  ;
    % New variable.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    AddTransformed = yes).

n_new_value(Val, CSet, Cs, CsOut, Descs) :-
  foldl(
    (pred(C::in, CsIn-DescsIn::in, CsOut1-Descs1::out) is semidet :-
      % If we need to assign a new value for X, first search(CsIn, X, cs(_)) to
      % confirm that it hasn't already been assigned. (Prevent loops.)
      (C = var(X) + Y, search(CsIn, X, cs(_)) ->
        % We have Val = X + Y. Set X to Val - Y).
        n_unify(X, ':='(Val - Y), CsIn, CsOut1, Descs1)
      ;(C = var(X) ++ var(Y), search(CsIn, X, val(XVal)), search(CsIn, Y, cs(_)) ->
        % We have Val = X + Y and XVal. Set Y to Val - XVal.
        n_unify(Y, ':='(Val - XVal), CsIn, CsOut1, Descs1)
      ;(C = var(X) ++ var(Y), search(CsIn, Y, val(YVal)), search(CsIn, X, cs(_)) ->
        % We have Val = X + Y and YVal. Set X to Val - YVal.
        n_unify(X, ':='(Val - YVal), CsIn, CsOut1, Descs1)
      ;(C = var(X) -- var(Y), search(CsIn, X, val(XVal)), search(CsIn, Y, cs(_)) ->
        % We have Val = X - Y and XVal. Set Y to XVal - Val.
        n_unify(Y, ':='(XVal - Val), CsIn, CsOut1, Descs1)
      ;(C = var(X) -- var(Y), search(CsIn, Y, val(YVal)), search(CsIn, X, cs(_)) ->
        % We have Val = X - Y and YVal. Set X to Val + YVal.
        n_unify(X, ':='(Val + YVal), CsIn, CsOut1, Descs1)
      % Check boolean constraints.
      ;(C = '=<'(X) ->
        Val =< X,
        CsOut1 = CsIn,
        Descs1 = DescsIn
      ;
        % This shouldn't happen.
        CsOut1 = CsIn,
        Descs1 = DescsIn))))))),
    CSet, Cs-set.init, CsOut-Descs).

n_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %s)", [i(V), s(to_string(Val))]).
n_constraint_to_string(V, var(X1) + X2) =       format("(= (var %i) (+ (var %i) %s)", [i(V), i(X1), s(to_string(X2))]).
n_constraint_to_string(V, var(X1) ++ var(X2)) = format("(= (var %i) (+ (var %i) (var %i))", [i(V), i(X1), i(X2)]).
n_constraint_to_string(V, var(X1) -- var(X2)) = format("(= (var %i) (- (var %i) (var %i))", [i(V), i(X1), i(X2)]).
n_constraint_to_string(V, '=<'(X)) =            format("(<= (var %i) %s)", [i(V), s(to_string(X))]).

f_constraint_to_string(V, C) = n_constraint_to_string(V, C).
i_constraint_to_string(V, C) = n_constraint_to_string(V, C).
s_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %s)", [i(V), s(Val)]).
