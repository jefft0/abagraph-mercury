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
:- import_module printing. % only for n_dump_store
:- import_module string.

:- pred n_unify(int::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, set(string)::out) is semidet <= number(T).
:- pred s_unify(int::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, set(string)::out) is semidet.
% n_set_value(V, Val, Cs, CsOut, Descs).
% If Cs already has a val for V then confirm it. Otherwise set val(Val). If Cs has constraints, call n_set_value to evaluate them.
:- pred n_set_value(int::in, T::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, set(string)::out) is semidet <= number(T).
% n_new_value(Val, C, Cs, CsOut, Descs).
% The variable with constraint C has a new value Val. Confirm a boolean constraint C with Val or
% maybe get a new value for another variable in the arithmetic expression C.
:- pred n_new_value(T::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, set(string)::out) is semidet <= number(T).
% n_add_math_constraint(V, C, Cs, CsOut, AddTransformed).
% If the constraints for V already has C, then set AddTransformed no and do nothing.
% If the constraints for V already has a val, then set AddTransformed yes and do nothing.
% Otherwise, set AddTransformed yes and add C to the constraints for V.
% If AddTransformed is yes, then you should add the transformed constraint(s) to the other variable(s).
:- pred n_add_math_constraint(int::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, bool::out) is det.
:- func n_constraint_to_string(int, n_constraint(T)) = string is det <= number(T).
:- pred n_dump_store(string::in, map(int, n_constraints(T))::in) is det <= number(T).

init = constraints(map.init, map.init, map.init).

% Dispatch unify to n_unify, s_unify, etc.
unify(V, f(FC), constraints(FCs, ICs, SCs), constraints(FCsOut, ICs, SCs), Descs) :- n_unify(V, FC, FCs, FCsOut, Descs).
unify(V, i(IC), constraints(FCs, ICs, SCs), constraints(FCs, ICsOut, SCs), Descs) :- n_unify(V, IC, ICs, ICsOut, Descs).
unify(V, s(SC), constraints(FCs, ICs, SCs), constraints(FCs, ICs, SCsOut), Descs) :- s_unify(V, SC, SCs, SCsOut, Descs).

n_unify(V, ':='(Val), Cs, CsOut, Descs) :- n_set_value(V, Val, Cs, CsOut, Descs).
n_unify(V, var(X) + Y, Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    % We already know the value. Treat this like assignment.
    n_set_value(V, XVal + Y, Cs, CsOut, Descs)
  ;
    n_add_math_constraint(V, var(X) + Y, Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(X, var(V) + (-Y), CsOut1, CsOut2, Descs1),

      % Add or tighten boolean constraints.
      (search(CsOut2, X, cs(XCSet)) ->
        foldl(
          (pred(XC::in, CsIn-DescsIn::in, CsOut3-Descs3::out) is semidet :-
            (XC = '=<'(XVal) ->
              % We have var(V) - Y = var(X) and also var(X) =< XVal, so add
              % var(V) - Y =< XVal -> var(V) =< XVal + Y.
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
    n_set_value(V, XVal + YVal, Cs, CsOut, Descs)
  ;
    n_add_math_constraint(V, var(X) ++ var(Y), Cs, CsOut1, AddTransformed),
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
    n_set_value(V, XVal - YVal, Cs, CsOut, Descs)
  ;
    n_add_math_constraint(V, var(X) -- var(Y), Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(X, var(V) ++ var(Y), CsOut1, CsOut2, Descs1),
      n_unify(Y, var(X) -- var(V), CsOut2, CsOut, Descs2),
      Descs = union(Descs1, Descs2)
    ;
      CsOut = CsOut1,
      Descs = set.init)).
n_unify(V, '=<'(X), Cs, CsOut, Descs) :-
  C = '=<'(X),
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the constraint with the existing value.
      BoundVal =< X,
      CsOut = Cs,
      Descs = set.init
    ;
      ValOrCSet = cs(CSet),
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        Descs = set.init
      ;
        % Search for other boolean constraints and confirm or tighten.
        foldl(
          (pred(OtherC::in, CSetIn-AddCIn-CSetChangedIn::in, CSetOut1-AddCOut1-CSetChangedOut1::out) is semidet :-
            (AddCIn = no ->
              % We have discarded C in favor of another. Do nothing.
              CSetOut1 = CSetIn,
              AddCOut1 = AddCIn,
              CSetChangedOut1 = CSetChangedIn
            ;
              (OtherC = '=<'(OtherX) ->
                (OtherX =< X ->
                  % V =< OtherX is already tighter than V =< X, so discard C.
                  CSetOut1 = CSetIn,
                  AddCOut1 = no,
                  CSetChangedOut1 = CSetChangedIn
                ;
                  % Discard OtherC in favor of the tighter new C.
                  CSetOut1 = delete(CSetIn, OtherC),
                  AddCOut1 = AddCIn,
                  CSetChangedOut1 = yes))
              ;
                % Ignore OtherC.
                CSetOut1 = CSetIn,
                AddCOut1 = AddCIn,
                CSetChangedOut1 = CSetChangedIn)),
          CSet, pair.(CSet-yes)-no, pair.(CSet1-AddC)-CSetChanged),

        (AddC = yes ->
          % TODO: Search for math constraints and add a related boolean constraint.
          CsOut = set(Cs, V, cs(insert(CSet1, C))),
          (verbose ->
            Descs = make_singleton_set(format("(var %i) <= %s", [i(V), s(to_string(X))]))
          ; 
            Descs = set.init)
        ;
          (CSetChanged = yes ->
            % Update with the new CSet modified by the search.
            CsOut = set(Cs, V, cs(CSet1))
          ;
            CsOut = Cs),
          Descs = set.init)))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) <= %s", [i(V), s(to_string(X))]))
    ; 
      Descs = set.init)).
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

n_set_value(V, Val, Cs, CsOut, Descs) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the existing value.
      Val == BoundVal,
      CsOut = Cs,
      Descs = set.init
    ;
      % Save the constraints.
      ValOrCSet = cs(CSet),
      % Set the binding as the only constraint.
      Cs1 = set(Cs, V, val(Val)),

      (verbose ->
        Descs1 = make_singleton_set(format("(var %i) = %s", [i(V), s(to_string(Val))]))
      ; 
        Descs1 = set.init),
      % Possibly evaluate all the constraints.
      foldl(
        (pred(C::in, CsIn-DescsIn::in, CsOut1-DescsOut1::out) is semidet :-
          n_new_value(Val, C, CsIn, CsOut1, Descs2),
          DescsOut1 = union(DescsIn, Descs2)),
        CSet, Cs1-Descs1, CsOut-Descs))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, val(Val)),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) = %s", [i(V), s(to_string(Val))]))
    ; 
      Descs = set.init)).

n_new_value(Val, var(X) + Y, CsIn, CsOut, Descs) :-
  % We have Val = X + Y. Set X to Val - Y).
  n_set_value(X, Val - Y, CsIn, CsOut, Descs).
n_new_value(Val, var(X) ++ var(Y), CsIn, CsOut, Descs) :-
  (search(CsIn, X, val(XVal)) ->
    % We have Val = X + Y and XVal. Set Y to Val - XVal.
    n_set_value(Y, Val - XVal, CsIn, CsOut, Descs)
  ;(search(CsIn, Y, val(YVal)) ->
    % We have Val = X + Y and YVal. Set X to Val - YVal.
    n_set_value(X, Val - YVal, CsIn, CsOut, Descs)
  ;
    CsOut = CsIn, Descs = set.init)).
n_new_value(Val, var(X) -- var(Y), CsIn, CsOut, Descs) :-
  (search(CsIn, X, val(XVal)) ->
    % We have Val = X - Y and XVal. Set Y to XVal - Val.
    n_set_value(Y, XVal - Val, CsIn, CsOut, Descs)
  ;(search(CsIn, Y, val(YVal)) ->
    % We have Val = X - Y and YVal. Set X to Val + YVal.
    n_set_value(X, Val + YVal, CsIn, CsOut, Descs)
  ;
    CsOut = CsIn, Descs = set.init)).
% Boolean constraints.
n_new_value(Val, '=<'(X), CsIn, CsIn, set.init) :- Val =< X.
% Ignore. (Shouldn't happen.)
n_new_value(_Val, ':='(_), CsIn, CsIn, set.init).

n_add_math_constraint(V, C, Cs, CsOut, AddTransformed) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = cs(CSet) ->
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        AddTransformed = no
      ;
        CsOut = set(Cs, V, cs(insert(CSet, C))),
        AddTransformed = yes)
    ;
      % This is already val(X).
      CsOut = Cs,
      AddTransformed = yes)
  ;
    % New variable.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    AddTransformed = yes).

n_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %s)", [i(V), s(to_string(Val))]).
n_constraint_to_string(V, var(X1) + X2) =       format("(= (var %i) (+ (var %i) %s)", [i(V), i(X1), s(to_string(X2))]).
n_constraint_to_string(V, var(X1) ++ var(X2)) = format("(= (var %i) (+ (var %i) (var %i))", [i(V), i(X1), i(X2)]).
n_constraint_to_string(V, var(X1) -- var(X2)) = format("(= (var %i) (- (var %i) (var %i))", [i(V), i(X1), i(X2)]).
n_constraint_to_string(V, '=<'(X)) =            format("(<= (var %i) %s)", [i(V), s(to_string(X))]).

f_constraint_to_string(V, C) = n_constraint_to_string(V, C).
i_constraint_to_string(V, C) = n_constraint_to_string(V, C).
s_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %s)", [i(V), s(Val)]).

n_dump_store(Prefix, Cs) :-
  open("C:/Users/Jeff/AERA/replicode/AERA/runtime_out.txt", "a", Fd),
  format(Fd, "%s\n", [s(Prefix)]),
  _ = foldl(func(V, ValOrCSet, _) = 0 :-
      (ValOrCSet = val(Val) ->
        format(Fd, "  %s\n", [s(n_constraint_to_string(V, ':='(Val)))])
      ;
        (ValOrCSet = cs(CSet) ->
          _ = foldl(func(C, _) = 0 :-
              format(Fd, "  %s\n", [s(n_constraint_to_string(V, C))]),
            CSet, 0)
        ;
          true)),
    Cs, 0),

  close(Fd).
