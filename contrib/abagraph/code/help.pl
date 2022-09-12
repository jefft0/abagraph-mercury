
help :-
 format('Strategies:~n', []),
 format('  turn choice:~n', []),
 format('     p - proponent priority [DEFAULT]~n', []),
 format('     o - opponent priority~n', []),
 format('     s - smallest number of sentences/justification-pairs first~n', []),
 format('  opponent sj-pair choice:~n', []),
 format('     n - newest~n', []),
 format('     o - oldest~n', []),
 format('     s - smallest set of pending (unmarked) sentences [DEFAULT]~n', []),
 format('     l - largest set of pending (unmarked) sentences~n', []),
 format('   lmb - lowest maximum \'branching\' coefficient~n', []),
 format('  sentence choice (proponent and opponent):~n', []),
 format('     n - newest~n', []),
 format('     o - oldest~n', []),
 format('     e - eager (choose an assumption if possible)~n', []),
 format('     p - patient (choose a non-assumption if poss.)  [DEFAULT (prop and opp)]~n', []),
 format('    pn - patient (patient, newest first, if poss.)  [DEFAULT (prop and opp)]~n', []),
 format('    be - sentence with smallest \'branching\' coefficient (eager)~n', []),
 format('    bp - sentence with smallest \'branching\' coefficient (patient)~n', []),
 format('  proponent rule choice:~n', []),
 format('     s - smallest rule body first~n', []),
 format('    l1 - look-ahead, 1-step  [DEFAULT]~n', []).