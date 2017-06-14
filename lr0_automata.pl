/*
    "Programming Languages and Paradigms" course @ MIMUW
    Author: Michał Preibisch < mp347207@students.mimuw.edu.pl >
    Lecturer: dr Michał Skrzypczak < M.Skrzypczak@mimuw.edu.pl >

    File implementing Prolog module for creating LR(0)-type automata based
    on given context-free grammar.

    Two module's main functions are (further description below) :
        createLR(+Grammar, -Automata, -Info)
        accepts(+Automata, +Word)

    Implementation of LR(0) automata is inspired by wikipedia articles:
    https://pl.wikipedia.org/wiki/Parser_LR
    https://pl.wikipedia.org/wiki/Generowanie_parser%C3%B3w_LR

    Assumptions:
    - Representation of grammar is correct
    - Grammar does not containt non-terminal 'Z' and terminal '#'
    - Example grammar representation:
        gramatyka('E', [prod('E', [[nt('E'),+,nt('T')], [nt('T')]]),
                    prod('T', [[id], ['(', nt('E'), ')']]) ]).

    Warning: Phrase "dot" is used multiple times in this file. Explanation is in
    wikipedia articles for which links are provided above.
*/

:- use_module(library(lists)).

% Testing function for grammars in testing section
test(Q, A, I) :-
    grammar(Q, X),
    createLR(X, A, I),
    write(A).

% Creating LR automata with reduce_reduce check.
createLRReduce(gramatyka(St, Prods), Auto, Info) :-
    productions(gramatyka(St, Prods), Productions),
    starting_items_from_nts([St], Productions, S),
    closure(S, Productions, I0),
    create_states([I0], Productions, [], Trans),
    ( \+ check_reduce_reduce_conflict(Trans)
    ->  Info = reduce_reduce_conflict,
        Auto = null
    ;   Info = yes,
        Auto = auto(I0, Trans)
    ).

% Creating LR automata with shift_reduce check.
createLRShift(gramatyka(St, Prods), Auto, Info) :-
    productions(gramatyka(St, Prods), Productions),
    starting_items_from_nts([St], Productions, S),
    closure(S, Productions, I0),
    create_states([I0], Productions, [], Trans),
    (   \+ check_shift_reduce_conflict(Trans)
    ->  Info = shift_reduce_conflict,
        Auto = null
    ;   Info = yes,
        Auto = auto(I0, Trans)
    ).

createLR(gramatyka(St, Prods), Auto, Info) :-
    createLRShift(gramatyka(St, Prods), AutoX, InfoX),
    (   AutoX \= null
    ->  createLRReduce(gramatyka(St, Prods), Auto, Info)
    ;   Auto = AutoX,
        Info = InfoX
    ).

% Creating states - transitions between closed sets via symbol.
create_states([], _, X, X).
create_states(States, Prods, TrAcc, Res) :-
    States = [S | ST],
    elems_after_dot(S, Symbols),
    create_states_helper(S, Prods, Symbols, NewStates, NewTrans),
    (   \+ isSubset(NewTrans, TrAcc)
    ->  union(States, NewStates, NewS),
        union(NewTrans, TrAcc, NewTrAcc),
        create_states(NewS, Prods, NewTrAcc, Res)
    ;   create_states(ST, Prods, TrAcc, Res)
    ).

create_states_helper(_, _, [], [], []).
create_states_helper(S, Prods, [SH | ST], [R | NT], [trans(S, SH, R) | RT]) :-
    goto(S, Prods, SH, R),
    create_states_helper(S, Prods, ST, NT, RT).

% Res is a closure of and item set Items where Prods are all productions.
closure([], _,[]) :-
    !.
closure(Items, Prods, Res) :-
    non_terminals_after_dot(Items, NTs),
    starting_items_from_nts(NTs, Prods, NewI),
    union(Items, NewI, R),
    ( \+ isSubset(NewI, Items) % If intersection of Items and R is empty, then we didnt add any new Item
    ->  closure(R, Prods, Res)
    ;   Res = R
    ).

% Checking for reduce-reduce conflict in given transitions list.
% RR-conflict exists if there are multiple items with an ending dot within a single set.
check_reduce_reduce_conflict([]).
check_reduce_reduce_conflict([trans(I1, _, I2)| TT]) :-
    items_with_ending_dot(I1, L1),
    items_with_ending_dot(I2, L2),
    length(L1, X1),
    length(L2, X2),
    X1 < 2,
    X2 < 2,
    check_reduce_reduce_conflict(TT).

% Checks if list of transitions has a shift_reduce conflict.
% shift_reduce conflict exists if there is a transition from state S1 to S2,
% where S1 contains item ending with a dot - meaning there has to be reduce, but
% if such transition exists, then there is shift, which means a conflict.
check_shift_reduce_conflict([]).
check_shift_reduce_conflict([trans(I1, T, _) | TT]) :-
    items_with_ending_dot(I1, X),
    length(X, E),
    (   E > 0           % If there is and item with ending dot...
    -> \+ T = nt(_)     % ... there can't be a transition via terminal.
    ; check_shift_reduce_conflict(TT)
    ).

% starting_production(X)
starting_production(_, [], []).
starting_production(Symbol, [prod(Symbol, _) | _], prod(Symbol, _)) :-
    !.
starting_production(Symbol, [_ | PT], X) :-
    starting_production(Symbol, PT, X).


% R is list of items with a dot before X symbol, from a list of items S.
items_with_dot_before([], _, []).
items_with_dot_before([H | T], X, [H | RT]) :-
    H = item(_, P, J),
    elem_after_dot(P, J, X),
    items_with_dot_before(T, X, RT),
    !.
items_with_dot_before([_ | T], X, RT) :-
    items_with_dot_before(T, X, RT).

% Items with dot at the last index, such as  E -> w *  (where * is a dot).
items_with_ending_dot([], []).
items_with_ending_dot([item(X, P, I) | IT], [item(X, P, I) | RT]) :-
    length(P, I),
    items_with_ending_dot(IT, RT),
    !.
items_with_ending_dot([_ | IT], RT) :-
    items_with_ending_dot(IT, RT).

% Generates next closed set of items (R), from set S, via letter X.
goto([], _, _, []).
goto(S, Prods, X, R) :-
    items_with_dot_before(S, X, NI),
    moved_dot_list(NI, SM),
    closure(SM, Prods, R).

% Moves dot by one position if it's possible.
move_dot(item(X, P, J), item(X, P, K)) :-
    K is J + 1,
    length(P, L),
    K =< L.

moved_dot_list([], []).
moved_dot_list([H | T], [RH | RT]) :-
    move_dot(H, RH),
    moved_dot_list(T, RT), !.
moved_dot_list([_ | T], RT) :- moved_dot_list(T, RT).

% P is list of right-productions from non-terminal NT,
% where PS is list of all productions (terms "prod/3")
productions_from_nt(_, [], []).
productions_from_nt(NT, [PH | _], P) :-
    PH = prod(NT, P),
    !.
productions_from_nt(NT, [_| PH], P) :-
    productions_from_nt(NT, PH, P).

productions_from_nts([], _, []).
productions_from_nts([NT | NH], Prods, PS) :-
    productions_from_nt(NT, Prods, P1),
    productions_from_nts(NH, Prods, P2),
    union(P1, P2, PS).

% elem_after_dot(L, J, E) - E is first element after 'dot' in list L, where
% J is and index of a 'dot' in L.
elem_after_dot([], _, []).
elem_after_dot([H | _], 0, H) :-
    !.
elem_after_dot([_ | T], N, H) :-
    N > 0,
    N1 is N-1,
    elem_after_dot(T, N1 , H).

% elems_after_dot(L, E) - E are elements after dot from item's list L.
elems_after_dot([], []).
elems_after_dot([item(_, P, J) | T], E) :-
    elem_after_dot(P, J, E1),
    elems_after_dot(T, E2),
    (   E1 \= []
    -> union([E1], E2, E)
    ;   E = E2
    ).

% NTs is list of non_terminals after dot from items.
non_terminals_after_dot(Items, NTs) :-
    elems_after_dot(Items, N),
    non_terminals(N, NTs).

% Items are starting items generated from nonterminals NTs where Prods are all producitons
starting_items_from_nts([], _, []).
starting_items_from_nts([NT | NH], Prods, Items) :-
    productions_from_nt(NT, Prods, PS),
    starting_items_from_productions(NT, PS, I1),
    starting_items_from_nts(NH, Prods, I2),
    union(I1, I2, Items).

% I is starting item from a production NT -> R  (starting means 0 is dot's index)
starting_item_from_production(NT, R, I) :-
    items_from_rule(NT, R, 0, I),
    !.

starting_items_from_productionsH(_, [], []).
starting_items_from_productionsH(NT, [RH | RT], [IT | IH]) :-
    starting_item_from_production(NT, RH, IT),
    starting_items_from_productionsH(NT, RT, IH).

starting_items_from_productions(_, [], []).
starting_items_from_productions(NT, R, I) :-
  starting_items_from_productionsH(NT, R, IR),
  flatten_list(IR, I).

% P is list of productions of grammar named G, with an additional productions
% Z -> X#, where X is grammar's starting symbol
productions(gramatyka(S, PS), P) :-
    P = [prod('Z', [[nt(S), #]]) | PS]. % Adding production Z -> E

% S are symbols from production P
symbols_from_prod(P, S) :-
    symbols_from_prod(P, [], S).    % Helper function with accumulator
symbols_from_prod([], A, UniqA) :-
    unique(A, UniqA).
symbols_from_prod([H | T], A, R) :-
    append(H, A, NewAcc),
    symbols_from_prod(T, NewAcc, R).

% non_terminals_from_prod(P, Y) - Y is list of non-terminals from production P
non_terminals_from_prod(P, NT) :-
    symbols_from_prod(P, S),
    non_terminals(S, NT).

% non_terminals(X, Y) - Y is list of non-terminals from list X
non_terminals([], []).
non_terminals([nt(H) | T1], [H | T2]) :-
    non_terminals(T1, T2), !.
non_terminals([_|T1], T2) :- non_terminals(T1, T2).

% Items from a single rule (NT - nonterminal, R - right side of arrow).
% Example or rule: A -> bcA  (NT - nonterminal, R - right side of arrow)
% NT = 'E', R = [nt('E'), '+', nt('T')]
items_from_rule(NT, R, I) :-
    length(R, L),
    items_from_rule(NT, R, L, I),
    !.
items_from_rule(NT, R, 0, [item(NT, R, 0)]).
items_from_rule(NT, R, N, [item(NT, R, N) | T]) :-
    C is N-1,
    items_from_rule(NT, R, C, T).

% UniqL is unique sublist of L, with reversed order: [1, 2, 2, 3] -> [3, 2, 1]
unique(L, UniqL) :-
    unique(L, [], UniqL).   % Helper function with accumulator
unique([], UniqL, UniqL).
unique([H | L], A, UniqL) :-
    member(H, L),
    unique(L, A, UniqL), !.
unique([H | L], A, UniqL) :-
    unique(L, [H | A], UniqL).

% R is flattened list from first argument
flatten_list([], []).
flatten_list([H | T], R) :-
    flatten_list(T, T1),
    append(H, T1 , R).

intersection([], _, []).
intersection([H | T], L, [H | Res]) :-
    member(H, L),
    intersection(T, L, Res).

intersection([_ | T], L, Res) :-
    intersection(T, L, Res).

% union(A, B, C) when C is union of and B list  (w/o duplicates!)
union([], U, U).
union([H | T], L, U) :-
   member(H, L),
   !,
   union(T, L, U).
union([H | T], L, [H | U]) :-
   union(T, L, U).

subset([], []).
subset([E| T], [E| NT]):-
 subset(T, NT).
subset([_| T], NT):-
 subset(T, NT).

 isSubset([], _).
 isSubset([H | T],Y):-
     member(H, Y),
     select(H, Y, Z),
     isSubset(T, Z).
 equal(X, Y):-
     isSubset(X, Y),
     isSubset(Y, X).

/*  ============================================================
    ==================     TESTING GRAMMARS      ===============
    ============================================================    */

grammar(ex1, gramatyka('E',
                [prod('E', [[nt('E'), '+', nt('T')], [nt('T')]]),
                prod('T', [[id], ['(', nt('E'), ')']]) ])).

grammar(ex2, gramatyka('A', [prod('A', [[nt('A'), x], [x]])])).

grammar(ex3, gramatyka('A', [prod('A', [[x, nt('A')], [x]])])).

grammar(ex4, gramatyka('A',
                [prod('A', [[x, nt('B')], [nt('B'), y], []]),
                prod('B', [[]])])).

grammar(ex5, gramatyka('S',
                [prod('S', [[id], [nt('V'), ':=', nt('E')]]),
                prod('V', [[id], [id, '[', nt('E'), ']']]),
                prod('E', [[v]])])).

grammar(ex6, gramatyka('A',
                [prod('A', [[x], [nt('B'), nt('B')]]),
                prod('B', [[x]])])).

grammar(myex, gramatyka('E',  % E -> E * B ; E -> E + B ; E -> B
                [
                prod('E', [ [nt('E'), '+', nt('B')],[nt('E'), '*', nt('B')],[nt('B')] ]),
                prod('B', [['0'], ['1']])
                ]
            )
        ).  % B -> 0 ; B -> 1
