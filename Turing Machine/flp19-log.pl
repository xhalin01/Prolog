 %Turingov stroj
 %xhalin01
 %Michael Halinar

:- dynamic rules/1.
:- dynamic tapes/1.

%Reads line from stdin, terminates on LF or EOF.
read_line(L,C) :-
	get_char(C),
	(isEOFEOL(C), L = [], !;
		read_line(LL,_),% atom_codes(C,[Cd]),
		[C|LL] = L).

%Tests if character is EOF or LF.
isEOFEOL(C) :-
	C == end_of_file;
	(char_code(C,Code), Code==10).

read_lines(Ls) :-
	read_line(L,C),
	
	( C == end_of_file, Ls = [] ;
	  read_lines(LLs), Ls = [L|LLs]
	).

%drops first N elements of list 
drop(0,LastElems,LastElems) :- !.
drop(N,[_|Tail],LastElems) :-
	N > 0,
	N2 is N  - 1,
	drop(N2,Tail,LastElems).

%takes first N elements of list
%-1 is correction for the left shift
take(-1,_,[]) :- !.
take(0, _, []) :- !.
take(N, [H|T1], [H|T2]) :-
	N > 0,
	N2 is N - 1,
	take(N2, T1, T2).

%converts string to list of chars
stringToList(Str, Chars) :-
    name(Str, X),
    maplist( numToChar, X, Chars ).
numToChar(Num, Char) :-
    name(Char, [Num]).

%make array of states from rules
makeStatesArray([],['S']).
makeStatesArray([Rule|Tail],Arr) :- 
	Rule=[_,_,State,_],
	makeStatesArray(Tail,Next),
	Arr=[State|Next].

%returns all rules from knowledge database
getAllRules(All) :-
	findall(R,rules(R),All).

%appends start state to the given input tape
makeStartingTape(LL,StartingTape) :-
	last(LL,X),
	append(['S'],X,StartingTape).

%asserts all states to the database
assertStates(_) :-
	getAllRules(AllRules),
	makeStatesArray(AllRules,StatesArray),
	sort(StatesArray,UniqueStates),
	assertz(allStates(UniqueStates)).

%function makes rules from input, and 
%puts them in knowledge dabase
makeRules([]).
makeRules([H|T]) :- 
	[St,_,Symb,_,Nxt,_,Act] = H,
	Rule=[St,Symb,Nxt,Act],
	assertz(rules(Rule)),
	makeRules(T).

%returns ActState and Symbol under head of TM
%acording to given tape [X|XS]
actState([X|XS],ActState,Symbol) :-
	allStates(StatesArray),
	member(X,StatesArray),
	ActState=X,    
	[Symbol|_]=XS
	;
	actState(XS,ActState,Symbol).

%finds next rule which wil be used
%for given ActState and Symbol under head
nextRule(ActState,Symbol,NextState,NextSymbol,Rules) :-
	Rules=[[St,Symb,NxtSt,NxtSymb]|_],
	ActState==St,Symbol==Symb,
 	NextState=NxtSt,
 	NextSymbol=NxtSymb
 	;
	Rules=[_|RestOfRules],
	nextRule(ActState,Symbol,NextState,NextSymbol,RestOfRules).

%Test if given state is final state
testFinalState(State) :-
	State=='F',true;
	false.

%rewrites symbol under head
%NewTape=Beg+Config+Rest
%Beg - beging of old tape, from start to the state symbol on old tape
%Config = NextState+NextSymbol
%Rest - rest of old tape from state to the end
rewrite(OldTape,ActState,NextState,NextSymbol,NewTape) :-
	%make parts of tape
	atomic_list_concat(OldTape,Concatenated),
	sub_string(Concatenated,Index,_,_,ActState),
	take(Index,OldTape,Tmp),
	atomic_list_concat(Tmp,Beg),
	drop(Index, OldTape,[_|[_|Tmp2]]),
	atomic_list_concat(Tmp2,Rest),

	%make new tape from all parts
	atom_concat(NextState,NextSymbol,Config),
	atom_concat(Beg,Config,TempTape),
	atom_concat(TempTape,Rest,NewTape).

%shifts head to the right
%NewTape = Beg2+ActState+Symbol+Rest2
%Beg2 - part of old tape from begining to the State
%ActState - new state
%ActSymbol - succesor char of State on old tape
%Rest2 - rest of the tape from Symbol on oldTape to the end 
shiftR(OldTape,ActState,ActSymbol,NextState,NewTape) :-
	%make parts of new tape
	atomic_list_concat(OldTape,Concatenated),
	sub_string(Concatenated,Index,_,_,ActState),
	(
		drop(Index,OldTape,TmpR),
		drop(2,TmpR,Rest),
		take(Index,OldTape,Beg),
		
		%make NewTape from its parts
		atomic_list_concat(Beg,Beg2),
		atom_concat(Beg2,ActSymbol,Tmp1),
		atom_concat(Tmp1,NextState,Tmp2),
		atomic_list_concat(Rest,Rest2),
		length(Rest,RestLen),
		(
			atom_concat(Tmp2,Rest2,NewTape),
			RestLen>1
			;
			atom_concat(Tmp2,Rest2,Tmp3),
			atom_concat(Tmp3,' ',NewTape) %end of tape, add blank
			)
	).
	
%shifts head to the left
%NewTape = Beg2+ActState+Symbol+Rest2
%Beg2 - part of old tape from begining to the State
%ActState - new state
%Symbol - predecessor char of State on old tape
%Rest2 - rest of the tape from Symbol on oldTape to the end 
shiftL(OldTape,ActState,NextState,NewTape) :-
	
		%make parts of new tape
		atomic_list_concat(OldTape,Concatenated),
		sub_string(Concatenated,Index,_,_,ActState),
		(
			Index==0,
			write('Abnormal stop - shifting to left not possible.'),nl,
			halt
			;
			N1 is Index - 1,
			take(N1,OldTape,Beg),
			nth0(N1,OldTape,Symbol),
			N2 is Index + 1,
			drop(N2,OldTape,Rest),

			%make new tape from all parts
			atomic_list_concat(Beg,Beg2),
			atom_concat(Beg2,NextState,Tmp1),
			atom_concat(Tmp1,Symbol,Tmp2),
			atomic_list_concat(Rest,Rest2),
			atom_concat(Tmp2,Rest2,NewTape)
		).
		

%executes given step of Turing machine
makeStep(OldTape,ActState,ActSymbol,NextState,NextSymbol,NewTape) :-
	NextSymbol=='R',
		shiftR(OldTape,ActState,ActSymbol,NextState,NewTape)
	;
	NextSymbol=='L',
		shiftL(OldTape,ActState,NextState,NewTape)
	;
	rewrite(OldTape,ActState,NextState,NextSymbol,NewTape).

%executes steps of Turing machine, acording to actual state
execute(Tape) :-
	actState(Tape,ActState,_),
	testFinalState(ActState)
	;
	actState(Tape,ActState,ActSymbol),	
	getAllRules(AllRules),
	nextRule(ActState,ActSymbol,NextState,NextSymbol,AllRules),
	makeStep(Tape,ActState,ActSymbol,NextState,NextSymbol,NewTape),
	stringToList(NewTape,TmpTape),
	execute(TmpTape),
	assertz(tapes(NewTape)).

%writes starting tape and sequence of
%tapes from TM
writeOutput(StartingTape) :-
	atomic_list_concat(StartingTape,ST),
	write(ST),nl,
	findall(T,tapes(T),Tapes),

	length(Tapes,Len),
	reorderElements(Tapes,Len,NewTapes),
	writeTapes(NewTapes).

%reverses elements in Tapes
reorderElements(_,0,[]).
reorderElements(Tapes,N,Reversed) :-
	length(Tapes,Len),
	N=<Len,
	nth1(N,Tapes,TmpTape),
	N2 is N - 1,
	reorderElements(Tapes,N2,Rest),
	Reversed=[TmpTape|Rest].

%write tapes one by one
writeTapes([]).
writeTapes([X|XS]) :-
	write(X),nl,
	writeTapes(XS).
	

main :-
		prompt(_, ''),
		%read input
		read_lines(Lines),
		%make rules
		append(Rules, [_], Lines),
		makeRules(Rules),
		%make and assert states array
		assertStates(_),
		%make starting tape
		makeStartingTape(Lines,StartingTape),
		%execute turing machine
		execute(StartingTape),
		%write output
		writeOutput(StartingTape),
		halt.