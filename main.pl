%--------------------------------------------------
% Load and Save from files
%--------------------------------------------------


%KB open and save

open_kb(Route,KB):-     
	open(Route,read,Stream),
	readclauses(Stream,X),
	close(Stream),
	atom_to_term(X,KB).

readclauses(InStream,W) :-
        get0(InStream,Char),
        checkCharAndReadRest(Char,Chars,InStream),
	atom_chars(W,Chars).

checkCharAndReadRest(-1,[],_) :- !.  % End of Stream	
checkCharAndReadRest(end_of_file,[],_) :- !.

checkCharAndReadRest(Char,[Char|Chars],InStream) :-
        get0(InStream,NextChar),
        checkCharAndReadRest(NextChar,Chars,InStream).

%compile an atom string of characters as a prolog term
atom_to_term(ATOM, TERM) :-
	atom(ATOM),
	atom_to_chars(ATOM,STR),
	atom_to_chars('.',PTO),
	append(STR,PTO,STR_PTO),
	read_from_chars(STR_PTO,TERM).

:- op(800,xfx,'=>').

%-------------------------------------------------
% Save KB
%-------------------------------------------------

save_kb(Name,KB):- 
        decompose_term(KB,NewKB),
	open(Name,write,Stream),
        format(Stream,'[',[]),
        format_kb(NewKB,Stream),
        format(Stream,']',[]),
	close(Stream).

decompose_term([],[]).
decompose_term([class(V,W,X,Y,Z)|More],[[V,W,X,Y,Z]|Tail]):-
         decompose_term(More,Tail).

format_kb([],_):-!.
format_kb([[V,W,[],[],[]]], Stream):-
         format(Stream,'~nclass(~q, ~q, [], [], [])~n',[V,W]),!.         
format_kb([[V,W,X,Y,[]]], Stream):-
         format(Stream,'~nclass(~q, ~q, ~n~5|~q, ~n~5|~q, ~n~5|[])~n',[V,W,X,Y]),!.
format_kb([[V,W,X,Y,Z]], Stream):-
         format(Stream,'~nclass(~q, ~q, ~n~5|~q, ~n~5|~q, ~n~5|[',[V,W,X,Y]),format_indv_kb(Z,Stream), format(Stream,'~n~5|]~n~5|)~n',[]),!.
format_kb([[V,W,[],[],[]]|More], Stream):-
         format(Stream,'~nclass(~q, ~q, [], [], []),~n',[V,W]),format_kb(More,Stream),!.
format_kb([[V,W,X,Y,[]]|More], Stream):-
         format(Stream,'~nclass(~q, ~q, ~n~5|~q, ~n~5|~q, ~n~5|[]~n~5|),~n',[V,W,X,Y]),format_kb(More,Stream),!.
format_kb([[V,W,X,Y,Z]|More], Stream):-
         format(Stream,'~nclass(~q, ~q, ~n~5|~q, ~n~5|~q, ~n~5|[',[V,W,X,Y]),format_indv_kb(Z,Stream), format(Stream,'~n~5|]~n~5|),~n',[]), format_kb(More,Stream),!.

format_indv_kb([],_):-!.
format_indv_kb([Obj],Stream):-
         format(Stream,'~n~10|~q',[Obj]),!.
format_indv_kb([Obj|More],Stream):-
         format(Stream,'~n~10|~q,',[Obj]),format_indv_kb(More,Stream),!.

%------------------------------
% Ejemplo:  
%------------------------------

%Cargar la base en una lista, imprimir la lista en consola y guardar todo en un nuevo archivo.
%No olvides poner las rutas correctas para localizar el archivo kb.txt en tu computadora!!!

ejemplo:-
	open_kb('kb.txt',KB),	write('KB: '),	write(KB),	save_kb('new_kb.txt',KB).

% (a) Extensión de una clase
% Predicado para encontrar la extensión de una clase y sus subclases.
class_extension(ClassName, KnowledgeBase, Extension) :-
    findall(InstanceID,
            (   member(class(ClassName, _, _, _, Instances), KnowledgeBase),
                member([id=>InstanceID|_], Instances)
            ),
            DirectInstances),
    findall(SubClassName,
            member(class(SubClassName, ClassName, _, _, _), KnowledgeBase),
            SubClasses),
    find_subclass_instances(SubClasses, KnowledgeBase, SubClassInstances),
    append(DirectInstances, SubClassInstances, Extension).

% Predicado auxiliar para encontrar las instancias de subclases.
find_subclass_instances([], _, []).
find_subclass_instances([SubClass|Rest], KnowledgeBase, AllInstances) :-
    class_extension(SubClass, KnowledgeBase, SubClassInstances),
    find_subclass_instances(Rest, KnowledgeBase, RestInstances),
    append(SubClassInstances, RestInstances, AllInstances).

%inciso b
% Predicado para buscar todas las instancias que tienen una propiedad específica y devolver sus valores en el formato Id:Value
property_extension(Property, KB, Result) :-
    findall(
        Id:Value, % Lista en formato Id:Value
        (
            member(class(_, _, Properties, _, Instances), KB),
            member([id=>Id | Attributes], Instances),
            (
                % Si la propiedad está en las propiedades de la clase o en los atributos de la instancia
                (member(Property, Properties), Value = yes)
                ;
                (member(Property=>Value, Attributes), Value = yes)
                ;
                Value = no % Si no se encuentra la propiedad, asignar 'no'
            )
        ),
        ResultUnfiltered
    ),
    % Filtrar duplicados dejando solo el primer resultado encontrado
    sort(ResultUnfiltered, Result).

%Inciso C)
% Predicado para verificar si una clase hereda una relación de sus superclases
inherits_relation(Relation, Class, KB) :-
    member(class(Class, SuperClass, _, _, _), KB),
    (relation_in_class(Relation, Class, KB); (SuperClass \= none, inherits_relation(Relation, SuperClass, KB))).

% Predicado auxiliar para verificar si una relación está en una clase
relation_in_class(Relation, Class, KB) :-
    member(class(Class, _, _, _, Instances), KB),
    member([id=>_, _, Relations], Instances),
    member(Relation=>_, Relations).

% Predicado para buscar la extensión de una relación en la base de conocimientos
relation_extension(Relation, KB, Result) :-
    findall(
        Id:Related, % Formato Id:Related
        (
            member(class(Class, _, _, _, Instances), KB),
            (
                % Verificar si la clase hereda la relación
                inherits_relation(Relation, Class, KB),
                member([id=>Id, _, Relations], Instances),
                member(Relation=>Related, Relations)
            )
        ),
        ResultUnfiltered
    ),
    % Eliminar duplicados dejando solo la primera ocurrencia
    sort(ResultUnfiltered, Result).

