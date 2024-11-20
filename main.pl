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

%-----------------------------------
%-----------------------------------
%-----------------------------------
% Estoy agregando éstas 3 líneas para que corra el programa hoy 11/19/2024 a las 12:09 AM

:- discontiguous has_property/2.
:- discontiguous has_negated_property/2.
:- discontiguous has_relation/2.

%-----------------------------------
%-----------------------------------
%-----------------------------------

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



%-----------------------------------
%		Punto 1
%-----------------------------------
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
    % Buscar las instancias que tienen la propiedad mediante herencia
    findall(
        Id:Value, % Lista en formato Id:Value
        (
            % Recorre las clases en KB
            member(class(Class, ParentClass, _, _, Instances), KB),
            % Busca la propiedad en la jerarquía de clases (padre si es necesario)
            check_property_with_inheritance(Property, Class, ParentClass, KB, InitialValue),
            % Para cada instancia, asigna el valor heredado o el valor del atributo
            member([id=>Id, Attributes, _], Instances),
            % Desempaquetar los atributos para buscar la propiedad
            flatten(Attributes, FlatAttributes),
            % Sobrescribir el valor si la propiedad está definida en los atributos de la instancia
            (   member(Property=>AttributeValue, FlatAttributes) 
                -> Value = AttributeValue, write(Value),nl
            ;   Value = InitialValue
            )
        ),
        ResultUnfiltered
    ), filter_list(ResultUnfiltered, ResultUnSort),
    % Procesar ResultUnfiltered para eliminar duplicados: conservar el que tenga 'yes' si hay 'no' para el mismo Id
    remove_duplicates_with_preference(ResultUnSort, Result).

% Predicado auxiliar para verificar la propiedad en la clase actual o en la clase padre si es necesario
check_property_with_inheritance(Property, Class, ParentClass, KB, Value) :-
    % Verifica si la propiedad está en la lista de propiedades de la clase actual
    (   member(class(Class, _, Properties, _, _), KB),
        (   member([Property, 0], Properties) % Propiedad afirmativa en la clase actual
        ->  Value = yes
        ;   member([not(Property), 0], Properties) % Propiedad negada en la clase actual
        ->  Value = no
        ;   % Si no está en la clase actual y hay una clase padre, verifica en la clase padre
            ParentClass \= none,
            check_property_with_inheritance(Property, ParentClass, _, KB, Value)
        )
    ;   % Si no se encuentra la propiedad en ninguna parte de la jerarquía, asigna 'no'
        Value = no
    ).

% Predicado auxiliar para eliminar duplicados, manteniendo condiciones específicas
remove_duplicates_with_preference(Unfiltered, Filtered) :-
    % Agrupar por Id y seleccionar el valor preferido según las reglas
    findall(
        Id:FinalValue,
        (
            member(Id:_, Unfiltered), % Buscar cada Id único en Unfiltered
            findall(Value, member(Id:Value, Unfiltered), Values), % Filtrar todos los valores asociados a ese Id
            % Aplicar las reglas para seleccionar el valor final
            process_values(Values, FinalValue)
        ),
        FilteredUnsorted
    ),
    % Remover duplicados en caso de múltiples Id:Value idénticos
    sort(FilteredUnsorted, Filtered).

% Procesar la lista de valores asociada a un Id para seleccionar el valor final
process_values(Values, FinalValue) :-
    exclude(==(no), Values, NonNoValues), % Excluir 'no' de la lista
    exclude(==(yes), NonNoValues, FilteredValues), % Excluir 'yes' de la lista
    (
        FilteredValues \= [] % Si hay valores diferentes de 'yes' o 'no', seleccionarlos
        -> list_to_set(FilteredValues, [FinalValue|_]) % Eliminar duplicados, quedarse con el primero
        ; NonNoValues \= [] % Si no hay valores diferentes, pero hay 'yes', seleccionarlo
        -> FinalValue = yes
        ; FinalValue = no % Si todo es 'no', selecciona 'no'
    ).

% Predicado principal
filter_list(List, Result) :-
    (   has_other_values(List) ->
        exclude(yes_no_pair, List, Result)
    ;   Result = List
    ).

% Verifica si hay algún valor distinto de 'yes' o 'no'
has_other_values([]) :- false.
has_other_values([_:Value | Rest]) :-
    (   Value \= yes, Value \= no ->
        true
    ;   has_other_values(Rest)
    ).

% Predicado auxiliar para excluir pares con valores 'yes' o 'no'
yes_no_pair(_Key:Value) :-
    Value = yes;
    Value = no.

%Inciso C)

relation_extension(Relation, KB, Result) :-
    % Buscar las instancias que tienen la propiedad mediante herencia
    findall(
        Id:Value, % Lista en formato Id:Value
        (
            % Recorre las clases en KB
            member(class(Class, ParentClass, _, _, Instances), KB),
            decompose_relation_first(Relation, RelDecomp1),
            first_element(RelDecomp1, Head1),
            % Busca la propiedad en la jerarquía de clases (padre si es necesario)
            check_relation_with_inheritance_relation(Relation, Class, ParentClass, KB, InitialValue),
            % Para cada instancia, asigna el valor heredado o el valor del atributo
            member([id=>Id, _, Relations], Instances),
            (   
                Head1==amigo
                -> member([AmigoDe=>Amigo, _], Relations), Value=[Amigo]
            ;  
                Head1==not
                ->  member([not(AmigoDe=>Amigo), _], Relations), Value=[Amigo]
            ; 
                look_ids(InitialValue, KB, IdLook), Value = IdLook
            )
        ),
        ResultUnfiltered
    ), filter_non_empty_lists(ResultUnfiltered, ResultUnSort),
    % Procesar ResultUnfiltered para eliminar duplicados: conservar el que tenga 'yes' si hay 'no' para el mismo Id
   remove_duplicates_with_preference_relation(ResultUnSort, Result), !.


% Predicado auxiliar para buscar los IDs relacionados con una clase específica
look_ids(RelationValue, KB, IdLook) :-
    findall(
        Id,
        (  
            member(class(RelationValue, _, _, _, Instances), KB),
            extract_id(Instances, Id) % Extraer el ID usando un predicado auxiliar
        ),
        IdLook
    ).

% Caso base: se encuentra un elemento con la estructura [id=>Id, _, _]
extract_id([[id=>Id, _, _] | _], Id).

% Caso recursivo: se sigue buscando en la lista
extract_id([_ | Tail], Id) :- 
    extract_id(Tail, Id).


% Predicado auxiliar para verificar la propiedad en la clase actual o en la clase padre si es necesario
check_relation_with_inheritance_relation(Relation, Class, ParentClass, KB, Value) :-
    % Verifica si la propiedad está en la lista de propiedades de la clase actual
    (   member(class(Class, _, _, Relationes, _), KB),
        (  member([Relation=>RelationValue, 0], Relationes) % Propiedad afirmativa en la clase actual
        ->  Value = RelationValue
        ;   member([not(Relation=>RelationValue), 0], Relationes) % Propiedad negada en la clase actual
        ->  Value = RelationValue
        ;   % Si no está en la clase actual y hay una clase padre, verifica en la clase padre
            ParentClass \= none,
            check_relation_with_inheritance_relation(Relation, ParentClass, _, KB, Value)
        )
    ;   % Si no se encuentra la propiedad en ninguna parte de la jerarquía, asigna 'no'
        Value = []
    ).

% Predicado auxiliar para eliminar duplicados, manteniendo condiciones específicas
remove_duplicates_with_preference_relation(Unfiltered, Filtered) :-
    findall(Id:FinalValue, 
        (
            member(Id:_UnfilteredValues, Unfiltered), % Buscar cada Id único en Unfiltered
            findall(Value, member(Id:Value, Unfiltered), Values), % Filtrar todos los valores asociados a ese Id
            process_values_relation(Values, FinalValue) % Aplicar las reglas para seleccionar el valor final
        ),
        FilteredUnsorted),
    sort(FilteredUnsorted, Filtered). % Eliminar duplicados en caso de múltiples Id:Value idénticos
   
% Procesar la lista de valores asociada a un Id para seleccionar el valor final
process_values_relation(Values, FinalValue) :-
    exclude(==(no), Values, NonNoValues), % Excluir 'no' de la lista
    exclude(==(yes), NonNoValues, FilteredValues), % Excluir 'yes' de la lista
    (
        FilteredValues = [] % Si no quedan valores diferentes de 'no' o 'yes'
        -> FinalValue = [] % Retornar una lista vacía
        ; list_to_set(FilteredValues, [FinalValue|_]) % Si hay valores diferentes, eliminar duplicados y seleccionar el primero
    ).

% Predicado principal para filtrar elementos con listas vacías
filter_non_empty_lists([], []). % Caso base: lista vacía devuelve lista vacía
filter_non_empty_lists([Key:Value | Rest], Result) :-
    (   Value = [] -> % Si el valor es una lista vacía
        filter_non_empty_lists(Rest, Result) % No lo conservamos
    ;   Result = [Key:Value | FilteredRest], % Lo conservamos
        filter_non_empty_lists(Rest, FilteredRest)
    ).
% Predicado principal para descomponer la lista
decompose_relation(Term, Result) :-
    (   compound(Term), Term = not(Relation) -> % Verifica si es un término compuesto y coincide con not(Relation)
        decompose_relation(Relation, RelationDecomposed),
        append([not, '('], RelationDecomposed, Temp), % Agrega 'not(' al inicio
        append(Temp, [')'], Result)                  % Agrega ')' al final
    ;   compound(Term), Term = (Left => Right) ->   % Verifica si es una relación =>
        Result = [Left, '=>', Right]
    ;   % Caso base para otros términos (no relaciones complejas)
        Result = [Term]
    ).

% Predicado principal para descomponer la lista
decompose_relation_first(Term, Result) :-
    (   Term = not(Relation) ->
        Result = [not, '(', Relation, ')']
    ;   % Caso base para otros términos (no relaciones complejas)
        Result = [Term]
    ).

first_element([Head | _], Head).

%inciso d)
% Predicado principal para encontrar todas las clases a las que pertenece un objeto
classes_of_individual(Object, KB, Classes) :-
    findall(
        Class,
        (
            member(class(Class, _, _, _, Instances), KB),
            member([id=>Object | _], Instances)
        ),
        DirectClasses
    ),
    find_superclasses_list(DirectClasses, KB, AllClasses),
    % Eliminar duplicados y devolver la lista final
    sort(AllClasses, Classes).

% Predicado auxiliar para encontrar las superclases de una lista de clases
find_superclasses_list([], _, []).
find_superclasses_list([Class | Rest], KB, [Class | SuperClasses]) :-
    find_superclasses(Class, KB, ClassSuperClasses),
    find_superclasses_list(Rest, KB, RestSuperClasses),
    append(ClassSuperClasses, RestSuperClasses, SuperClasses),
    !. % Corte para evitar que siga buscando soluciones

% Predicado auxiliar para encontrar las superclases de una clase de forma recursiva
find_superclasses(Class, KB, SuperClasses) :-
    member(class(Class, SuperClass, _, _, _), KB),
    SuperClass \= none,
    find_superclasses(SuperClass, KB, ParentSuperClasses),
    SuperClasses = [SuperClass | ParentSuperClasses].

find_superclasses(_, _, []).

%inciso e)
% Obtener todas las propiedades de un individuo
properties_of_individual(Individual, KB, Result) :-
    member(class(ClassName, ClassParent, _, _, _), KB),
    % Buscar la clase que contiene al individuo
    member(class(ClassName, _, _, _, Instances), KB),
    % Verificar si el individuo tiene una lista de propiedades definida
    member([id=>Individual, IndividualProps,_], Instances),
    (
        % Caso 1: El individuo tiene una lista de propiedades definida
        IndividualProps \= [] ->
        findall(Prop, member([Prop, _], IndividualProps), ResultF)
    ), class_properties_indi(ClassName, ClassParent, KB, ResultF, Result1), 
    clean_properties(Result1, Result),!.
    
% Obtener todas las propiedades de una clase (incluidas las de las superclases)
class_properties_indi(ClassName, SuperClass, KB, ResultF, Result) :-
    % Encontrar la definición de la clase
    member(class(ClassName, SuperClass, ClassProps, _, _), KB),
    write(ClassProps), 
    (
        ClassProps \= [] -> append(ClassProps, ResultF, Result)
        %write(CurrentProps), nl
        ;
        % Extraer propiedades de la clase actual
        findall(Prop, member([Prop, _], ClassProps), CurrentProps),
        write(CurrentProps),
        % Recursivamente obtener las propiedades de las superclases
        ->(
            SuperClass \= none ->
            class_properties_indi(SuperClass, _, KB, ResultF, SuperProps);
            SuperProps = []
        )
    ).
    % Combinar propiedades actuales con las heredadas
   
% Predicado para limpiar la lista de propiedades y eliminar los números
clean_properties([], []). % Caso base: lista vacía
clean_properties([[Prop, _] | Tail], [Prop | CleanTail]) :- % Eliminar números de cada propiedad
    clean_properties(Tail, CleanTail).
clean_properties([Prop | Tail], [Prop | CleanTail]) :- % Si ya es una propiedad limpia, conservarla
    clean_properties(Tail, CleanTail).

% Obtener todas las propiedades de una clase (incluidas las de las superclases)
class_properties(ClassName, KB, Result) :-
    % Buscar la clase actual
    member(class(ClassName, SuperClass, ClassProps, _, _), KB),
    % Extraer propiedades de la clase actual
    findall(Prop, member([Prop, _], ClassProps), CurrentProps),
    (
        % Caso 1: La clase tiene una superclase
        SuperClass \= none ->
        class_properties(SuperClass, KB, SuperProps),
        append(SuperProps, CurrentProps, CombinedProps),
        % Quitar números de las propiedades combinadas
        clean_properties(CombinedProps, Result)
    ;
        % Caso 2: No hay superclase, devolver solo las propiedades actuales
        clean_properties(CurrentProps, Result)
    ), !.


%inciso f)
% Regla para encontrar las relaciones específicas de un individuo en la base de conocimientos.
relations_of_individual(Individual, KB, Relations) :-
    findall(
        Property,
        (
            member(class(_, _, _, _, Properties), KB),
            member([id=>Individual, _, Props], Properties),
            member([Property, _], Props),
            append(Props, InitialValue, Result)
        ),
        RelationsUnfiltered
    ),
    sort(RelationsUnfiltered, Relations).

% Predicado principal para encontrar todas las clases de un individuo
class_of_individual(Individual, KB, Classes) :-
    % Encuentra la clase del individuo
    member(class(Class, _, _, _, Instances), KB),
    member(id=>Individual, Instances),
    % Encuentra todas las clases ascendentes (herencia)
    find_all_classes(Class, KB, Classes).

% Predicado recursivo para encontrar todas las clases heredadas
find_all_classes(Class, KB, [Class|ParentClasses]) :-
    member(class(Class, ParentClass, _, _, _), KB),
    ParentClass \= none, % Si no es la clase raíz
    find_all_classes(ParentClass, KB, ParentClasses).
find_all_classes(Class, KB, [Class]) :-
    member(class(Class, none, _, _, _), KB). % Clase raíz (sin padres)



% Predicado para encontrar todas las relaciones de una clase
% Define la regla para encontrar todas las subclases de una clase dada.
class_relations(Class, KB, Relations) :-
    findall(
        Subclass,
        (member(class(Subclass, Class, _, _, _), KB)),
        DirectRelations
    ),
    findall(
        SubSubclass,
        (member(class(SubSubclass, SubclassRelation, _, _, _), KB), 
         member(class(SubclassRelation, Class, _, _, _), KB)),
        IndirectRelations
    ),
    append(DirectRelations, IndirectRelations, Relations).


% Predicado auxiliar para encontrar relaciones heredadas de una lista de clases
find_inherited_relations_f([], _, []).
find_inherited_relations_f([Class | Rest], KB, Relations) :-
    class_relations(Class, KB, ClassRelations),
    find_inherited_relations_f(Rest, KB, RestRelations),
    append(ClassRelations, RestRelations, Relations).

% Predicado para encontrar todas las clases a las que pertenece un objeto
classes_of_individual_f(Object, KB, Classes) :-
    findall(
        Class,
        (
            member(class(Class, _, _, _, Instances), KB),
            member([id=>Object | _], Instances)
        ),
        DirectClasses
    ),
    find_superclasses_list_f(DirectClasses, KB, AllClasses),
    sort(AllClasses, Classes). % Elimina duplicados y ordena

% Predicado auxiliar para encontrar las superclases de una lista de clases
find_superclasses_list_f([], _, []).
find_superclasses_list_f([Class | Rest], KB, [Class | SuperClasses]) :-
    find_superclasses_f(Class, KB, ClassSuperClasses),
    find_superclasses_list_f(Rest, KB, RestSuperClasses),
    append(ClassSuperClasses, RestSuperClasses, SuperClasses),
    !. % Corte para evitar seguir buscando

% Predicado auxiliar para encontrar las superclases de una clase de forma recursiva
find_superclasses_f(Class, KB, SuperClasses) :-
    member(class(Class, SuperClass, _, _, _), KB),
    SuperClass \= none,
    find_superclasses_f(SuperClass, KB, ParentSuperClasses),
    SuperClasses = [SuperClass | ParentSuperClasses],
    !. % Corte para evitar seguir buscando

find_superclasses_f(_, _, []).

%-----------------------------------
%-----------------------------------
%-----------------------------------
% % Desde aqui estoy agregando hoy 11/19/2024 a las 12:09 AM

%-----------------------------------
%               Punto 2
%-----------------------------------
%--------------------------------------------------
% Añadir Clases y Objetos
%--------------------------------------------------

% Añadir una clase
add_class(ClaseNombre, ClaseMadre, KB, NuevaKB) :-
    (member(class(ClaseNombre, _, _, _, _), KB) ->
        write('La clase ya existe y no se puede duplicar.'), nl,
        NuevaKB = KB
    ;
        append(KB, [class(ClaseNombre, ClaseMadre, [], [], [])], NuevaKB),
        write('Clase agregada exitosamente.'), nl

    ).

% Añadir un objeto
add_object(NombreObjeto, ClaseNombre, KB, NuevaKB) :-
    (member(class(ClaseNombre, ClaseMadre, Props, Relaciones, Objetos), KB) ->
        select(class(ClaseNombre, ClaseMadre, Props, Relaciones, Objetos), KB, TempKB),
        append(Objetos, [[id=>NombreObjeto, [], []]], NuevaListaObjetos),
        append(TempKB, [class(ClaseNombre, ClaseMadre, Props, Relaciones, NuevaListaObjetos)], NuevaKB),
        write('Objeto agregado exitosamente.'), nl
    ;
        write('La clase especificada no existe.'), nl,


        NuevaKB = KB
    ).

%--------------------------------------------------
% Añadir Propiedades
%--------------------------------------------------

% Añadir una propiedad a una clase
add_class_property(ClaseNombre, Propiedad, Valor, KB, NuevaKB) :-
    (select(class(ClaseNombre, ClaseMadre, Props, Relaciones, Objetos), KB, TempKB) ->
        append(Props, [[Propiedad => Valor]], NuevasProps),
        append(TempKB, [class(ClaseNombre, ClaseMadre, NuevasProps, Relaciones, Objetos)], NuevaKB),
        write('Propiedad agregada a la clase exitosamente.'), nl
    ;
        write('La clase especificada no existe.'), nl,
        NuevaKB = KB
    ).


% Añadir una propiedad a un objeto
add_object_property(ObjectName, Property, Value, KB, NewKB) :-
    maplist(
        ({ObjectName, Property, Value}/[Class, UpdatedClass]>>
            (Class = class(ClassName, Parent, Props, Rels, Objects) ->
                maplist(
                    ({ObjectName, Property, Value}/[Obj, UpdatedObj]>>
                        (Obj = [id=>ObjectName, ObjProps, ObjRels] ->
                            (   \+ member([Property=>_], ObjProps), % Asegurar que no exista la propiedad
                                append(ObjProps, [[Property=>Value]], UpdatedProps),
                                UpdatedObj = [id=>ObjectName, UpdatedProps, ObjRels]
                            )
                        ;
                            UpdatedObj = Obj
                        )
                    ),
                    Objects, UpdatedObjects),
                UpdatedClass = class(ClassName, Parent, Props, Rels, UpdatedObjects)
            ;
                UpdatedClass = Class
            )
        ),
        KB, NewKB
    ),
    write('Propiedad agregada al objeto exitosamente.'), nl.




%--------------------------------------------------
% Añadir Relaciones
%--------------------------------------------------

% Añadir una relación a una clase
add_class_relation(ClaseNombre, Relacion, ClasesRelacionadas, KB, NuevaKB) :-
    (select(class(ClaseNombre, ClaseMadre, Props, Relaciones, Objetos), KB, TempKB) ->
        append(Relaciones, [[Relacion => ClasesRelacionadas]], NuevasRelaciones),
        append(TempKB, [class(ClaseNombre, ClaseMadre, Props, NuevasRelaciones, Objetos)], NuevaKB),
        write('Relación agregada a la clase exitosamente.'), nl
    ;
        write('La clase especificada no existe.'), nl,
        NuevaKB = KB
    ).


% Añadir una relación a un objeto
add_object_relation(ObjectName, Relation, RelatedObjects, KB, NewKB) :-
    maplist(
        ({ObjectName, Relation, RelatedObjects}/[Class, UpdatedClass]>>
            (Class = class(ClassName, Parent, Props, Rels, Objects) ->
                maplist(
                    ({ObjectName, Relation, RelatedObjects}/[Obj, UpdatedObj]>>
                        (Obj = [id=>ObjectName, ObjProps, ObjRels] ->
                            (   \+ member([Relation=>_], ObjRels), % Asegurar que no exista la relación
                                append(ObjRels, [[Relation=>RelatedObjects]], UpdatedRels),
                                UpdatedObj = [id=>ObjectName, ObjProps, UpdatedRels]
                            )
                        ;
                            UpdatedObj = Obj
                        )
                    ),
                    Objects, UpdatedObjects),
                UpdatedClass = class(ClassName, Parent, Props, Rels, UpdatedObjects)
            ;
                UpdatedClass = Class
            )
        ),
        KB, NewKB
    ),
    write('Relación agregada al objeto exitosamente.'), nl.



% Punto 3
% Crear predicados para eliminar

% Elimina una clase y sus objetos de la base de conocimientos.
rm_class(ClassName, KB, NewKB) :-
    exclude(is_class(ClassName), KB, NewKB).

is_class(ClassName, class(ClassName, _, _, _, _)).

% Elimina un objeto específico de una clase.

rm_object(ObjectName, KB, NewKB) :-
    maplist(remove_object_from_class(ObjectName), KB, NewKB).

remove_object_from_class(ObjectName, class(ClassName, Parent, Props, Rels, Objects),
                         class(ClassName, Parent, Props, Rels, UpdatedObjects)) :-
    exclude(has_object_id(ObjectName), Objects, UpdatedObjects).

% Si la clase no contiene el objeto, no se modifica
remove_object_from_class(_, Class, Class).

% Verifica si un objeto tiene el identificador dado
has_object_id(ObjectName, [id=>ObjectName | _]).


% Elimina una propiedad específica de una clase.

rm_class_property(ClassName, Property, KB, NewKB) :-
    maplist(remove_class_property(ClassName, Property), KB, NewKB).

remove_class_property(ClassName, Property, class(ClassName, Parent, Props, Rels, Objects),
                      class(ClassName, Parent, UpdatedProps, Rels, Objects)) :-
    exclude(has_property(Property), Props, UpdatedProps).

remove_class_property(_, _, Class, Class). % Si no es la clase objetivo, no se modifica.

has_property(Property, [Property=>_]).


% Elimina una propiedad específica de un objeto dentro de una clase

rm_object_property(ObjectName, Property, KB, NewKB) :-
    maplist(remove_object_property_from_class(ObjectName, Property), KB, NewKB).

remove_object_property_from_class(ObjectName, Property,
                                   class(ClassName, Parent, Props, Rels, Objects),
                                   class(ClassName, Parent, Props, Rels, UpdatedObjects)) :-
    maplist(remove_property_from_object(ObjectName, Property), Objects, UpdatedObjects).

remove_property_from_object(ObjectName, Property, [id=>ObjectName, Props, Rels],
                            [id=>ObjectName, UpdatedProps, Rels]) :-
    exclude(has_property(Property), Props, UpdatedProps).

remove_property_from_object(_, _, Object, Object). % Si no es el objeto, no se modifica.


%  Elimina una relación específica de una clase.

rm_class_relation(ClassName, Relation, KB, NewKB) :-
    maplist(remove_class_relation(ClassName, Relation), KB, NewKB).

remove_class_relation(ClassName, Relation, class(ClassName, Parent, Props, Rels, Objects),
                      class(ClassName, Parent, Props, UpdatedRels, Objects)) :-
    exclude(has_relation(Relation), Rels, UpdatedRels).

remove_class_relation(_, _, Class, Class). % Si no es la clase objetivo, no se modifica.

has_relation(Relation, [Relation=>_]).


% Elimina una relación específica de un objeto dentro de una clase.

rm_object_relation(ObjectName, Relation, KB, NewKB) :-
    maplist(remove_object_relation_from_class(ObjectName, Relation), KB, NewKB).

remove_object_relation_from_class(ObjectName, Relation,
                                   class(ClassName, Parent, Props, Rels, Objects),
                                   class(ClassName, Parent, Props, Rels, UpdatedObjects)) :-
    maplist(remove_relation_from_object(ObjectName, Relation), Objects, UpdatedObjects).

remove_relation_from_object(ObjectName, Relation, [id=>ObjectName, Props, Rels],
                            [id=>ObjectName, Props, UpdatedRels]) :-
    exclude(has_relation(Relation), Rels, UpdatedRels).

remove_relation_from_object(_, _, Object, Object). % Si no es el objeto, no se modifica.



%--------------------------------------------------
% Punto 4: Cambiar valores en clases y objetos
%--------------------------------------------------


% Cambiar el nombre de una clase
change_class_name(OldName, NewName, KB, NewKB) :-
    maplist(update_class_name(OldName, NewName), KB, IntermediateKB),
    update_parent_references(OldName, NewName, IntermediateKB, NewKB).

% Actualizar el nombre de la clase en su definición
update_class_name(OldName, NewName, class(OldName, Parent, Props, Rels, Objects),
                  class(NewName, Parent, Props, Rels, Objects)) :- !.
update_class_name(_, _, Class, Class). % No modificar si no es la clase objetivo.

% Actualizar referencias a la clase como clase padre
update_parent_references(_, _, [], []).
update_parent_references(OldName, NewName, [class(Name, OldName, Props, Rels, Objects)|Rest], [class(Name, NewName, Props, Rels, Objects)|UpdatedRest]) :-
    update_parent_references(OldName, NewName, Rest, UpdatedRest).
update_parent_references(OldName, NewName, [Class|Rest], [Class|UpdatedRest]) :-
    update_parent_references(OldName, NewName, Rest, UpdatedRest).




% Cambiar el nombre de un objeto
change_object_name(OldName, NewName, KB, NewKB) :-
    maplist(update_object_name(OldName, NewName), KB, NewKB).

% Actualizar el nombre del objeto dentro de su clase
update_object_name(OldName, NewName, class(Name, Parent, Props, Rels, Objects),
                   class(Name, Parent, Props, Rels, UpdatedObjects)) :-
    maplist(rename_object(OldName, NewName), Objects, UpdatedObjects).
update_object_name(_, _, Class, Class). % No modificar si no es la clase objetivo.

% Renombrar el objeto en la lista de objetos
rename_object(OldName, NewName, [id=>OldName, Props, Rels], [id=>NewName, Props, Rels]) :- !.
rename_object(_, _, Object, Object). % No modificar si no es el objeto objetivo.



% Cambiar el valor de una propiedad específica de una clase
change_value_class_property(ClassName, Property, NewValue, KB, NewKB) :-
    maplist(update_class_property(ClassName, Property, NewValue), KB, NewKB).

update_class_property(ClassName, Property, NewValue,
                      class(ClassName, Parent, Props, Rels, Objects),
                      class(ClassName, Parent, UpdatedProps, Rels, Objects)) :-
    % Eliminar cualquier conflicto previo (not(Property) o Property=>_)
    exclude(has_property(Property), Props, CleanedProps),
    exclude(has_negated_property(Property), CleanedProps, FilteredProps),
    % Añadir la nueva propiedad
    append(FilteredProps, [[Property=>NewValue]], UpdatedProps).

update_class_property(_, _, _, Class, Class). % No modificar si no es la clase objetivo.

% Verificar si la propiedad ya existe
has_property(Property, [Property|_]).
has_property(Property, [Property=>_]).

% Verificar si la negación de la propiedad existe
has_negated_property(Property, [not(Property)|_]).






% Cambiar el valor de una propiedad específica de un objeto
change_value_object_property(ObjectName, Property, NewValue, KB, NewKB) :-
    maplist(
        ({ObjectName, Property, NewValue}/[Class, UpdatedClass]>>
            (Class = class(ClassName, Parent, Props, Rels, Objects) ->
                % Actualizar la propiedad en el objeto correspondiente
                maplist(
                    ({ObjectName, Property, NewValue}/[Obj, UpdatedObj]>>
                        (Obj = [id=>ObjectName, ObjProps, ObjRels] ->
                            % Eliminar cualquier conflicto previo (Property=>_ o not(Property))
                            exclude(has_property(Property), ObjProps, FilteredProps),
                            exclude(has_negated_property(Property), FilteredProps, CleanedProps),
                            % Añadir la nueva propiedad
                            append(CleanedProps, [[Property=>NewValue]], UpdatedProps),
                            UpdatedObj = [id=>ObjectName, UpdatedProps, ObjRels]
                        ;
                            UpdatedObj = Obj
                        )
                    ),
                    Objects, UpdatedObjects),
                UpdatedClass = class(ClassName, Parent, Props, Rels, UpdatedObjects)
            ;
                UpdatedClass = Class
            )
        ),
        KB, NewKB
    ).

% Verificar si la propiedad ya existe
has_property(Property, [Property=>_]).

% Verificar si la negación de la propiedad existe
has_negated_property(Property, [not(Property)|_]).




% Cambiar con quién mantiene una relación específica una clase
change_value_class_relation(ClassName, Relation, NewRelatedClasses, KB, NewKB) :-
    maplist(update_class_relation(ClassName, Relation, NewRelatedClasses), KB, NewKB).


% Actualizar la relación específica de una clase
update_class_relation(ClassName, Relation, NewRelatedClasses,
                      class(ClassName, Parent, Props, Rels, Objects),
                      class(ClassName, Parent, Props, UpdatedRels, Objects)) :-
    % Eliminar la relación existente
    exclude(has_relation(Relation), Rels, FilteredRels),
    % Añadir la nueva relación
    append(FilteredRels, [[Relation=>NewRelatedClasses]], UpdatedRels).

update_class_relation(_, _, _, Class, Class). % No modificar si no es la clase objetivo.

% Verificar si una relación específica existe
has_relation(Relation, [Relation=>_]).






% Cambiar con quién mantiene una relación específica un objeto
change_value_object_relation(ObjectName, Relation, NewRelatedObjects, KB, NewKB) :-
    maplist(update_object_relation(ObjectName, Relation, NewRelatedObjects), KB, NewKB).

update_object_relation(ObjectName, Relation, NewRelatedObjects,
                       class(Name, Parent, Props, Rels, Objects),
                       class(Name, Parent, Props, Rels, UpdatedObjects)) :-
    maplist(update_object_specific_relation(ObjectName, Relation, NewRelatedObjects), Objects, UpdatedObjects).

update_object_specific_relation(ObjectName, Relation, NewRelatedObjects,
                                [id => ObjectName, Props, Rels],
                                [id => ObjectName, Props, UpdatedRels]) :-
    % Eliminar cualquier relación conflictiva
    exclude(has_relation(Relation), Rels, FilteredRels),
    % Añadir la nueva relación
    append(FilteredRels, [[Relation => NewRelatedObjects]], UpdatedRels).

update_object_specific_relation(_, _, _, Object, Object). % No modificar si no es el objeto objetivo.

% Verificar si la relación ya existe
has_relation(Relation, [Relation => _]).



% Obtener el valor de una propiedad en una clase
class_property_value(ClassName, Property, KB, Value) :-
    % Verificar si la propiedad está definida directamente o por herencia
    (   find_property_in_class(ClassName, Property, KB, DirectValue)
    ->  Value = DirectValue
    ;   Value = unknown % Si no se encuentra la propiedad, retorna 'unknown'
    ).

% Buscar la propiedad en la clase actual o en sus superclases
find_property_in_class(ClassName, Property, KB, Value) :-
    member(class(ClassName, ParentClass, Properties, _, _), KB),
    % Verificar si la propiedad está definida directamente en la clase actual
    (   member([Property, 0], Properties)
    ->  Value = yes
    ;   member([not(Property), 0], Properties)
    ->  Value = no
    ;   % Si no está en la clase actual, buscar en la superclase
        ParentClass \= none,
        find_property_in_class(ParentClass, Property, KB, Value)
    ).


% Obtener el valor de una propiedad de un objeto
object_property_value(ObjectName, Property, KB, Value) :-
    member(class(_, _, _, _, Objects), KB),
    member([id=>ObjectName, ObjectProps, _], Objects),
    (
        % Formato Propiedad=>Valor
        member([Property=>PropValue, _], ObjectProps)
    ->  Value = PropValue
    ;   % Formato Propiedad, Flag
        member([Property, Flag], ObjectProps),
        Value = Flag
    ;   % No encontrada
        Value = unknown
    ).

%-----------------------------------
%-----------------------------------
%-----------------------------------
% Hasta aqui agregué hoy 11/19/2024 a las 12:09 AM


   % Predicado para imprimir la información de una clase específica
imprimir_clase(class(NombreClase, ClasePadre, Propiedades, Restricciones, Objetos)) :-
    format('Clase actual: ~w~n', [NombreClase]),
    format('Clase padre: ~w~n', [ClasePadre]),
    format('Propiedades: ~w~n', [Propiedades]),
    format('Restricciones: ~w~n', [Restricciones]),
    format('Objetos: ~w~n', [Objetos]),
    nl.

% Predicado para imprimir todas las clases desde la lista KB
imprimir_clases(KB) :-
    member(Class, KB),
    imprimir_clase(Class),
    fail.
imprimir_clases(_).


% Predicado para obtener las propiedades y restricciones heredadas
obtener_propiedades_restricciones(NombreClase, Propiedades, Restricciones, KB) :-
    obtener_propiedades_ancestros(NombreClase, KB, PropiedadesHeredadas, RestriccionesHeredadas),
    member(class(NombreClase, _, PropiedadesClase, RestriccionesClase, _), KB),
    append(PropiedadesHeredadas, PropiedadesClase, Propiedades),
    append(RestriccionesHeredadas, RestriccionesClase, Restricciones).

% Predicado auxiliar para obtener propiedades y restricciones de todos los ancestros
obtener_propiedades_ancestros(NombreClase, KB, Propiedades, Restricciones) :-
    member(class(NombreClase, ClasePadre, PropiedadesClase, RestriccionesClase, _), KB),
    ClasePadre \= none,  % Verifica que la clase tenga un padre
    obtener_propiedades_ancestros(ClasePadre, KB, PropiedadesPadre, RestriccionesPadre),
    append(PropiedadesPadre, PropiedadesClase, Propiedades),
    append(RestriccionesPadre, RestriccionesClase, Restricciones).

obtener_propiedades_ancestros(NombreClase, KB, [], []) :-
    member(class(NombreClase, none, _, _, _), KB).  % Caso base: sin padre (clase raíz)
