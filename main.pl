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
    ),
    % Procesar ResultUnfiltered para eliminar duplicados: conservar el que tenga 'yes' si hay 'no' para el mismo Id
    remove_duplicates_with_preference(ResultUnfiltered, Result).

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


%Inciso C)

relation_extension(Relation, KB, Result) :-
    % Buscar las instancias que tienen la propiedad mediante herencia
    findall(
        Id:Value, % Lista en formato Id:Value
        (
            % Recorre las clases en KB
            member(class(Class, ParentClass, _, _, Instances), KB),
            % Busca la propiedad en la jerarquía de clases (padre si es necesario)
            check_relation_with_inheritance_relation(Relation, Class, ParentClass, KB, InitialValue),
            % Para cada instancia, asigna el valor heredado o el valor del atributo
            member([id=>Id, _, Relations], Instances),
            % Desempaquetar los atributos para buscar la propiedad
            flatten(Relations, FlatRelations),
            % Sobrescribir el valor si la propiedad está definida en los atributos de la instancia
            (   member(Relation=>RelationValue, FlatRelations) 
                -> Value = RelationValue, write(Value), nl
            ;  
                member(not(Relation=>RelationValue), FlatRelations) 
                -> Value = RelationValue
            ; 
            Value = [InitialValue]
            )
        ),
        ResultUnfiltered
    ),
    % Procesar ResultUnfiltered para eliminar duplicados: conservar el que tenga 'yes' si hay 'no' para el mismo Id
   remove_duplicates_with_preference_relation(ResultUnfiltered, Result), !.


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
        ->  look_ids(RelationValue, KB, IdLook),
            Value = IdLook, write(Value)
        ;   member([not(Relation=>RelationValue), 0], Relationes) % Propiedad negada en la clase actual
        ->  look_ids(RelationValue, KB, IdLook),
            Value = IdLook, write(Value)
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
% Predicado principal para encontrar todas las propiedades de un objeto
properties_of_individual(Object, KB, Properties) :-
    findall(
        Property:Value,
        (
            member(class(_, _, _, _, Instances), KB),
            member([id=>Object, Attributes, _], Instances),
            member(Property=>Value, Attributes),
            ! % Corte para detener la búsqueda de más soluciones una vez encontrada una propiedad
        ),
        DirectProperties
    ),
    classes_of_individual_e(Object, KB, Classes),
    find_inherited_properties(Classes, KB, InheritedProperties),
    append(DirectProperties, InheritedProperties, AllProperties),
    sort(AllProperties, Properties), % Elimina duplicados y ordena
    !. % Corte para detener la búsqueda después de obtener el resultado final

% Predicado para encontrar todas las propiedades de una clase
class_properties(Class, KB, Properties) :-
    findall(
        Property,
        (
            member(class(Class, _, ClassProperties, _, _), KB),
            member(Property, ClassProperties),
            ! % Corte para detener la búsqueda de más soluciones
        ),
        DirectProperties
    ),
    find_superclasses_e(Class, KB, SuperClasses),
    find_inherited_properties(SuperClasses, KB, InheritedProperties),
    append(DirectProperties, InheritedProperties, AllProperties),
    sort(AllProperties, Properties), % Elimina duplicados y ordena
    !. % Corte para finalizar la búsqueda

% Predicado auxiliar para encontrar las propiedades heredadas de una lista de clases
find_inherited_properties([], _, []).
find_inherited_properties([Class | Rest], KB, Properties) :-
    class_properties(Class, KB, ClassProperties),
    find_inherited_properties(Rest, KB, RestProperties),
    append(ClassProperties, RestProperties, Properties),
    !. % Corte para evitar seguir buscando

% Predicado para encontrar todas las clases a las que pertenece un objeto
classes_of_individual_e(Object, KB, Classes) :-
    findall(
        Class,
        (
            member(class(Class, _, _, _, Instances), KB),
            member([id=>Object | _], Instances),
            ! % Corte para detener la búsqueda de más soluciones
        ),
        DirectClasses
    ),
    find_superclasses_list_e(DirectClasses, KB, AllClasses),
    sort(AllClasses, Classes), % Elimina duplicados y ordena
    !. % Corte para finalizar la búsqueda

% Predicado auxiliar para encontrar las superclases de una lista de clases
find_superclasses_list_e([], _, []).
find_superclasses_list_e([Class | Rest], KB, [Class | SuperClasses]) :-
    find_superclasses_e(Class, KB, ClassSuperClasses),
    find_superclasses_list_e(Rest, KB, RestSuperClasses),
    append(ClassSuperClasses, RestSuperClasses, SuperClasses),
    !. % Corte para evitar seguir buscando

% Predicado auxiliar para encontrar las superclases de una clase de forma recursiva
find_superclasses_e(Class, KB, SuperClasses) :-
    member(class(Class, SuperClass, _, _, _), KB),
    SuperClass \= none,
    find_superclasses_e(SuperClass, KB, ParentSuperClasses),
    SuperClasses = [SuperClass | ParentSuperClasses],
    !. % Corte para evitar seguir buscando

find_superclasses_e(_, _, []).

%inciso f)
% Predicado principal para encontrar todas las relaciones de un objeto
% Regla para encontrar las relaciones específicas de un individuo en la base de conocimientos.
relations_of_individual(Individual, KB, Relations) :-
    findall(
        Property,
        (
            member(class(_, _, _, _, Properties), KB),
            member([id=>Individual | Props], Properties),
            member(Property, Props)
        ),
        Relations
    ).


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
%		Punto 2
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
add_object_property(NombreObjeto, Propiedad, Valor, KB, NuevaKB) :-
    (select(class(ClaseNombre, ClaseMadre, Props, Relaciones, Objetos), KB, TempKB) ->
        maplist(
            ({NombreObjeto, Propiedad, Valor}/[Objeto, ObjetoActualizado]>>
                (Objeto = [id=>NombreObjeto, PropiedadesObjeto, RelacionesObjeto] ->
                    append(PropiedadesObjeto, [[Propiedad => Valor]], NuevasProps),
                    ObjetoActualizado = [id=>NombreObjeto, NuevasProps, RelacionesObjeto]
                ;
                    ObjetoActualizado = Objeto
                )
            ),
            Objetos, NuevosObjetos),
        append(TempKB, [class(ClaseNombre, ClaseMadre, Props, Relaciones, NuevosObjetos)], NuevaKB),
        write('Propiedad agregada al objeto exitosamente.'), nl
    ;
        write('El objeto o su clase no existen.'), nl,
        NuevaKB = KB
    ).

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
add_object_relation(NombreObjeto, Relacion, ObjetosRelacionados, KB, NuevaKB) :-
    (select(class(ClaseNombre, ClaseMadre, Props, Relaciones, Objetos), KB, TempKB) ->
        maplist(
            ({NombreObjeto, Relacion, ObjetosRelacionados}/[Objeto, ObjetoActualizado]>>
                (Objeto = [id=>NombreObjeto, PropsObjeto, RelacionesObjeto] ->
                    append(RelacionesObjeto, [[Relacion => ObjetosRelacionados]], NuevasRelacionesObjeto),
                    ObjetoActualizado = [id=>NombreObjeto, PropsObjeto, NuevasRelacionesObjeto]
                ;
                    ObjetoActualizado = Objeto
                )
            ),
            Objetos, NuevosObjetos),
        append(TempKB, [class(ClaseNombre, ClaseMadre, Props, Relaciones, NuevosObjetos)], NuevaKB),
        write('Relación agregada al objeto exitosamente.'), nl
    ;
        write('El objeto o su clase no existen.'), nl,
        NuevaKB = KB
    ).

%-----------------------------------
%		Punto 3
%-----------------------------------
%inciso a)
% Predicado para eliminar una clase de la base de conocimientos
rm_class(ClassName, CurrentKB, NewKB) :-
    exclude(is_exact_class(ClassName), CurrentKB, NewKB).

is_exact_class(ClassName, class(ClassName, _, _, _, _)).

% Predicado para eliminar un objeto de la base de conocimientos
rm_object(ObjectID, CurrentKB, NewKB) :-
    maplist(remove_object_from_class(ObjectID), CurrentKB, UpdatedKB),
    exclude(is_empty_class, UpdatedKB, NewKB).

remove_object_from_class(ObjectID, class(Name, Superclass, Properties, Relations, Objects), class(Name, Superclass, Properties, Relations, UpdatedObjects)) :-
    exclude(has_id(ObjectID), Objects, UpdatedObjects).

% Predicado para verificar si un objeto tiene un identificador específico con el formato id=>ObjectID
has_id(ObjectID, id=>ObjectID).

% Predicado para verificar si una clase está vacía (sin objetos)
is_empty_class(class(_, _, _, _, Objects)) :-
    Objects == [].



%inciso b
% Predicado para eliminar una propiedad específica de una clase
rm_class_property(ClassName, Property, CurrentKB, NewKB) :-
    maplist(remove_class_property(ClassName, Property), CurrentKB, UpdatedKB),
    NewKB = UpdatedKB.

remove_class_property(ClassName, Property, class(Name, Superclass, Properties, Relations, Objects), class(Name, Superclass, UpdatedProperties, Relations, Objects)) :-
    (Name == ClassName ->
        exclude(==(Property), Properties, UpdatedProperties)
    ;
        UpdatedProperties = Properties
    ).

% Predicado para eliminar una propiedad específica de un objeto
rm_object_property(ObjectID, Property, CurrentKB, NewKB) :-
    maplist(remove_object_property_from_class(ObjectID, Property), CurrentKB, NewKB).

remove_object_property_from_class(ObjectID, Property, class(Name, Superclass, Properties, Relations, Objects), class(Name, Superclass, Properties, Relations, UpdatedObjects)) :-
    maplist(remove_property_from_object(ObjectID, Property), Objects, UpdatedObjects).

% Predicado para eliminar una propiedad específica de un objeto
remove_property_from_object(ObjectID, Property, Object, UpdatedObject) :-
    (Object =.. [id=>ObjectID | Props] ->
        exclude(==(Property), Props, UpdatedProps),
        UpdatedObject =.. [id=>ObjectID | UpdatedProps]
    ;
        UpdatedObject = Object
    ).

%Inciso c)
% Remove a relation from a class and maintain the order
rm_class_relation(ClassName, Relation, KB, NewKB) :-
    write('Buscando la clase: '), write(ClassName), nl,
    select(class(ClassName, Parent, Methods, Properties, Instances), KB, RestKB),
    write('Clase encontrada. Eliminando la relación: '), write(Relation), nl,
    (member(Relation, Methods) ->
        delete(Methods, Relation, NewMethods),
        NewClass = class(ClassName, Parent, NewMethods, Properties, Instances),
        append(RestKB, [NewClass], OrderedKB),
        write('Clase modificada: '), write(NewClass), nl,
        NewKB = OrderedKB,  % Mantener el orden original de la base de conocimientos
        !
    ;
        write('La relación no se encontró en la clase.'), nl,
        NewKB = KB
    ).

% Remove a relation from an object within a class and maintain the order
rm_object_relation(ObjectName, Relation, KB, NewKB) :-
    write('Buscando la clase que contiene el objeto: '), write(ObjectName), nl,
    select(class(ClassName, Parent, Methods, Properties, Instances), KB, RestKB),
    write('Clase encontrada: '), write(ClassName), nl,
    % Verificar si hay una instancia con el formato id=>ObjectName
    (member(id=>ObjectName, Instances) ->
        write('Objeto encontrado en la clase: '), write(ObjectName), nl,
        % Buscar y modificar la relación de las propiedades
        (select(mimic=>yes, Instances, UpdatedInstances) ->
            write('Relación encontrada y eliminada: '), write(Relation), nl,
            % Reconstruir la clase con la instancia actualizada
            NewClass = class(ClassName, Parent, Methods, Properties, UpdatedInstances),
            append(RestKB, [NewClass], OrderedKB),
            write('Clase modificada con objeto actualizado: '), write(NewClass), nl,
            NewKB = OrderedKB,  % Mantener el orden original de la base de conocimientos
            !
        ;
            write('La relación no se encontró en el objeto.'), nl,
            NewKB = KB
        )
    ;
    write('El objeto no fue encontrado en la clase.'), nl,
    fail  % Si el objeto no se encuentra, falla para seguir buscando en otras clases
    ).




%-----------------------------------
%		Punto 4
%-----------------------------------
% Inciso a
% Modificar el nombre de una clase
% Predicado para cambiar el nombre de una clase
change_class_name(NombreClaseActual, NuevoNombreClase, KB, NuevaKB) :-
    select(class(NombreClaseActual, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    append(KBRestante, [class(NuevoNombreClase, ClaseMadre, Propiedades, Relaciones, Objetos)], NuevaKB).
% Modificar el nombre de un objeto
% Predicado para cambiar el nombre de un objeto dentro de una clase
change_object_name(NombreClase, NombreObjetoActual, NuevoNombreObjeto, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    maplist(
        ({NombreObjetoActual, NuevoNombreObjeto}/[Objeto, ObjetoModificado]>>
            (Objeto = [id=>NombreObjetoActual, PropiedadesObjeto, RelacionesObjeto] ->
             ObjetoModificado = [id=>NuevoNombreObjeto, PropiedadesObjeto, RelacionesObjeto] ;
             ObjetoModificado = Objeto)),
        Objetos, NuevosObjetos),
    append(KBRestante, [class(NombreClase, ClaseMadre, Propiedades, Relaciones, NuevosObjetos)], NuevaKB).
% Inciso b
% Predicado para modificar el valor de una propiedad específica de una clase
change_value_class_property(NombreClase, Propiedad, NuevoValor, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    maplist(
        ({Propiedad, NuevoValor}/[PropiedadActual=>ValorActual, PropiedadActual=>ValorModificado]>>
            ( (PropiedadActual == Propiedad) -> ValorModificado=NuevoValor ; ValorModificado=ValorActual )),
        Propiedades, NuevasPropiedades),
    append(KBRestante, [class(NombreClase, ClaseMadre, NuevasPropiedades, Relaciones, Objetos)], NuevaKB).
% Predicado para modificar el valor de una propiedad específica de un objeto dentro de una clase
change_value_object_property(NombreClase, NombreObjeto, Propiedad, NuevoValor, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    maplist(
        ({NombreObjeto, Propiedad, NuevoValor}/[Objeto, ObjetoModificado]>>
            (Objeto = [id=>NombreObjeto, PropiedadesObjeto, RelacionesObjeto] ->
             maplist(
                ({Propiedad, NuevoValor}/[PropiedadActual=>ValorActual, PropiedadActual=>ValorModificado]>>
                    ( (PropiedadActual == Propiedad) -> ValorModificado=NuevoValor ; ValorModificado=ValorActual )),
                PropiedadesObjeto, NuevasPropiedadesObjeto),
             ObjetoModificado = [id=>NombreObjeto, NuevasPropiedadesObjeto, RelacionesObjeto] ;
             ObjetoModificado = Objeto)),
        Objetos, NuevosObjetos),
    append(KBRestante, [class(NombreClase, ClaseMadre, Propiedades, Relaciones, NuevosObjetos)], NuevaKB).
% Inciso c
% Predicado para modificar una relación específica de una clase
change_value_class_relation(NombreClase, Relacion, NuevasClasesRelacionadas, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    maplist(
        ({Relacion, NuevasClasesRelacionadas}/[RelacionActual=>RelacionadosActuales, RelacionActual=>RelacionModificada]>>
            ( (RelacionActual == Relacion) -> RelacionModificada=NuevasClasesRelacionadas ; RelacionModificada=RelacionadosActuales )),
        Relaciones, NuevasRelaciones),
    append(KBRestante, [class(NombreClase, ClaseMadre, Propiedades, NuevasRelaciones, Objetos)], NuevaKB).
% Predicado para modificar una relación específica de un objeto dentro de una clase
change_value_object_relation(NombreClase, NombreObjeto, Relacion, NuevosObjetosRelacionados, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    maplist(
        ({NombreObjeto, Relacion, NuevosObjetosRelacionados}/[Objeto, ObjetoModificado]>>
            (Objeto = [id=>NombreObjeto, PropiedadesObjeto, RelacionesObjeto] ->
             maplist(
                ({Relacion, NuevosObjetosRelacionados}/[RelacionActual=>RelacionadosActuales, RelacionActual=>RelacionModificada]>>
                    ( (RelacionActual == Relacion) -> RelacionModificada=NuevosObjetosRelacionados ; RelacionModificada=RelacionadosActuales )),
                RelacionesObjeto, NuevasRelacionesObjeto),
             ObjetoModificado = [id=>NombreObjeto, PropiedadesObjeto, NuevasRelacionesObjeto] ;
             ObjetoModificado = Objeto)),
        Objetos, NuevosObjetos),
    append(KBRestante, [class(NombreClase, ClaseMadre, Propiedades, Relaciones, NuevosObjetos)], NuevaKB).



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
