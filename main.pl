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
% Inciso a
% Predicado para añadir una nueva clase a la base de conocimientos
add_class(NombreClase, ClaseMadre, KB, NuevaKB) :-
    append(KB, [class(NombreClase, ClaseMadre, [], [], [])], NuevaKB).

% Predicado para añadir un nuevo objeto a una clase específica en la base de conocimientos
add_object(NombreObjeto, NombreClase, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    append(Objetos, [[id=>NombreObjeto, [], []]], NuevosObjetos),
    append(KBRestante, [class(NombreClase, ClaseMadre, Propiedades, Relaciones, NuevosObjetos)], NuevaKB).

% Inciso b
% Predicado para añadir una propiedad a una clase en la base de conocimientos
add_class_property(NombreClase, Propiedad, Valor, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    append(Propiedades, [Propiedad=>Valor], NuevasPropiedades),
    append(KBRestante, [class(NombreClase, ClaseMadre, NuevasPropiedades, Relaciones, Objetos)], NuevaKB).

% Predicado para añadir una propiedad a un objeto dentro de una clase
add_object_property(NombreClase, NombreObjeto, Propiedad, Valor, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    % Encuentra y modifica el objeto específico
    maplist(
        ( [id=>NombreObjeto, PropiedadesObjeto, RelacionesObjeto] >> 
            (append(PropiedadesObjeto, [Propiedad=>Valor], NuevasPropiedadesObjeto),
             [id=>NombreObjeto, NuevasPropiedadesObjeto, RelacionesObjeto]) ),
        Objetos, NuevosObjetos),
    append(KBRestante, [class(NombreClase, ClaseMadre, Propiedades, Relaciones, NuevosObjetos)], NuevaKB).

% Inciso c
% Predicado para añadir una relación a una clase en la base de conocimientos
add_class_relation(NombreClase, Relacion, ClasesRelacionadas, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    append(Relaciones, [Relacion=>ClasesRelacionadas], NuevasRelaciones),
    append(KBRestante, [class(NombreClase, ClaseMadre, Propiedades, NuevasRelaciones, Objetos)], NuevaKB).

% Predicado para añadir una relación a un objeto dentro de una clase
add_object_relation(NombreClase, NombreObjeto, Relacion, ObjetosRelacionados, KB, NuevaKB) :-
    select(class(NombreClase, ClaseMadre, Propiedades, Relaciones, Objetos), KB, KBRestante),
    maplist(
        ( [id=>NombreObjeto, PropiedadesObjeto, RelacionesObjeto] >> 
            (append(RelacionesObjeto, [Relacion=>ObjetosRelacionados], NuevasRelacionesObjeto),
             [id=>NombreObjeto, PropiedadesObjeto, NuevasRelacionesObjeto]) ),
        Objetos, NuevosObjetos),
    append(KBRestante, [class(NombreClase, ClaseMadre, Propiedades, Relaciones, NuevosObjetos)], NuevaKB).

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
