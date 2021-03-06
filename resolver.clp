;;; IC: Trabajo (2016/2017)
;;; Resolución deductiva de un Kakuro
;;; Departamento de Ciencias de la Computación e Inteligencia Artificial
;;; Universidad de Sevilla
;;;============================================================================


;;;============================================================================
;;; Representación del Kakuro
;;;============================================================================

;;;   Utilizaremos la siguiente plantilla para representar las celdas del
;;; Kakuro. Cada celda tiene los siguientes campos:
;;; - id: Identificador único de la celda
;;; - fila: Número de fila en la que se encuentra la celda
;;; - columna: Número de columna en la que se encuentra la celda
;;; - rango: Rango de valores que se pueden colocar en la celda. Inicialmente
;;;   el rango son todos los valores numéricos de 1 a 9.
(defmodule MAIN (export ?ALL))

(deftemplate MAIN::celda
  (slot id)
  (slot fila)
  (slot columna)
  (multislot rango
             (default (create$ 1 2 3 4 5 6 7 8 9))))

;;;   De esta forma, una celda tendrá un valor asignado si y solo si dicho
;;; valor es el único elemento del rango.

;;;   La siguiente variable global sirve enumerar las restricciones del puzle.

(defglobal ?*restricciones* = 0)

;;;   La siguiente función sirve para asignar de forma automática y única
;;; identificadores a las restricciones del puzle.

(deffunction MAIN::idRestriccion ()
  (bind ?*restricciones* (+ ?*restricciones* 1))
  ?*restricciones*)

;;;   Utilizaremos la siguiente plantilla para almacenar las restricciones del
;;; puzle. Cada restricción tiene los siguientes campos:
;;; - id: Identificador único de la restricción
;;; - valor: Valor de la restricción
;;; - casillas: Identificadores de las casillas que se ven afectadas por la
;;;   restricción

(deftemplate MAIN::restriccion
  (slot id
        (default-dynamic (idRestriccion))
  )
  (slot valor)
  (multislot casillas))

(defrule MAIN::pasar-modulo
  =>
  (focus VALORES-INICIALES ELIMINAR-VALORES))

(deffacts MAIN::inicial
  (no-eliminado)
)

;;;============================================================================
;;; Estrategias de resolución
;;;============================================================================

;;;   El objetivo del trabajo consiste en implementar un conjunto de reglas
;;; CLIPS que resuelvan un Kakuro de forma deductiva, es decir, deduciendo el
;;; valor de una casilla a partir de reglas que analicen los posibles valores
;;; de las casillas relacionadas.
(defmodule VALORES-INICIALES (import MAIN ?ALL) (export ?ALL))

;;;;;;;; La suma igual a tres en dos celdas toma valores 1 y 2
(defrule VALORES-INICIALES::dos-celdas-suma-tres
  (restriccion (valor 3) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  (exists (celda (id ?id&?id1|?id2) (rango 1 2 ? $?)))
  =>
  (modify ?h1 (rango 1 2))
  (modify ?h2 (rango 1 2))
)

;;;;;;;; La suma igual a 4 en dos celdas toma valores 1 y 3
(defrule VALORES-INICIALES::dos-celdas-suma-cuatro
  (restriccion (valor 4) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  (exists (celda (id ?id&?id1|?id2) (rango 1 $? 3 ? $?)))
  =>
  (modify ?h1 (rango 1 3))
  (modify ?h2 (rango 1 3))
)

;;;;;;;; La suma igual a 16 en dos celdas toma valores 7 y 9
(defrule VALORES-INICIALES::dos-celdas-suma-dieciseis
  (restriccion (valor 16) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango $? ? ?))
  ?h2 <- (celda (id ?id2) (rango $? ? ?))
  (exists (celda (id ?id&?id1|?id2) (rango $? ? 7 $? 9)))
  =>
  (modify ?h1 (rango 7 9))
  (modify ?h2 (rango 7 9))
)

;;;;;;;; La suma igual a 17 en dos celdas toma valores 8 y 9
(defrule VALORES-INICIALES::dos-celdas-suma-diecisiete
  (restriccion (valor 17) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango $? ? ?))
  ?h2 <- (celda (id ?id2) (rango $? ? ?))
  (exists (celda (id ?id&?id1|?id2) (rango $? ? 8 9)))
  =>
  (modify ?h1 (rango 8 9))
  (modify ?h2 (rango 8 9))
)

;;;;;;;; La suma igual a 6 en tres celdas toma los valores 1, 2 y 3
(defrule VALORES-INICIALES::tres-celdas-suma-seis
  (restriccion (valor 6) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  (exists (celda (id ?id&?id1|?id2|?id3) (rango 1 2 3 ? $?)))
  =>
  (modify ?h1 (rango 1 2 3))
  (modify ?h2 (rango 1 2 3))
  (modify ?h3 (rango 1 2 3))
)

;;;;;;;; La suma igual a 7 en tres celdas toma los valores 1, 2 y 4
(defrule VALORES-INICIALES::tres-celdas-suma-siete
  (restriccion (valor 7) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  (exists (celda (id ?id&?id1|?id2|?id3) (rango 1 2 $? 4 ? $?)))
  =>
  (modify ?h1 (rango 1 2 4))
  (modify ?h2 (rango 1 2 4))
  (modify ?h3 (rango 1 2 4))
)

;;;;;;;; La suma igual a 23 en tres celdas toma los valores 6, 8 y 9
(defrule VALORES-INICIALES::tres-celdas-suma-veintitres
  (restriccion (valor 23) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  (exists (celda (id ?id&?id1|?id2|?id3) (rango $? ? 6 $? 8 9)))
  =>
  (modify ?h1 (rango 6 8 9))
  (modify ?h2 (rango 6 8 9))
  (modify ?h3 (rango 6 8 9))
)

;;;;;;;; La suma igual a 24 en tres celdas toma los valores 7, 8 y 9
(defrule VALORES-INICIALES::tres-celdas-suma-veinticuatro
  (restriccion (valor 24) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  (exists (celda (id ?id&?id1|?id2|?id3) (rango $? ? 7 8 9)))
  =>
  (modify ?h1 (rango 7 8 9))
  (modify ?h2 (rango 7 8 9))
  (modify ?h3 (rango 7 8 9))
)

;;;;;;;; La suma igual a 10 en cuatro celdas toma los valores 1, 2, 3 y 4
(defrule VALORES-INICIALES::cuatro-celdas-suma-diez
  (restriccion (valor 10) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4) (rango 1 2 3 4 ? $?)))
  =>
  (modify ?h1 (rango 1 2 3 4))
  (modify ?h2 (rango 1 2 3 4))
  (modify ?h3 (rango 1 2 3 4))
  (modify ?h4 (rango 1 2 3 4))
)

;;;;;;;; La suma igual a 11 en cuatro celdas toma los valores 1, 2, 3 y 5
(defrule VALORES-INICIALES::cuatro-celdas-suma-once
  (restriccion (valor 11) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4) (rango 1 2 3 4 5 ? $?)))
  =>
  (modify ?h1 (rango 1 2 3 5))
  (modify ?h2 (rango 1 2 3 5))
  (modify ?h3 (rango 1 2 3 5))
  (modify ?h4 (rango 1 2 3 5))
)

;;;;;;;; La suma igual a 29 en cuatro celdas toma los valores 5, 7, 8 y 9
(defrule VALORES-INICIALES::cuatro-celdas-suma-veintinueve
  (restriccion (valor 29) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4) (rango $? ? 5 $? 7 8 9)))
  =>
  (modify ?h1 (rango 5 7 8 9))
  (modify ?h2 (rango 5 7 8 9))
  (modify ?h3 (rango 5 7 8 9))
  (modify ?h4 (rango 5 7 8 9))
)

;;;;;;;; La suma igual a 30 en cuatro celdas toma los valores 6, 7, 8 y 9
(defrule VALORES-INICIALES::cuatro-celdas-suma-treinta
  (restriccion (valor 30) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4) (rango $? ? 6 7 8 9)))
  =>
  (modify ?h1 (rango 6 7 8 9))
  (modify ?h2 (rango 6 7 8 9))
  (modify ?h3 (rango 6 7 8 9))
  (modify ?h4 (rango 6 7 8 9))
)

;;;;;;;; La suma igual a 15 en cuatro celdas toma los valores 1, 2, 3, 4 y 5
(defrule VALORES-INICIALES::cinco-celdas-suma-quince
  (restriccion (valor 15) (casillas ?id1 ?id2 ?id3 ?id4 ?id5))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  ?h5 <- (celda (id ?id5))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4|?id5) (rango 1 2 3 4 5 ? $?)))
  =>
  (modify ?h1 (rango 1 2 3 4 5))
  (modify ?h2 (rango 1 2 3 4 5))
  (modify ?h3 (rango 1 2 3 4 5))
  (modify ?h4 (rango 1 2 3 4 5))
  (modify ?h5 (rango 1 2 3 4 5))
)

;;;;;;;; La suma igual a 16 en cinco celdas toma los valores 1, 2, 3, 4 y 6
(defrule VALORES-INICIALES::cinco-celdas-suma-deiciseis
  (restriccion (valor 16) (casillas ?id1 ?id2 ?id3 ?id4 ?id5))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  ?h5 <- (celda (id ?id5))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4|?id5) (rango 1 2 3 4 $? 6 ? $?)))
  =>
  (modify ?h1 (rango 1 2 3 4 6))
  (modify ?h2 (rango 1 2 3 4 6))
  (modify ?h3 (rango 1 2 3 4 6))
  (modify ?h4 (rango 1 2 3 4 6))
  (modify ?h5 (rango 1 2 3 4 6))
)

;;;;;;;; La suma igual a 34 en cinco celdas toma los valores 4, 6, 7, 8 y 9
(defrule VALORES-INICIALES::cinco-celdas-suma-treintaycuatro
  (restriccion (valor 34) (casillas ?id1 ?id2 ?id3 ?id4 ?id5))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  ?h5 <- (celda (id ?id5))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4|?id5) (rango $? ? 4 $? 6 7 8 9)))
  =>
  (modify ?h1 (rango 4 6 7 8 9))
  (modify ?h2 (rango 4 6 7 8 9))
  (modify ?h3 (rango 4 6 7 8 9))
  (modify ?h4 (rango 4 6 7 8 9))
  (modify ?h5 (rango 4 6 7 8 9))
)

;;;;;;;; La suma igual a 35 en cinco celdas toma los valores 4, 6, 7, 8 y 9
(defrule VALORES-INICIALES::cinco-celdas-suma-treintaycinco
  (restriccion (valor 35) (casillas ?id1 ?id2 ?id3 ?id4 ?id5))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  ?h5 <- (celda (id ?id5))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4|?id5) (rango $? ? 5 6 7 8 9)))
  =>
  (modify ?h1 (rango 5 6 7 8 9))
  (modify ?h2 (rango 5 6 7 8 9))
  (modify ?h3 (rango 5 6 7 8 9))
  (modify ?h4 (rango 5 6 7 8 9))
  (modify ?h5 (rango 5 6 7 8 9))
)

;;;;;;;; La suma igual a 21 en cuatro celdas toma los valores 1, 2, 3, 4, 5 y 6
(defrule VALORES-INICIALES::seis-celdas-suma-veintiuno
  (restriccion (valor 21) (casillas ?id1 ?id2 ?id3 ?id4 ?id5 ?id6))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  ?h5 <- (celda (id ?id5))
  ?h6 <- (celda (id ?id6))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4|?id5|?id6) (rango 1 2 3 4 5 6 ? $?)))
  =>
  (modify ?h1 (rango 1 2 3 4 5 6))
  (modify ?h2 (rango 1 2 3 4 5 6))
  (modify ?h3 (rango 1 2 3 4 5 6))
  (modify ?h4 (rango 1 2 3 4 5 6))
  (modify ?h5 (rango 1 2 3 4 5 6))
  (modify ?h6 (rango 1 2 3 4 5 6))
)

;;;;;;;; La suma igual a 22 en cuatro celdas toma los valores 1, 2, 3, 4, 5 y 6
(defrule VALORES-INICIALES::seis-celdas-suma-veintidos
  (restriccion (valor 22) (casillas ?id1 ?id2 ?id3 ?id4 ?id5 ?id6))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  ?h5 <- (celda (id ?id5))
  ?h6 <- (celda (id ?id6))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4|?id5|?id6) (rango 1 2 3 4 5 ? 7 $?)))
  =>
  (modify ?h1 (rango 1 2 3 4 5 7))
  (modify ?h2 (rango 1 2 3 4 5 7))
  (modify ?h3 (rango 1 2 3 4 5 7))
  (modify ?h4 (rango 1 2 3 4 5 7))
  (modify ?h5 (rango 1 2 3 4 5 7))
  (modify ?h6 (rango 1 2 3 4 5 7))
)

;;;;;;;; La suma igual a 38 en seis celdas toma los valores 3, 5, 6, 7, 8 y 9
(defrule VALORES-INICIALES::seis-celdas-suma-38
  (restriccion (valor 38) (casillas ?id1 ?id2 ?id3 ?id4 ?id5 ?id6))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  ?h5 <- (celda (id ?id5))
  ?h6 <- (celda (id ?id6))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4|?id5|?id6) (rango $? 3 ? 5 6 7 8 9)))
  =>
  (modify ?h1 (rango 3 5 6 7 8 9))
  (modify ?h2 (rango 3 5 6 7 8 9))
  (modify ?h3 (rango 3 5 6 7 8 9))
  (modify ?h4 (rango 3 5 6 7 8 9))
  (modify ?h5 (rango 3 5 6 7 8 9))
  (modify ?h6 (rango 3 5 6 7 8 9))
)

;;;;;;;; La suma igual a 39 en cuatro celdas toma los valores 4, 5, 6, 7, 8 y 9
(defrule VALORES-INICIALES::seis-celdas-suma-39
  (restriccion (valor 39) (casillas ?id1 ?id2 ?id3 ?id4 ?id5 ?id6))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  ?h5 <- (celda (id ?id5))
  ?h6 <- (celda (id ?id6))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4|?id5|?id6) (rango $? ? 4 5 6 7 8 9)))
  =>
  (modify ?h1 (rango 4 5 6 7 8 9))
  (modify ?h2 (rango 4 5 6 7 8 9))
  (modify ?h3 (rango 4 5 6 7 8 9))
  (modify ?h4 (rango 4 5 6 7 8 9))
  (modify ?h5 (rango 4 5 6 7 8 9))
  (modify ?h6 (rango 4 5 6 7 8 9))
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;   MODULO   ;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;; RESOLVER ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmodule RESOLVER (import VALORES-INICIALES ?ALL) (export ?ALL))
(defrule RESOLVER::no-nuevo-valor
  (declare (salience -5))
  (no-nuevo-valor)
  =>
  (focus IMPRIMIR)
)

(defrule RESOLVER::nuevo-valor
  (declare (salience -5))
  ?h <- (nuevo-valor)
  =>
  (retract ?h)
  (assert (no-eliminado))
  (focus ELIMINAR-VALORES)
)

;; Completa restricción.
;; El funcionamiento es el siguiente: Si la restricción tiene una sola casilla
;;    y el valor de la restricción esta esta en el rango de la celda, completa
;;    la restricción.
(defrule RESOLVER::completar-restriccion
  (restriccion (valor ?v) (casillas ?i))
  ?h <- (celda (id ?i) (rango $?r))
  (not (celda (id ?i) (rango ?)))
  (test (member$ ?v $?r))
  =>
  (modify ?h (rango ?v))
  (assert (nuevo-valor))
)

(defrule RESOLVER::pone-valor-restriccion-tres-celdas
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3))
  (celda (id ?c1&?i1|?i2|?i3) (rango 5 7 8))
  ?h <- (celda (id ?c2&?i1|?i2|?i3) (rango 5 8))
  (celda (id ?c3&?i1|?i2|?i3) (rango 7 8))
  =>
  (modify ?h (rango 5))
  (assert (nuevo-valor))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;   MODULO   ;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;; ELIMINAR ;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;; VALORES ;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmodule ELIMINAR-VALORES (import RESOLVER ?ALL) (export ?ALL))

(defrule ELIMINAR-VALORES::eliminado
  (declare (salience -5))
  ?h <- (eliminado)
  =>
  (retract ?h)
  (assert (no-nuevo-valor))
  (focus RESOLVER)
)

(defrule ELIMINAR-VALORES::no-eliminado
  (declare (salience -5))
  (no-eliminado)
  =>
  (focus IMPRIMIR)
)

(defrule ELIMINAR-VALORES::eliminar-sumas-imposibles-dos-celdas
  ;;(declare (salience -1))
  (restriccion (valor ?v) (casillas ?i1 ?i2))
  ?h <- (celda (id ?c1&?i1|?i2) (rango $?i ?r $?d))
  (celda (id ?c2&?i1|?i2) (rango $?r2))
  (test (neq ?c1 ?c2))
  (test (not (member$ (- ?v ?r) $?r2)))
  =>
  (modify ?h (rango $?i $?d))
  (assert (eliminado))
)

;; Elimina de las casillas de la misma restriccion el valor de las celdas
;;      que tienen un solo valor en su rango. (Importante: Alta prioridad.)
;;      Los motivos de la alta prioridad es que se ejecute antes de eliminar
;;      una celda de una restriccion y ayuda a la resolución más rápida.
(defrule ELIMINAR-VALORES::eliminar-valor-existente-en-restriccion
  (declare (salience 100))
  (restriccion (casillas $? ?i1 $? ?i2 $?))
  (celda (id ?i3&?i1|?i2) (rango ?v))
  ?h <- (celda (id ?i4&?i1|?i2) (rango $?vi ?v $?vd))
  (test (neq ?i3 ?i4))
  =>
  (modify ?h (rango $?vi $?vd))
  (assert (eliminado))
)

;; Elimina aquellos valores del rango de una casilla que esté en una
;;      restricción de dos celdas que cumplan que el valor de la restriccion
;;      entre dos esté en el rango de la celda.
(defrule ELIMINAR-VALORES::eliminar-valores-rango-dividir-entre-dos
  (restriccion (valor ?v) (casillas ?i1 ?i2))
  ?h <- (celda (id ?i3&?i1|?i2) (rango $?v1 ?r $?v2))
  (test (eq ?v (* ?r 2)))
  =>
  (modify ?h (rango $?v1 $?v2))
  (assert (eliminado))
)

; Elimina aquellos valores del rango que sean mayores que el valor de la
;      restricción a la que pertenece.
(defrule ELIMINAR-VALORES::eliminar-valores-rango-mayor-que-restriccion
  (restriccion (valor ?v) (casillas $? ?i $?))
  ?h <- (celda (id ?i) (rango $?v1 ?v2))
  (test (> ?v2 ?v))
  =>
  (modify ?h (rango $?v1))
  (assert (eliminado))
)

; Resuelve intersecciones de tres restricciones, una de tres celdas y las otras
;    dos restantes restricciones de dos celdas.
(defrule ELIMINAR-VALORES::pone-valor-interseccion-dos-dos-dos-tres-celdas
  (restriccion (valor ?v1) (casillas ?i1 ?i2)) ;; indep.
  (restriccion (valor ?v4) (casillas ?i7 ?i8 ?i9))
  (restriccion (valor ?v2) (casillas ?i3&?i1|?i7 ?i4&?i1|?i7)) ;; 1º inter
  (restriccion (valor ?v3) (casillas ?i5&?i2|?i8 ?i6&?i2|?i8)) ;; 2º inter
  ?h <- (celda (id ?i9) (rango $?r))
  (not (celda (id ?i9) (rango ?)))
  (test (member$ (- (+ ?v1 ?v4) (+ ?v2 ?v3)) $?r))
  =>
  (modify ?h (rango (- (+ ?v1 ?v4) (+ ?v2 ?v3))))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::pone-valor-interseccion-dos-dos-dos-tres-celdas-v2
  (restriccion (valor ?v1) (casillas ?i1 ?i2)) ;; indep.
  (restriccion (valor ?v4) (casillas ?i7 ?i8 ?i9))
  (restriccion (valor ?v2) (casillas ?i3&?i1|?i8 ?i4&?i1|?i8)) ;; 1º inter
  (restriccion (valor ?v3) (casillas ?i5&?i2|?i9 ?i6&?i2|?i9)) ;; 2º inter
  ?h <- (celda (id ?i7) (rango $?r))
  (not (celda (id ?i7) (rango ?)))
  (test (member$ (- (+ ?v1 ?v4) (+ ?v2 ?v3)) $?r))
  =>
  (modify ?h (rango (- (+ ?v1 ?v4) (+ ?v2 ?v3))))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::pone-valor-unico-restriccion-cuatro-celdas
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h <- (celda (id ?c1&?i1|?i2|?i3|?i4) (rango ?r1 ?r ?r2 ?r3))
  (celda (id ?c2&?i1|?i2|?i3|?i4) (rango ?r2 ?r3))
  (celda (id ?c3&?i1|?i2|?i3|?i4) (rango ?r1 ?r3))
  (celda (id ?c4&?i1|?i2|?i3|?i4) (rango $?rango))
  (test (not (member$ ?r $?rango)))
  =>
  (modify ?h (rango ?r))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::elimina-valor-suma-imposible-tres-celdas
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3))
  ?h <- (celda (id ?c1&?i1|?i2|?i3) (rango $?i ?r $?d))
  (celda (id ?c2&?i1|?i2|?i3) (rango ?r1 ?r2))
  (celda (id ?c3&?i1|?i2|?i3) (rango $?rango))
  (test (neq ?c1 ?c2)) (test (neq ?c1 ?c3)) (test (neq ?c2 ?c3))
  (test (not (member$ (- ?v (+ ?r ?r1)) $?rango)))
  (test (not (member$ (- ?v (+ ?r ?r2)) $?rango)))
  =>
  (modify ?h (rango $?i $?d))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::elimina-valor-suma-imposible-tres-celdas-v2
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3))
  ?h <- (celda (id ?c1&?i1|?i2|?i3) (rango $?i ?r $?d))
  (celda (id ?c2&?i1|?i2|?i3) (rango ?r1 ?r2 ?r3))
  (celda (id ?c3&?i1|?i2|?i3) (rango $?rango))
  (test (neq ?c1 ?c2)) (test (neq ?c1 ?c3)) (test (neq ?c2 ?c3))
  (test (not (member$ (- ?v (+ ?r ?r1)) $?rango)))
  (test (not (member$ (- ?v (+ ?r ?r2)) $?rango)))
  (test (not (member$ (- ?v (+ ?r ?r3)) $?rango)))
  =>
  (modify ?h (rango $?i $?d))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::elimina-valor-suma-imposible-tres-celdas-v3
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3))
  ?h <- (celda (id ?c1&?i1|?i2|?i3) (rango $?i ?r $?d))
  (celda (id ?c2&?i1|?i2|?i3) (rango ?r1 ?r2))
  (celda (id ?c3&?i1|?i2|?i3) (rango ?r3 ?r4))
  (test (neq ?c1 ?c2)) (test (neq ?c1 ?c3)) (test (neq ?c2 ?c3))
  (test (eq ?r ?r2))
  (test (neq ?v (+ ?r3 ?r1 ?r)))
  (test (neq ?v (+ ?r4 ?r1 ?r)))
  =>
  (modify ?h (rango $?i $?d))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::elimina-valor-suma-imposible-tres-celdas-v4
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3))
  ?h <- (celda (id ?c1&?i1|?i2|?i3) (rango $?i ?r $?d))
  (celda (id ?c2&?i1|?i2|?i3) (rango ?r1 ?r2))
  (celda (id ?c3&?i1|?i2|?i3) (rango ?r1 ?r2))
  (test (neq ?c1 ?c2)) (test (neq ?c1 ?c3)) (test (neq ?c2 ?c3))
  (test (neq ?v (+ ?r ?r1 ?r2)))
  =>
  (modify ?h (rango $?i $?d))
  (assert (eliminado))
)


; Elimina el menor valor del rango de la primera celda que, al sumarse con los
;    mayores valores de los rangos de las demas celdas, den como resultado el
;    valor de la restriccion pero hay valor repetido.
(defrule ELIMINAR-VALORES::elimina-valores-suma-imposible-menor-cuatro-celdas
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h <- (celda (id ?c1&?i1|?i2|?i3|?i4) (rango ?r1 $?r))
  (celda (id ?c2&?i1|?i2|?i3|?i4) (rango $? ?r2))
  (celda (id ?c3&?i1|?i2|?i3|?i4) (rango $? ?r3))
  (celda (id ?c4&?i1|?i2|?i3|?i4) (rango $? ?r4))
  (not (celda (id ?c1) (rango ?)))
  (not (celda (id ?c2) (rango ?)))
  (not (celda (id ?c3) (rango ?)))
  (not (celda (id ?c4) (rango ?)))
  (test (neq ?c1 ?c2)) (test (neq ?c1 ?c3)) (test (neq ?c1 ?c4))
  (test (neq ?c2 ?c3)) (test (neq ?c2 ?c4)) (test (neq ?c3 ?c4))
  (or (and (or (test (eq ?r1 ?r4))
               (test (eq ?r1 ?r2))
               (test (eq ?r1 ?r3))
               (test (eq ?r2 ?r3))
               (test (eq ?r2 ?r4))
               (test (eq ?r3 ?r4)))
               (test (>= ?v (+ ?r1 ?r2 ?r3 ?r4))))
      (test (> ?v (+ ?r1 ?r2 ?r3 ?r4))))
  =>
  (modify ?h (rango $?r))
  (assert (eliminado))
)

;;Elimina un valor de una casilla perteneciente a una restriccion de cuatro celdas
(defrule ELIMINAR-VALORES::elimina-valor-restriccion-cuatro-celdas-sum-imp-2
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h <- (celda (id ?i1) (rango ?r1  $?r))
  (celda (id ?i4) (rango ?r1 ?r2))
  (celda (id ?i2) (rango ?r3 $?))
  (celda (id ?i3) (rango ?r4 $?))
  (test (< ?v (+ ?r1 ?r2 ?r3 ?r4)))
  =>
  (modify ?h (rango $?r))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::elimina-valor-restriccion-4-celdas-suma-imp-3
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h <- (celda (id ?c1&?i1|?i2|?i3|?i4) (rango ?r1  $?r))
  (celda (id ?c2&?i1|?i2|?i3|?i4) (rango ?r7 ?r8))
  (celda (id ?c3&?i1|?i2|?i3|?i4) (rango ?r3 ?r5))
  (celda (id ?c4&?i1|?i2|?i3|?i4) (rango ?r1 ?r3))
  (test (neq ?v (+ ?r1 ?r7 ?r5 ?r3)))
  (test (neq ?v (+ ?r1 ?r8 ?r5 ?r3)))
  (test (neq ?c1 ?c2)) (test (neq ?c1 ?c3)) (test (neq ?c1 ?c4))
  (test (neq ?c2 ?c3)) (test (neq ?c2 ?c4)) (test (neq ?c3 ?c4))
  =>
  (modify ?h (rango $?r))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::elimina-valor-restriccion-5-celdas-suma-imp
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4 ?i5))
  ?h <- (celda (id ?c1&?i1|?i2|?i3|?i4|?i5) (rango $?r ?r9))
  (celda (id ?c2&?i1|?i2|?i3|?i4|?i5) (rango ?r1 ?rk))
  (celda (id ?c3&?i1|?i2|?i3|?i4|?i5) (rango ?r1 ?r3 ?rj))
  (celda (id ?c4&?i1|?i2|?i3|?i4|?i5) (rango ?r8 ?ri))
  (celda (id ?c5&?i1|?i2|?i3|?i4|?i5) (rango ?r1 ?r2))
  (test (neq ?c1 ?c2)) (test (neq ?c1 ?c3)) (test (neq ?c1 ?c4))
  (test (neq ?c1 ?c5)) (test (neq ?c2 ?c3)) (test (neq ?c2 ?c4))
  (test (neq ?c2 ?c5)) (test (neq ?c3 ?c4)) (test (neq ?c3 ?c5)) (test (neq ?c5 ?c4))
  (or (test (< ?v (+ ?r9 ?r1 ?r3 ?r8 ?r2)))
      (and (test (<= ?v (+ ?r9 ?r1 ?r3 ?r8 ?r2)))
           (test (eq ?r8 ?r9))))
  =>
  (modify ?h (rango $?r))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::elimina-valor-interseccion-tres-tres-dos-dos
  (restriccion (valor ?v1) (casillas ?i1 ?i2 ?i3))
  (restriccion (valor ?v2) (casillas ?i2 ?i4 ?i5))
  (restriccion (valor ?v3) (casillas ?i3 ?i6))
  (restriccion (valor ?v4) (casillas ?i5 ?i6))
  (celda (id ?i1) (rango ?r1 ?r3))
  (celda (id ?i2) (rango ?r1 ?r2 ?r3))
  ?h <- (celda (id ?i3) (rango ?r8 ?r9))
  (celda (id ?i5) (rango ?r1 ?r2))
  (celda (id ?i6) (rango ?r8 ?r9))
  (test (eq ?v1 (+ ?r9 ?r1 ?r2)))
  (test (neq ?v1 (+ ?r9 ?r3 ?r1)))
  (test (neq ?v1 (+ ?r9 ?r3 ?r2)))
  (test (neq ?v1 (+ ?r9 ?r3 ?r3)))
  (test (eq ?v3 (+ ?r9 ?r8)))
  (test (eq ?v4 (+ ?r8 ?r2)))
  =>
  (modify ?h (rango ?r8))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::elimina-valor-celda-en-cuadrado-v1
  (restriccion (valor ?v1) (casillas ?i1 ?i2))
  (restriccion (valor ?v2) (casillas ?i3 ?i4))
  (restriccion (valor ?v3) (casillas ?i1 ?i3))
  ?h <- (celda (id ?i1) (rango ?r7 ?r8))
  (celda (id ?i2) (rango ?r2 ?r3))
  (celda (id ?i3) (rango ?r7 ?r8))
  (test (eq ?v1 (+ ?r8 ?r2)))
  (test (eq ?v3 (+ ?r8 ?r7)))
  (test (eq ?v2 (+ ?r7 ?r2)))
  =>
  (modify ?h (rango ?r7))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::pone-valor-unico-restriccion-cinco-celdas
  (restriccion (casillas ?i1 ?i2 ?i3 ?i4 ?i5))
  ?h <- (celda (id ?c1&?i1|?i2|?i3|?i4|?i5) (rango ?r ?r1 ?r2 ?r3 ?r4))
  (celda (id ?c2&?i1|?i2|?i3|?i4|?i5) (rango ?r1 ?r2 ?r3 ?r4))
  (celda (id ?c3&?i1|?i2|?i3|?i4|?i5) (rango ?r1 ?r2 ?r3 ?r4))
  (celda (id ?c4&?i1|?i2|?i3|?i4|?i5) (rango ?r2 ?r4))
  (celda (id ?c5&?i1|?i2|?i3|?i4|?i5) (rango ?r2 ?r3))
  (test (neq ?c1 ?c2)) (test (neq ?c1 ?c3)) (test (neq ?c1 ?c4)) (test (neq ?c1 ?c5))
  (test (neq ?c2 ?c3)) (test (neq ?c4 ?c2)) (test (neq ?c5 ?c2)) (test (neq ?c4 ?c3))
  (test (neq ?c5 ?c3)) (test (neq ?c4 ?c5))
  =>
  (modify ?h (rango ?r))
  (assert (eliminado))
)

;; Elimina una celda que ya tenga un único valor de la restriccion a la cual
;;      pertenece.
(defrule ELIMINAR-VALORES::eliminar-celda-restriccion
  (declare (salience 2))
  ?h <- (restriccion (id ?i) (valor ?v) (casillas $?casillas))
  (celda (id ?c) (rango ?r))
  (test (member$ ?c $?casillas))
  =>
  (modify ?h (valor (- ?v ?r)) (casillas (delete$ $?casillas
      (member$ ?c $?casillas) (member$ ?c $?casillas))))
  (assert (eliminado))
)

;; Elimina una restriccion cuyo valor es cero, lo cual significa que ya no
;;      tiene casillas que resolver.
(defrule ELIMINAR-VALORES::eliminar-restriccion
  ?h <- (restriccion (valor 0))
  =>
  (retract ?h)
  (assert (eliminado))
)
;;;============================================================================
;;; Reglas para imprimir el resultado
;;;============================================================================

;;;   Las siguientes reglas permiten visualizar el estado del puzle, una vez
;;; aplicadas todas las reglas que implementan las estrategias de resolución.
;;; La prioridad de estas reglas es -10 para que sean las últimas en
;;; aplicarse.

;;;   Para las casillas del tablero con un único valor en su rango se indica
;;; dicho valor, para las casillas del tablero en las que no se haya podido
;;; deducir el valor se indica el símbolo '?'. El resto de las casillas hasta
;;; completar la cuadrícula 9x9 se dejan en blanco.
(defmodule IMPRIMIR (import ELIMINAR-VALORES ?ALL) (export ?ALL))
(defrule IMPRIMIR::imprime-solucion
  (declare (salience -10))
  =>
  (printout t "+---------+" crlf "|")
  (assert (imprime 1 1)))

(defrule IMPRIMIR::imprime-celda-1
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (celda (fila ?i) (columna ?j) (rango $?v))
  =>
  (retract ?h)
  (if (= (length$ $?v) 1)
      then (printout t (nth$ 1 $?v))
    else (printout t "?"))
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

(defrule IMPRIMIR::imprime-celda-2
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (not (celda (fila ?i) (columna ?j) (rango $?v)))
  =>
  (retract ?h)
  (printout t " ")
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

;;;============================================================================
;;; Funcionalidad para leer los puzles del fichero de ejemplos
;;;============================================================================

;;;   Esta función crea una lista de identificadores de casillas en horizontal.

(deffunction MAIN::crea-casillas-horizontal (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat ?f (+ ?c ?i))))))
  ?datos)

;;;   Esta función construye los hechos que representan las restricciones de
;;; una línea horizontal del Kakuro.

(deffunction MAIN::procesa-restricciones-fila (?f $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?c ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?c))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-horizontal ?f ?c (- ?i ?c)))))))
  TRUE)

;;;   Esta función crea una lista de identificadores de casillas en vertical.

(deffunction MAIN::crea-casillas-vertical (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat (+ ?f ?i) ?c)))))
  ?datos)

;;;   Esta función construye los hechos que representan las restricciones de
;;; una línea horizontal del Kakuro.

(deffunction MAIN::procesa-restricciones-columna (?c $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?f ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?f))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-vertical ?f ?c (- ?i ?f)))))))
  TRUE)

;;;   Esta función construye todos los hechos que representan las restricciones
;;; de un Kakuro dado en el formato utilizado en el fichero de ejemplos.

(deffunction MAIN::procesa-restricciones-ejemplo (?datos)
  (loop-for-count
   (?i 1 9)
   (bind $?linea (create$))
   (loop-for-count
    (?j 2 10)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-fila ?i ?linea))
  (loop-for-count
   (?j 2 10)
   (bind $?linea (create$))
   (loop-for-count
    (?i 1 9)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-columna (- ?j 1) ?linea))
  TRUE)

;;;   Esta función localiza el Kakuro que se quiere resolver en el fichero de
;;; ejemplos.

(deffunction MAIN::lee-kakuro (?n)
  (open "ejemplos.txt" data "r")
  (loop-for-count (?i 1 (- ?n 1))
                  (readline data))
  (bind ?datos (readline data))
  (procesa-restricciones-ejemplo ?datos)
  (close data))

;;;   Esta regla pregunta al usuario que número de Kakuro del fichero de
;;; ejemplos se quiere resolver y genera los hechos que representan las
;;; restricciones asociadas.

(defrule MAIN::kakuro-numero
  (declare (salience 100))
  =>
  (printout t "Qué problema quieres resolver (1-50)? : ")
  (lee-kakuro (read)))

;;;   Esta regla construye las celdas que aparecen en alguna de las
;;; restricciones del Kakuro que se quiere resolver.

(defrule MAIN::crea-celdas-restricciones
  (declare (salience 100))
  (restriccion (casillas $? ?id $?))
  (not (celda (id ?id)))
  =>
  (assert (celda (id ?id) (fila (div ?id 10)) (columna (mod ?id 10)))))
