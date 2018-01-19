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

(deftemplate MAIN::prueba
  (slot valor)
  (slot id1)
  (slot id2)
)

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
  (multislot casillas)
)

(defrule MAIN::pasar-modulo
  =>
  (focus VALORES-INICIALES RESOLVER)
)

;;;============================================================================
;;; Estrategias de resolución
;;;============================================================================

;;;   El objetivo del trabajo consiste en implementar un conjunto de reglas
;;; CLIPS que resuelvan un Kakuro de forma deductiva, es decir, deduciendo el
;;; valor de una casilla a partir de reglas que analicen los posibles valores
;;; de las casillas relacionadas.
(defmodule VALORES-INICIALES (import MAIN ?ALL) (export ?ALL))

;;;;;;;; La suma igual a tres en dos celdas es trivial
(defrule VALORES-INICIALES::dos-celdas-suma-tres
  (restriccion (valor 3) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango 1 2 ? $?))
  ?h2 <- (celda (id ?id2) (rango 1 2 ? $?))
  =>
  (modify ?h1 (rango 1 2))
  (modify ?h2 (rango 1 2))
)

(defrule VALORES-INICIALES::dos-celdas-suma-tres-interseccion
  (restriccion (valor 3) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango 1 2))
  ?h2 <- (celda (id ?id2) (rango 1 2 ? $?))
  =>
  (modify ?h1 (rango 1 2))
  (modify ?h2 (rango 1 2))
)

;;;;;;;; La suma igual a 4 en dos celdas es trivial
(defrule VALORES-INICIALES::dos-celdas-suma-cuatro
  (restriccion (valor 4) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango 1 ? 3 $?))
  ?h2 <- (celda (id ?id2) (rango 1 ? 3 $?))
  =>
  (modify ?h1 (rango 1 3))
  (modify ?h2 (rango 1 3))
)

(defrule VALORES-INICIALES::dos-celdas-suma-cuatro-interseccion
  (restriccion (valor 4) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango 1 3))
  ?h2 <- (celda (id ?id2) (rango 1 ? 3 $?))
  =>
  (modify ?h1 (rango 1 3))
  (modify ?h2 (rango 1 3))
)
;;;;;;;; La suma igual a 16 en dos celdas es trivial
(defrule VALORES-INICIALES::dos-celdas-suma-dieciseis
  (restriccion (valor 16) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango $? 7 ? 9))
  ?h2 <- (celda (id ?id2) (rango $? 7 ? 9))
  =>
  (modify ?h1 (rango 7 9))
  (modify ?h2 (rango 7 9))
)

(defrule VALORES-INICIALES::dos-celdas-suma-dieciseis-interseccion
  (restriccion (valor 16) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango 7 9))
  ?h2 <- (celda (id ?id2) (rango $? 7 ? 9))
  =>
  (modify ?h1 (rango 7 9))
  (modify ?h2 (rango 7 9))
)

;;;;;;;; La suma igual a 17 en dos celdas es trivial
(defrule VALORES-INICIALES::dos-celdas-suma-diecisiete
  (restriccion (valor 17) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango $? ? 8 9))
  ?h2 <- (celda (id ?id2) (rango $? ? 8 9))
  =>
  (modify ?h1 (rango 8 9))
  (modify ?h2 (rango 8 9))
)

(defrule VALORES-INICIALES::dos-celdas-suma-diecisiete-interseccion
  (restriccion (valor 17) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango 8 9))
  ?h2 <- (celda (id ?id2) (rango $? ? 8 9))
  =>
  (modify ?h1 (rango 8 9))
  (modify ?h2 (rango 8 9))
)

(defrule VALORES-INICIALES::tres-celdas-suma-seis
  (restriccion (valor 6) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango 1 2 3 ? $?))
  ?h3 <- (celda (id ?id3) (rango 1 2 3 ? $?))
  =>
  (modify ?h1 (rango 1 2 3))
  (modify ?h2 (rango 1 2 3))
  (modify ?h3 (rango 1 2 3))
)

(defrule VALORES-INICIALES::tres-celdas-suma-siete
  (restriccion (valor 7) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango 1 2 ? 4 ? $?))
  ?h2 <- (celda (id ?id2) (rango 1 2 $?))
  ?h3 <- (celda (id ?id3) (rango 1 2 ? 4 ? $?))
  =>
  (modify ?h1 (rango 1 2 4))
  (modify ?h2 (rango 1 2 4))
  (modify ?h3 (rango 1 2 4))
)

(defrule VALORES-INICIALES::tres-celdas-suma-veinticuatro
  (restriccion (valor 24) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango $? ? 7 8 9))
  ?h2 <- (celda (id ?id2) (rango $? ? 7 8 9))
  ?h3 <- (celda (id ?id3) (rango $? ? 7 8 9))
  =>
  (modify ?h1 (rango 7 8 9))
  (modify ?h2 (rango 7 8 9))
  (modify ?h3 (rango 7 8 9))
)

(defrule VALORES-INICIALES::tres-celdas-suma-veintitres
  (restriccion (valor 23) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango $? ? 6 ? 8 9))
  ?h2 <- (celda (id ?id2) (rango $? ? 6 ? 8 9))
  ?h3 <- (celda (id ?id3) (rango $? ? 9))
  =>
  (modify ?h1 (rango 6 8 9))
  (modify ?h2 (rango 6 8 9))
  (modify ?h3 (rango 6 8 9))
)

(defrule VALORES-INICIALES::cuatro-celdas-suma-diez
  (restriccion (valor 10) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1) (rango 1 2 3 4 ? $?))
  ?h2 <- (celda (id ?id2) (rango 1 2 3 4 ? $?))
  ?h3 <- (celda (id ?id3) (rango 1 2 3 4 ? $?))
  ?h4 <- (celda (id ?id4) (rango 1 2 3 4 ? $?))
  =>
  (modify ?h1 (rango 1 2 3 4))
  (modify ?h2 (rango 1 2 3 4))
  (modify ?h3 (rango 1 2 3 4))
  (modify ?h4 (rango 1 2 3 4))
)

(defrule VALORES-INICIALES::cuatro-celdas-suma-once
  (restriccion (valor 11) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1) (rango 1 2 3 ? 5 $?))
  ?h2 <- (celda (id ?id2) (rango 1 2 3 ? 5 $?))
  ?h3 <- (celda (id ?id3) (rango 1 2 3 ? 5 $?))
  ?h4 <- (celda (id ?id4) (rango 1 2 3 ? 5 $?))
  =>
  (modify ?h1 (rango 1 2 3 5))
  (modify ?h2 (rango 1 2 3 5))
  (modify ?h3 (rango 1 2 3 5))
  (modify ?h4 (rango 1 2 3 5))
)

(defrule VALORES-INICIALES::cuatro-celdas-suma-treinta
  (restriccion (valor 30) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1) (rango $? ? 6 7 8 9))
  ?h2 <- (celda (id ?id2) (rango $? ? 6 7 8 9))
  ?h3 <- (celda (id ?id3) (rango $?))
  ?h4 <- (celda (id ?id4) (rango $?))
  =>
  (modify ?h1 (rango 6 7 8 9))
  (modify ?h2 (rango 6 7 8 9))
  (modify ?h3 (rango 6 7 8 9))
  (modify ?h4 (rango 6 7 8 9))
)

(defrule interseccion-tres-cuatro-caso-uno
  ?r1 <- (restriccion (valor 3) (casillas ?id1 ?id2))
  ?r2 <- (restriccion (valor 4) (casillas ?id1 ?id3))
  ?h1 <- (celda (id ?id1) (rango 1 2 $?))
  ?h2 <- (celda (id ?id2) (rango 1 2 $?))
  ?h3 <- (celda (id ?id3) (rango 1 $? 3 $?))
  =>
  (modify ?h1 (rango 1))
  (modify ?h2 (rango 2))
  (modify ?h3 (rango 3))
)

(defrule interseccion-tres-cuatro-caso-dos
  ?r1 <- (restriccion (valor 3) (casillas ?id2 ?id1))
  ?r2 <- (restriccion (valor 4) (casillas ?id3 ?id1))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  =>
  (modify ?h1 (rango 1))
  (modify ?h2 (rango 2))
  (modify ?h3 (rango 3))
)

(defrule interseccion-tres-cuatro-caso-tres
  ?r1 <- (restriccion (valor 4) (casillas ?id2 ?id1))
  ?r2 <- (restriccion (valor 3) (casillas ?id1 ?id3))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  =>
  (modify ?h1 (rango 1))
  (modify ?h2 (rango 3))
  (modify ?h3 (rango 2))
)
;;;;;;;; Interseccion dieciseis diecisiete
(defrule interseccion-dieciseis-diecisiete-caso-uno
  (restriccion (valor 17) (casillas ?id1 ?id2))
  (restriccion (valor 16) (casillas ?id3 ?id1))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  =>
  (modify ?h1 (rango 9))
  (modify ?h2 (rango 8))
  (modify ?h3 (rango 7))
)

(defrule interseccion-dieciseis-diecisiete-caso-dos
  (restriccion (valor 17) (casillas ?id2 ?id1))
  (restriccion (valor 16) (casillas ?id1 ?id3))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  =>
  (modify ?h1 (rango 9))
  (modify ?h2 (rango 8))
  (modify ?h3 (rango 7))
)

(defrule interseccion-dieciseis-diecisiete-caso-tres
  (restriccion (valor 17) (casillas ?id2 ?id1))
  (restriccion (valor 16) (casillas ?id3 ?id1))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  =>
  (modify ?h1 (rango 9))
  (modify ?h2 (rango 8))
  (modify ?h3 (rango 7))
)

(defrule interseccion-dieciseis-diecisiete-caso-cuatro
  (restriccion (valor 17) (casillas ?id1 ?id2))
  (restriccion (valor 16) (casillas ?id1 ?id3))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  =>
  (modify ?h1 (rango 9))
  (modify ?h2 (rango 8))
  (modify ?h3 (rango 7))
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;; Intersecciones de dos celdas ;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmodule RESOLVER (import VALORES-INICIALES ?ALL) (export ?ALL))
;;;;;;;; Intersección de la restriccion de valor 3 y 4
(defrule interseccion-cinco-tres
  (restriccion (valor 3) (casillas ?id1 ?id2))
  (restriccion (valor 5) (casillas ?id3 ?id2))
  ?h3 <- (celda (id ?id3) (rango 1 2 4 5 6 7 8 9))
  ?h2 <- (celda (id ?id2) (rango 1 2))
  ?h1 <- (celda (id ?id1) (rango 1 2))
  =>
  (modify ?h3 (rango 4))
  (modify ?h2 (rango 1))
  (modify ?h1 (rango 2))
)

(defrule interseccion-seis-tres-dos-celdas-uno
  (restriccion (valor 6) (casillas ?i1 ?i2))
  (restriccion (valor 3) (casillas ?i2 ?i3))
  ?h1 <- (celda (id ?i1) (rango $? 5 $?))
  ?h2 <- (celda (id ?i2) (rango ? ?))
  =>
  (modify ?h1 (rango 5))
  (modify ?h2 (rango 1))
)

(defrule interseccion-seis-tres-dos-celdas-dos
  (restriccion (valor 3) (casillas ?i1 ?i2))
  (restriccion (valor 6) (casillas ?i2 ?i3))
  ?h2 <- (celda (id ?i2) (rango ? ?))
  ?h3 <- (celda (id ?i3) (rango $? 5 ?))
  =>
  (modify ?h3 (rango 5))
  (modify ?h2 (rango 1))
)

(defrule interseccion-ocho-tres
  (restriccion (valor 3) (casillas ?id1 ?id2))
  (restriccion (valor 8) (casillas ?id3 ?id1))
  ?h3 <- (celda (id ?id3) (rango $? ? 6))
  ?h2 <- (celda (id ?id2) (rango 1 2))
  ?h1 <- (celda (id ?id1) (rango 1 2))
  =>
  (modify ?h3 (rango 6))
  (modify ?h2 (rango 1))
  (modify ?h1 (rango 2))
)

(defrule interseccion-diecisiete-once
  (restriccion (valor 11) (casillas ?i1 ?i2))
  (restriccion (valor 17) (casillas ?i1 ?i3))
  ?h1 <- (celda (id ?i1) (rango 8 9))
  ?h2 <- (celda (id ?i2))
  ?h3 <- (celda (id ?i3) (rango 8 9))
  (not (celda (id ?i2) (rango $? 3 $?)))
  =>
  (modify ?h3 (rango 8))
  (modify ?h2 (rango 2))
  (modify ?h1 (rango 9))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; no la entiendo
(defrule interseccion-cuatro-siete
  (restriccion (valor 4) (casillas ?id2 ?id1))
  (restriccion (valor 7) (casillas ?id3 ?id4 ?id1))
  ?h1 <- (celda (id ?id1) (rango $?))
  ?h2 <- (celda (id ?id2) (rango 1 3))
  ?h3 <- (celda (id ?id3) (rango 1 3))
  ?h4 <- (celda (id ?id4) (rango 1 3))
  =>
  (modify ?h1 (rango 1))
  (modify ?h2 (rango 3))
)

(defrule resolver-restriccion-18-tres-celdas-con-dos
  (restriccion (valor 18) (casillas ?i1 ?i2 ?i3))
  ?h1 <- (celda (id ?i1) (rango ? ? $?))
  ?h2 <- (celda (id ?i2) (rango 2))
  ?h3 <- (celda (id ?i3))
  (not (celda (id ?i1) (rango $? 7 $?)))
  =>
  (modify ?h1 (rango 9))
  (modify ?h3 (rango 7))
)

(defrule resolver-restriccion-18-tres-celdas-con-uno
  (restriccion (valor 18) (casillas ?i1 ?i2 ?i3))
  ?h1 <- (celda (id ?i1) (rango ? ? $?))
  ?h2 <- (celda (id ?i2) (rango ? ? $?))
  ?h3 <- (celda (id ?i3) (rango 1))
  (not (celda (id ?i2) (rango $? 9)))
  =>
  (modify ?h1 (rango 9))
  (modify ?h2 (rango 8))
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defrule completar-restriccion-dos-celdas-primero
  (restriccion (valor ?v1) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ?v2))
  =>
  (modify ?h1 (rango (- ?v1 ?v2)))
)

(defrule completar-restriccion-dos-celdas-segundo
  (restriccion (valor ?v1) (casillas ?id1 ?id2))
  ?h1 <- (celda (id ?id1) (rango ?v2))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  =>
  (modify ?h2 (rango (- ?v1 ?v2)))
)

(defrule completar-restriccion-tres-celdas-primero
  (restriccion (valor ?v) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango ? ? $?))
  ?h2 <- (celda (id ?id2) (rango ?v2))
  ?h3 <- (celda (id ?id3) (rango ?v3))
  =>
  (modify ?h1 (rango (- ?v (+ ?v2 ?v3))))
)

(defrule completar-restriccion-tres-celdas-segundo
  (restriccion (valor ?v) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango ?v1))
  ?h2 <- (celda (id ?id2) (rango ? ? $?))
  ?h3 <- (celda (id ?id3) (rango ?v3))
  =>
  (modify ?h2 (rango (- ?v (+ ?v1 ?v3))))
)

(defrule completar-restriccion-tres-celdas-tercero
  (restriccion (valor ?v) (casillas ?id1 ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango ?v1))
  ?h2 <- (celda (id ?id2) (rango ?v2))
  ?h3 <- (celda (id ?id3) (rango ? ? $?))
  =>
  (modify ?h3 (rango (- ?v (+ ?v1 ?v2))))
)

(defrule completar-restriccion-cuatro-celdas-cuarto
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ?v3))
  ?h4 <- (celda (id ?i4) (rango ? ? $?))
  =>
  (modify ?h4 (rango (- ?v (+ ?v1 ?v2 ?v3))))
)

(defrule completar-restriccion-cuatro-celdas-primero
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h1 <- (celda (id ?i1) (rango ? ? $?))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ?v3))
  ?h4 <- (celda (id ?i4) (rango ?v4))
  =>
  (modify ?h1 (rango (- ?v (+ ?v2 ?v3 ?v4))))
)

(defrule completar-restriccion-cuatro-celdas-segundo
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ? ? $?))
  ?h3 <- (celda (id ?i3) (rango ?v3))
  ?h4 <- (celda (id ?i4) (rango ?v4))
  =>
  (modify ?h2 (rango (- ?v (+ ?v1 ?v3 ?v4))))
)

(defrule completar-restriccion-cuatro-celdas-tercero
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ? ? $?))
  ?h4 <- (celda (id ?i4) (rango ?v4))
  =>
  (modify ?h3 (rango (- ?v (+ ?v2 ?v1 ?v4))))
)

(defrule completar-restriccion-cinco-celdas-segundo
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4 ?i5))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ? ? $?))
  ?h3 <- (celda (id ?i3) (rango ?v3))
  ?h4 <- (celda (id ?i4) (rango ?v4))
  ?h5 <- (celda (id ?i5) (rango ?v5))
  =>
  (modify ?h2 (rango (- ?v (+ ?v1 ?v3 ?v4 ?v5))))
)

(defrule completar-restriccion-cinco-celdas-cuarto
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4 ?i5))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ?v3))
  ?h4 <- (celda (id ?i4) (rango ? ? $?))
  ?h5 <- (celda (id ?i5) (rango ?v5))
  =>
  (modify ?h4 (rango (- ?v (+ ?v1 ?v2 ?v3 ?v5))))
)

(defrule completar-restriccion-cinco-celdas-tercero
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4 ?i5))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ? ? $?))
  ?h4 <- (celda (id ?i4) (rango ?v4))
  ?h5 <- (celda (id ?i5) (rango ?v5))
  =>
  (modify ?h3 (rango (- ?v (+ ?v1 ?v2 ?v4 ?v5))))
)

(defrule completar-restriccion-seis-celdas-primero
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4 ?i5 ?i6))
  ?h1 <- (celda (id ?i1) (rango ? ? $?))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ?v3))
  ?h4 <- (celda (id ?i4) (rango ?v4))
  ?h5 <- (celda (id ?i5) (rango ?v5))
  ?h6 <- (celda (id ?i6) (rango ?v6))
  =>
  (modify ?h1 (rango (- ?v (+ ?v2 ?v3 ?v4 ?v5 ?v6))))
)

(defrule completar-restriccion-seis-celdas-sexto
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4 ?i5 ?i6))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ?v3))
  ?h4 <- (celda (id ?i4) (rango ?v4))
  ?h5 <- (celda (id ?i5) (rango ?v5))
  ?h6 <- (celda (id ?i6) (rango ? ? $?))
  =>
  (modify ?h6 (rango (- ?v (+ ?v2 ?v3 ?v4 ?v5 ?v1))))
)

(defrule completar-restriccion-seis-celdas-tercero
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4 ?i5 ?i6))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ? ? $?))
  ?h4 <- (celda (id ?i4) (rango ?v4))
  ?h5 <- (celda (id ?i5) (rango ?v5))
  ?h6 <- (celda (id ?i6) (rango ?v6))
  =>
  (modify ?h3 (rango (- ?v (+ ?v2 ?v6 ?v4 ?v5 ?v1))))
)

(defrule completar-restriccion-seis-celdas-cuarto
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4 ?i5 ?i6))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ?v2))
  ?h3 <- (celda (id ?i3) (rango ?v3))
  ?h4 <- (celda (id ?i4) (rango ? ? $?))
  ?h5 <- (celda (id ?i5) (rango ?v5))
  ?h6 <- (celda (id ?i6) (rango ?v6))
  =>
  (modify ?h4 (rango (- ?v (+ ?v2 ?v6 ?v3 ?v5 ?v1))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;; Resolver tres restricciones de dos celdas
(defrule resolver-tres-restricciones-dos-celdas-cada-una
  (restriccion (valor ?v1) (casillas ?id2 ?id1))
  (restriccion (valor ?v2) (casillas ?id1 ?id3))
  (restriccion (valor ?v3) (casillas ?id4 ?id3))
  ?h1 <- (celda (id ?id1) (rango ?s1 ?s2))
  ?h2 <- (celda (id ?id2) (rango ?s1 ?s2))
  ?h3 <- (celda (id ?id3) (rango ?s3 ?s4))
  ?h4 <- (celda (id ?id4) (rango ?s3 ?s4))
  (test (neq ?s3 (- ?v2 ?s1)))
  (test (neq ?s4 (- ?v2 ?s1)))
  (test (or (eq ?s3 (- ?v2 ?s2))
            (eq ?s4 (- ?v2 ?s2))))
  =>
  (modify ?h1 (rango ?s2))
  (modify ?h2 (rango ?s1))
  (modify ?h3 (rango (- ?v2 ?s2)))
  (modify ?h4 (rango (- ?v3 (- ?v2 ?s2))))
)

;; Resuelve dos de las tres restricciones implicadas
(defrule resolver-interseccion-tres-restricciones
  (restriccion (valor ?v1) (casillas ?id1 ?id2))
  (restriccion (valor ?v2) (casillas ?id2 ?id3))
  ?h1 <- (celda (id ?id1) (rango ?s1 ?s2))
  ?h2 <- (celda (id ?id2) (rango ?s1 ?s2))
  ?h3 <- (celda (id ?id3) (rango ?s3 ?s4 ?s5))
  (test (eq ?v2 (+ ?s1 ?s5)))
  (test (eq ?v1 (+ ?s1 ?s2)))
  =>
  (modify ?h1 (rango ?s2))
  (modify ?h2 (rango ?s1))
  (modify ?h3 (rango ?s5))
)


;;;;;;;; Resuelve la restriccion de dos
(defrule interseccion-cinco-celdas-dos-celdas
  (restriccion (casillas ?i1 ?i2 ?i3 ?i4 ?i5))
  (restriccion (valor ?r) (casillas ?i6 ?i4))
  (celda (id ?i1) (rango ?v1))
  ?h4 <- (celda (id ?i4) (rango ?v2 ?v3))
  ?h2 <- (celda (id ?i6) (rango ?v2 ?v3))
  (test (or (eq ?v1 ?v2) (eq ?v1 ?v3)))
  =>
  (modify ?h4 (rango (- ?r ?v1)))
  (modify ?h2 (rango ?v1))
)

(defrule eliminar-valor-de-izquierda-en-derecha
  (restriccion (casillas $? ?i1 $? ?i2 $?))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango $?v2 ?v1 $?v3))
  (not (celda (id ?i2) (rango ?)))
  =>
  (modify ?h2 (rango $?v2 $?v3))
)

(defrule eliminar-valor-de-derecha-en-izquierda
  (restriccion (casillas $? ?i2 $? ?i1 $?))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango $?v2 ?v1 $?v3))
  =>
  (modify ?h2 (rango $?v2 $?v3))
)

(defrule eliminar-valores-rango-mayor-que-restriccion
  (restriccion (valor ?v) (casillas $? ?i $?))
  ?h <- (celda (id ?i) (rango $?v1 ?v2))
  (test (>= ?v2 ?v))
  =>
  (modify ?h (rango $?v1))
)

(defrule eliminar-valores-rango-dos-celdas-imposibles-mayor
  (restriccion (valor ?v) (casillas ?i ?))
  ?h <- (celda (id ?i) (rango $?v1 ?r $?v2))
  (test (> (- ?v ?r) 9))
  (not (celda (id ?i) (rango ?)))
  =>
  (modify ?h (rango $?v1 $?v2))
)

(defrule eliminar-valores-rango-dos-celdas-imposibles-no-rango-paso
  (restriccion (valor ?v) (casillas ?i1 ?i2))
  ?h1 <- (celda (id ?i1) (rango ?v1 ?v2))
  ?h2 <- (celda (id ?i2))
  =>
  (assert (prueba (valor (- ?v ?v2)) (id1 ?i1) (id2 ?i2)))
)

(defrule paso-dos
  (prueba (valor ?v) (id1 ?i1) (id2 ?i2))
  ?h1 <- (celda (id ?i1) (rango ?v1 ?v2))
  ?h2 <- (celda (id ?i2))
  (not (celda (id ?i2) (rango $? ?v $?)))
  =>
  (modify ?h1 (rango ?v1))
)

(defrule interseccion-tres-celdas-cuatro-celdas
  (restriccion (valor ?v1) (casillas ?i1 ?i2 ?i3))
  (restriccion (valor ?v2) (casillas ?i4 ?i5 ?i3 ?i6))
  ?h1 <- (celda (id ?i3) (rango ?r1 ?r2))
  ?h2 <- (celda (id ?i2) (rango ?r1 ?r2))
  (celda (id ?i4) (rango ?r2))
  =>
  (modify ?h1 (rango ?r1))
  (modify ?h2 (rango ?r2))
)

(defrule interseccion-cuatro-celdas-dos-celdas-eliminar-valores-uno
  (restriccion (valor ?v1) (casillas ?i1 ?i2 ?i3 ?i4))
  (restriccion (valor ?v2) (casillas ?i5 ?i4))
  ?h4 <- (celda (id ?i4) (rango ?r1 ?r2))
  ?h2 <- (celda (id ?i2) (rango ?r2))
  =>
  (modify ?h4 (rango ?r1))
)

(defrule interseccion-cuatro-dos-eliminar-valores-dos
  (restriccion (valor ?v1) (casillas ?i1 ?i2 ?i3 ?i4))
  (restriccion (valor ?v2) (casillas ?i5 ?i3))
  ?h3 <- (celda (id ?i3) (rango ?r1 ?r2))
  ?h5 <- (celda (id ?i5) (rango ?r1 ?r2))
  (celda (id ?i1) (rango ?r1))
  =>
  (modify ?h3 (rango ?r2))
  (modify ?h5 (rango ?r1))
)

(defrule interseccion-cuatro-celdas-dos-celdas
  (restriccion (casillas ? ?i2 ?i1 ?))
  (restriccion (valor ?v) (casillas ?i2 ?i3))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango ?v2 ?v1))
  ?h3 <- (celda (id ?i3) (rango ? ? $?))
  =>
  (modify ?h2 (rango ?v2))
  (modify ?h3 (rango (- ?v ?v2)))
)

;; Resuelve una interseccion de dos restricciones de dos celdas cada una
(defrule interseccion-dos-celdas-dos-celdas
  (restriccion (valor ?v1) (casillas ?i1 ?i2))
  (restriccion (valor ?v2) (casillas ?i1 ?i3))
  ?h1 <- (celda (id ?i1) (rango ?r1 ?r2))
  ?h2 <- (celda (id ?i2) (rango ? ? $?))
  ?h3 <- (celda (id ?i3) (rango ? ? $?))
  (test (< 9 (- ?v2 ?r1)))
  (test (>= 9 (- ?v2 ?r2)))
  =>
  (modify ?h1 (rango ?r2))
  (modify ?h2 (rango ?r1))
  (modify ?h3 (rango (- ?v2 ?r2)))
)

(defrule interseccion-dos-celdas-dos-celdas-dos
  (restriccion (valor ?v1) (casillas ?i1 ?i2))
  (restriccion (valor ?v2) (casillas ?i3 ?i2))
  ?h1 <- (celda (id ?i1) (rango ?r1 ?r2))
  ?h2 <- (celda (id ?i2) (rango ?r1 ?r2))
  ?h3 <- (celda (id ?i3))
  (test (>= ?r2 ?v2))
  (test (<  ?r1 ?v2))
  =>
  (modify ?h1 (rango ?r2))
  (modify ?h2 (rango ?r1))
  (modify ?h3 (rango (- ?v2 ?r1)))
)

(defrule interseccion-dos-celdas-dos-celdas-tres
  (restriccion (valor ?v1) (casillas ?i1 ?i2))
  (restriccion (valor ?v2) (casillas ?i2 ?i3))
  ?h1 <- (celda (id ?i1))
  ?h2 <- (celda (id ?i2) (rango ?r1 ?r2))
  ?h3 <- (celda (id ?i3) (rango ?r1 ?r2))
  (test (>= ?r2 ?v1))
  (test (<  ?r1 ?v1))
  =>
  (modify ?h1 (rango (- ?v1 ?r1)))
  (modify ?h2 (rango ?r1))
  (modify ?h3 (rango ?r2))
)

;; Resuelve interseccion de dos restricciones una de dos celdas y otra de tres
(defrule valor-unico-tres-celdas-dos-celdas
  (restriccion (valor ?v1) (casillas ?i1 ?i2 ?i3))
  (restriccion (valor ?v2) (casillas ?i4 ?i2))
  ?h2 <- (celda (id ?i2) (rango ?r1 ?r2))
  ?h4 <- (celda (id ?i4) (rango ?r1 ?r2))
  ?h1 <- (celda (id ?i1) (rango ? ? $?))
  (test (<= ?v2 ?r2))
  (test (> ?v2 ?r1))
  =>
  (modify ?h2 (rango ?r1))
  (modify ?h1 (rango ?r2))
  (modify ?h4 (rango (- ?v2 ?r1)))
)

(defrule valor-unico-tres-celdas-dos-celdas-dos
  (restriccion (valor ?v1) (casillas ?i1 ?i2 ?i3))
  (restriccion (valor ?v2) (casillas ?i4 ?i3))
  ?h3 <- (celda (id ?i3) (rango ?r1 ?r2))
  (test (<= ?v2 ?r2))
  (test (> ?v2 ?r1))
  =>
  (modify ?h3 (rango ?r1))
)

(defrule valor-unico-dos-valores
  (restriccion (valor ?v1) (casillas ?i1 $?))
  ?h1 <- (celda (id ?i1) (rango ?r1 ?r2))
  (test (>= ?r2 ?v1))
  =>
  (modify ?h1 (rango ?r1))
)

(defrule valor-unico-tres-valores
  (restriccion (valor ?v1) (casillas ?i1 $?))
  ?h1 <- (celda (id ?i1) (rango ?r1 ?r2 ?r3))
  (test (and(>= ?r2 ?v1)
            (>= ?r3 ?v1)))
  =>
  (modify ?h1 (rango ?r1))
)

(defrule valor-unico-interseccion-tres-dos-celdas-ultimo
  (restriccion (valor ?v1) (casillas ?i1 ?i2 ?i3))
  (restriccion (valor ?v2) (casillas ?i3 ?i4))
  ?h1 <- (celda (id ?i1) (rango ?r1))
  ?h3 <- (celda (id ?i3) (rango ?r2 ?r3))
  (test (> (- ?v1 (+ ?r1 ?r2)) 9))
  =>
  (modify ?h3 (rango ?r3))
)

(defrule valor-unico-interseccion-tres-dos-celdas-primero
  (restriccion (valor ?v1) (casillas ?i1 ?))
  (restriccion (casillas ?i1 ? ?))
  ?h1 <- (celda (id ?i1) (rango ?r1 ?r2))
  (test (<= ?v1 ?r2))
  =>
  (modify ?h1 (rango ?r1))
)

(defrule valor-unico-interseccion-tres-dos-celdas-medio
  (restriccion (valor ?v1) (casillas ?i1 ?i2 ?i3))
  (restriccion (valor ?v2) (casillas ?i4 ?i2))
  ?h2 <- (celda (id ?i2) (rango ?r1 ?r2))
  (test (>= ?r2 ?v2))
  =>
  (modify ?h2 (rango ?r1))
)

(defrule resolver-valor-unico-interseccion-dos-celdas
  (restriccion (valor ?v1) (casillas ?i1 ?i2))
  (restriccion (valor ?v2) (casillas ?i2 ?i3))
  ?h1 <- (celda (id ?i1) (rango ? ? $?))
  ?h2 <- (celda (id ?i2) (rango ?r1 ?r2))
  ?h3 <- (celda (id ?i3) (rango ?r1 ?r2))
  (test (< 9 (- ?v1 ?r1)))
  =>
  (modify ?h2 (rango ?r2))
  (modify ?h3 (rango ?r1))
  (modify ?h1 (rango (- ?v1 ?r2)))
)

(defrule resolver-interseccion-dos-dos-dos-celdas
  (restriccion (valor ?v1) (casillas ?i1 ?i2))
  (restriccion (valor ?v2) (casillas ?i2 ?i3))
  (restriccion (valor ?v3) (casillas ?i4 ?i3))
  ?h1 <- (celda (id ?i1) (rango ?r1 ?r2))
  ?h2 <- (celda (id ?i2) (rango ?r1 ?r2))
  ?h3 <- (celda (id ?i3) (rango ?r3 ?r4))
  ?h4 <- (celda (id ?i4) (rango ?r3 ?r4))
  (test (and (eq ?r4 (- ?v2 ?r1))
             (neq ?r3 (- ?v2 ?r2))))
  =>
  (modify ?h2 (rango ?r1))
  (modify ?h1 (rango ?r2))
  (modify ?h3 (rango ?r4))
  (modify ?h4 (rango ?r3))
)

(defrule resolver-interseccion-dos-dos-dos-celdas-dos
  (restriccion (valor ?v1) (casillas ?i1 ?i2))
  (restriccion (valor ?v2) (casillas ?i1 ?i3))
  (restriccion (valor ?v3) (casillas ?i3 ?i4))
  ?h1 <- (celda (id ?i1) (rango ?r1 ?r2))
  ?h2 <- (celda (id ?i2) (rango ?r1 ?r2))
  ?h3 <- (celda (id ?i3) (rango ?r3 ?r4))
  ?h4 <- (celda (id ?i4) (rango ?r3 ?r4))
  (test (and (eq ?r4 (- ?v2 ?r1))
             (neq ?r3 (- ?v2 ?r2))))
  =>
  (modify ?h2 (rango ?r2))
  (modify ?h1 (rango ?r1))
  (modify ?h3 (rango ?r4))
  (modify ?h4 (rango ?r3))
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

(defrule imprime-solucion
  (declare (salience -10))
  =>
  (printout t "+---------+" crlf "|")
  (assert (imprime 1 1)))

(defrule imprime-celda-1
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

(defrule imprime-celda-2
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

;;;============================================================================
