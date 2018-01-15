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
             (default (create$ 1 2 3 4 5 6 7 8 9))
  )
)

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
  (focus VALORES-INICIALES ELIMINAR-VALORES)
)

(deffacts inicial
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
  (restriccion (valor 15) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4) (rango 1 2 3 4 5 ? $?)))
  =>
  (modify ?h1 (rango 1 2 3 4 5))
  (modify ?h2 (rango 1 2 3 4 5))
  (modify ?h3 (rango 1 2 3 4 5))
  (modify ?h4 (rango 1 2 3 4 5))
)

;;;;;;;; La suma igual a 16 en cuatro celdas toma los valores 1, 2, 3, 4 y 6
(defrule VALORES-INICIALES::cinco-celdas-suma-deiciseis
  (restriccion (valor 15) (casillas ?id1 ?id2 ?id3 ?id4))
  ?h1 <- (celda (id ?id1))
  ?h2 <- (celda (id ?id2))
  ?h3 <- (celda (id ?id3))
  ?h4 <- (celda (id ?id4))
  (exists (celda (id ?id&?id1|?id2|?id3|?id4) (rango 1 2 3 4 $? 6 ? $?)))
  =>
  (modify ?h1 (rango 1 2 3 4 6))
  (modify ?h2 (rango 1 2 3 4 6))
  (modify ?h3 (rango 1 2 3 4 6))
  (modify ?h4 (rango 1 2 3 4 6))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmodule RESOLVER (import VALORES-INICIALES ?ALL) (export ?ALL))
(defrule RESOLVER::no-nuevo-valor
  (declare (salience -10))
  (no-nuevo-valor)
  =>
  (focus IMPRIMIR)
)

(defrule RESOLVER::nuevo-valor
  (declare (salience -10))
  ?h <- (nuevo-valor)
  =>
  (retract ?h)
  (assert (no-eliminado))
  (focus ELIMINAR-VALORES)
)

(defrule RESOLVER::completar-restriccion-dos-celdas
  (restriccion (valor ?v) (casillas ?i1 ?i2))
  ?h1 <- (celda (id ?i3&?i1|?i2) (rango ?v1))
  ?h2 <- (celda (id ?i4&?i1|?i2) (rango ? ? $?))
  =>
  (modify ?h2 (rango (- ?v ?v1)))
  (assert (nuevo-valor))
)

(defrule RESOLVER::completar-restriccion-tres-celdas
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3))
  ?h1 <- (celda (id ?i4&?i1|?i2|?i3) (rango ?v1))
  ?h2 <- (celda (id ?i5&?i1|?i2|?i3) (rango ?v2&~?v1))
  ?h3 <- (celda (id ?i6&?i1|?i2|?i3) (rango ? ? $?))
  =>
  (modify ?h3 (rango (- ?v (+ ?v1 ?v2))))
  (assert (nuevo-valor))
)

(defrule RESOLVER::completar-restriccion-cuatro-celdas
  (restriccion (valor ?v) (casillas ?i1 ?i2 ?i3 ?i4))
  ?h1 <- (celda (id ?i5&?i1|?i2|?i3|?i4) (rango ?v1))
  ?h2 <- (celda (id ?i6&?i1|?i2|?i3|?i4) (rango ?v2&~?v1))
  ?h3 <- (celda (id ?i7&?i1|?i2|?i3|?i4) (rango ?v3&~?v1&~?v2))
  ?h4 <- (celda (id ?i8&?i1|?i2|?i3|?i4) (rango ? ? $?))
  (test (and (neq ?i5 ?i6) (neq ?i5 ?i7) (neq ?i6 ?i7)))
  =>
  (modify ?h4 (rango (- ?v (+ ?v1 ?v2 ?v3))))
  (assert (nuevo-valor))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmodule ELIMINAR-VALORES (import RESOLVER ?ALL) (export ?ALL))

(defrule ELIMINAR-VALORES::eliminado
  (declare (salience -10))
  ?h <- (eliminado)
  =>
  (retract ?h)
  (assert (no-nuevo-valor))
  (focus RESOLVER)
)

(defrule ELIMINAR-VALORES::no-eliminado
  (declare (salience -10))
  (no-eliminado)
  =>
  (focus IMPRIMIR)
)

(defrule ELIMINAR-VALORES::eliminar-valores-rango-mayor-que-restriccion
  (restriccion (valor ?v) (casillas $? ?i $?))
  ?h <- (celda (id ?i) (rango $?v1 ?v2))
  (test (>= ?v2 ?v))
  =>
  (modify ?h (rango $?v1))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::eliminar-valores-rango-dos-celdas-imposibles-mayor-9
  (restriccion (valor ?v) (casillas ?i1 ?i2))
  ?h <- (celda (id ?i3))
  (or (and (celda (id ?i3&?i1) (rango $?v1 ?r $?v2))
           (test (> (- ?v ?r) 9))
           (not (celda (id ?i3) (rango ?))))
      (and (celda (id ?i3&?i2) (rango $?v1 ?r $?v2))
           (test (> (- ?v ?r) 9))
           (not (celda (id ?i3) (rango ?))))
  )
  =>
  (modify ?h (rango $?v1 $?v2))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::eliminar-valores-rango-dividir-entre-dos
  (restriccion (valor ?v) (casillas ?i1 ?i2))
  ?h <- (celda (id ?i3))
  (or (and (celda (id ?i3&?i1) (rango $?v1 ?r $?v2))
           (test (eq ?v (* ?r 2))))
      (and (celda (id ?i3&?i2) (rango $?v1 ?r $?v2))
           (test (eq ?v (* ?r 2)))))
  =>
  (modify ?h (rango $?v1 $?v2))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::eliminar-valor-existente-en-restriccion
  (restriccion (casillas $? ?i1 $? ?i2 $?))
  (celda (id ?i3) (rango ?v))
  ?h <- (celda (id ?i4) (rango $?vi ?v $?vd))
  (or (and (celda (id ?i4&?i1))
           (celda (id ?i3&?i2)))
      (and (celda (id ?i4&?i2))
           (celda (id ?i3&?i1))))
  =>
  (modify ?h (rango $?vi $?vd))
  (assert (eliminado))
)

(defrule ELIMINAR-VALORES::eliminar-valores-rango-dos-celdas-imposibles-no-rango-paso
  (restriccion (valor ?v) (casillas ?i1 ?i2))
  ?h1 <- (celda (id ?i1) (rango ?v1 ?v2))
  ?h2 <- (celda (id ?i2))
  =>
  (assert (prueba (valor (- ?v ?v2)) (id1 ?i1) (id2 ?i2)))
)

(defrule ELIMINAR-VALORES::paso-dos
  (prueba (valor ?v) (id1 ?i1) (id2 ?i2))
  ?h1 <- (celda (id ?i1) (rango ?v1 ?v2))
  ?h2 <- (celda (id ?i2))
  (not (celda (id ?i2) (rango $? ?v $?)))
  =>
  (modify ?h1 (rango ?v1))
  (assert (eliminado))
)


(defrule ELIMINAR-VALORES::eliminar-sumas-imposibles-dos-celdas
  (restriccion (valor ?v) (casillas ?i1 ?i2))
  (celda (id ?i4) (rango ?x ?y))
  ?h <- (celda (id ?i3&~?i4) (rango $?v1 ?r $?v2))
  (or (and (celda (id ?i4&?i1))
           (celda (id ?i3&?i2))
           (test (neq ?v (+ ?r ?x)))
           (test (neq ?v (+ ?r ?y))))
      (and (celda (id ?i4&?i2))
           (celda (id ?i3&?i1))
           (test (neq ?v (+ ?r ?x)))
           (test (neq ?v (+ ?r ?y))))
  )
  =>
  (modify ?h (rango $?v1 $?v2))
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
