(deftemplate restriccion
  (slot id)
  (slot valor)
  (multislot casillas)
)

(deftemplate celda
  (slot id)
  (multislot rango
             (default (create$ 1 2 3 4 5 6 7 8 9))))

(deffacts f
  (restriccion (id 0) (valor 4) (casillas 1 2 3 4))
  (celda (id 1)(rango 3))
  (celda (id 2)(rango 1 2 3 4 5 6))
  (celda (id 6)(rango 6 7 8 9))
  (celda (id 3)(rango 1 3 4))
  (celda (id 4) (rango 1))
)

(defrule imprimir
  (restriccion (casillas ?i1 ?i2 ?i3))
  ?h1 <- (celda (id ?i1) (rango $?v1))
  ?h2 <- (celda (id ?i2) (rango $?v2))
  ?h3 <- (celda (id ?i3) (rango $?v3))
  ?h4 <- (celda (id ?i3) (rango $?v4))
  =>
  (printout t "..." $?v1 crlf)
  (printout t "..." $?v2 crlf)
  (printout t "..." $?v3 crlf)
  (printout t "..." $?v4 crlf)
)

(defrule eliminar-valores-mayores-restriccion
  (restriccion (valor ?v) (casillas $? ?i $?))
  ?h1 <- (celda (id ?i) (rango $?v1 ?v2))
  (test (>= ?v2 ?v))
  =>
  (modify ?h1 (rango $?v1))
  (printout t "..." $?v1 "........(Eliminando " ?v2 " )" crlf)
)

(defrule eliminar-valor-rango
  (restriccion (casillas $? ?i2 $? ?i1))
  ?h1 <- (celda (id ?i1) (rango ?v1))
  ?h2 <- (celda (id ?i2) (rango $?v2 ?v1 $?v3))
  =>
  (modify ?h2 (rango $?v2 $?v3))
)

(defrule no-valores-mayores
  (declare (salience -10))
  (restriccion (casillas ?i1 ?i2 ?i3 ?i4))
  ?h1 <- (celda (id ?i1) (rango $?v1))
  ?h2 <- (celda (id ?i2) (rango $?v2))
  ?h3 <- (celda (id ?i3) (rango $?v3))
  ?h4 <- (celda (id ?i4) (rango $?v4))
  =>
  (printout t "fin" $?v1 crlf)
  (printout t "fin" $?v2 crlf)
  (printout t "fin" $?v3 crlf)

  (printout t "fin" $?v4 crlf)
)
