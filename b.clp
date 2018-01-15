(deffacts ini
  (valor 4)
)

(defrule regla
  (valor ?i&1|2|3|4)
  =>
  (printout t "Valor " ?i " aceptado." crlf)
)
