### KAKURO CLIPS

## 0. ESTRUCTURA DEL PROYECTO
En este proyecto se han utilizado cinco módulos distintos:


1. MAIN: Se encarga de la lectura del problema.
2. VALORES-INICIALES: Se encarga de eliminar del rango aquellos valores que forman parte de una casilla con suma única.
3. RESOLVER: Se encarga de resolver restricciones.
4. ELIMINAR-VALORES: Se encarga de eliminar valores del rango mediante distintas estrategias.
5. IMPRIMIR: Se encarga de imprimir por pantalla el kakuro.


## 1. MÓDULO MAIN
Contiene los métodos de lectura, las plantillas iniciales así como la carga de los módulos a ejecutar.

## 2. MÓDULO VALORES-INICIALES
Contiene las sumas únicas desde dos celdas hasta las de seis celdas.

## 3. MÓDULO RESOLVER
Contiene dos reglas de control de flujo del problema. En ellas se controla si se han utilizado las reglas de este módulo o no, para pasar al módulo adecuado.
Además, contiene dos reglas: una que resuelve restricciones de una sola casilla, comprobando que el valor esté en el rango; la otra, resuelve un caso concreto.

## 4. MÓDULO ELIMINAR-VALORES
Contiene las reglas que eliminan valores del rango de las celdas y dos reglas de control de flujo para pasar al módulo correcto.


* eliminar-sumas-imposibles-dos-celdas: Elimina aquellos valores imposibles en la suma de valores para alcanzar el valor de la restriccion de dos celdas.
* eliminar-valor-existente-en-restriccion: Elimina del rango de todas las celdas de la restriccion aquellos valores asignados a otra celda de la misma restriccion.
* 

## 5. MÓDULO IMPRIMIR
Contiene las reglas encargadas de imprimir el kakuro con un correcto formato.
