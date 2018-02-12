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
* eliminar-valores-rango-dividir-entre-dos: En restricciones de dos celdas, elimina del rango de la celda aquellos valores que sean igual al valor de la restriccion dividido entre dos. Por ejemplo: el valor de la restriccion igual a 6. Elimina del rango el 3.
* eliminar-valores-rango-mayor-que-restriccion: Elimina aquellos valores del rango de la celda que sean mayores que la restriccion.
* pone-valor-interseccion-dos-dos-dos-tres-celdas y pone-valor-interseccion-dos-dos-dos-tres-celdas-v2: Establece un valor en una interseccion formada por tres restricciones de dos celdas y una restriccion de tres celdas.
* pone-valor-unico-restriccion-cuatro-celdas: Establece un valor único en el rango de una celda (que no contienen las demás celdas) en una restriccion de cuatro celdas.
* elimina-valor-suma-imposible-tres-celdas: Elimina valores del rango de una celda perteneciente a una restriccion de tres celdas que hagan imposible la suma igual a la restriccion.
* elimina-valores-suma-imposible-menor-cuatro-celdas, elimina-valor-restriccion-cuatro-celdas-sum-imp-2, elimina-valor-restriccion-4-celdas-suma-imp-3: Elimina valores del rango de una celda perteneciente a una restriccion de cuatro celdas, que hacen imposible igualar la suma de la restriccion.
* elimina-valor-interseccion-tres-tres-dos-dos: Establece un valor en una celda perteneciente a una interseccion de dos restricciones de dos celdas y otras dos restricciones de tres celdas.
* elimina-valor-celda-en-cuadrado-v1: Establece un valor en el rango de una celda perteneciente a un cuadrado. Es decir, tres restricciones de dos celdas.
* pone-valor-unico-restriccion-cinco-celdas: Establece un valor en el rango de una celda perteneciente a una restriccion de cinco celdas.

Además, se incluyen dos reglas más:


* eliminar-celda-restriccion: Elimina una celda con un único valor en el rango de una restriccion, restando el valor de ésta a la restriccion.
* eliminar-restriccion: Elimina la restriccion una vez no tenga celdas.

## 5. MÓDULO IMPRIMIR
Contiene las reglas encargadas de imprimir el kakuro con un correcto formato.
