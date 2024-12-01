#lang eopl
(require rackunit)

(define especificacion-lexica
  '(
    (espacio-blanco (whitespace) skip)
    (comentario ("%" (arbno (not #\newline))) skip)
    (identificador (letter (arbno (or letter digit "?" "$"))) symbol)
    (numero (digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)) number)
    (numero (digit (arbno digit)"." digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)"." digit (arbno digit)) number)
    )
  )


(define especificacion-gramatical
   '(
    ;; Programa principal
    (programa (expresion) a-program)

    ;; Expresiones
    (expresion (numero) lit-exp)
    (expresion (identificador) var-exp)

    ;; Booleanos
    (expresion ("true") true-exp)
    (expresion ("false") false-exp)

    ;; Condicionales
    (expresion ("if" expresion "then" expresion "else" expresion) if-exp)

    ;; Ligaduras locales
    (expresion ("let" (arbno identificador "=" expresion) "in" expresion) let-exp)

    ;; Procedimientos
    (expresion ("proc" "(" (separated-list identificador ",") ")" expresion) proc-exp)
    (expresion ("(" expresion (arbno expresion) ")") app-exp)

    ;; Procedimientos recursivos
    (expresion ("letrec" (arbno identificador "(" (separated-list identificador ",") ")" "=" expresion) "in" expresion) letrec-exp)

    ;; Asignación
    (expresion ("begin" expresion (arbno ";" expresion) "end") begin-exp)
    (expresion ("set" identificador "=" expresion) set-exp)

    ;; Primitivas
    (expresion (primitiva "(" (separated-list expresion ",") ")") prim-exp)
    (primitiva ("+") sum-prim)
    (primitiva ("-") minus-prim)
    (primitiva ("*") mult-prim)
    (primitiva ("/") div-prim)
    (primitiva ("add1") add-prim)
    (primitiva ("sub1") sub-prim)
    (primitiva (">") mayor-prim)
    (primitiva (">=") mayorigual-prim)
    (primitiva ("<") menor-prim)
    (primitiva ("<=") menorigual-prim)
    (primitiva ("==") igual-prim)

    ;; Expresiones de listas
    (expresion ("empty") list-empty-exp)
    (expresion ("cons" "(" expresion expresion ")") list-exp)
    (expresion ("length" "(" expresion ")") list-length-exp)
    (expresion ("first" "(" expresion ")") list-first-exp)
    (expresion ("rest" "(" expresion ")") list-rest-exp)
    (expresion ("nth" "(" expresion expresion ")") list-nth-exp)
    ;; Expesiones de cond
  ;;(expresion ("let" (arbno identificador "=" expresion) "in" expresion) let-exp)
    (expresion ("cond" (arbno expresion "-" expresion) "else" expresion "end") cond-exp)
  ))

;;Creamos los datatypes automaticamente
(sllgen:make-define-datatypes especificacion-lexica especificacion-gramatical)

;;Evaluar programa
(define evaluar-programa
  (lambda (pgm)
    (cases programa pgm
      (a-program (exp) (evaluar-expresion exp ambiente-inicial))
      ))
  )

;;ambientes
(define-datatype ambiente ambiente?
  (ambiente-vacio)
  (ambiente-extendido-ref
   (lids (list-of symbol?))
   (lvalue vector?)
   (old-env ambiente?)))

(define ambiente-extendido
  (lambda (lids lvalue old-env)
    (ambiente-extendido-ref lids (list->vector lvalue) old-env)))

;;Implementación ambiente extendido recursivo

(define ambiente-extendido-recursivo
  (lambda (procnames lidss cuerpos old-env)
    (let
        (
         (vec-clausuras (make-vector (length procnames)))
         )
      (letrec
          (
           (amb (ambiente-extendido-ref procnames vec-clausuras old-env))
           (obtener-clausuras
            (lambda (lidss cuerpos pos)
              (cond
                [(null? lidss) amb]
                [else
                 (begin
                   (vector-set! vec-clausuras pos
                                (closure (car lidss) (car cuerpos) amb))
                   (obtener-clausuras (cdr lidss) (cdr cuerpos) (+ pos 1)))]
                )
              )
            )
           )
        (obtener-clausuras lidss cuerpos 0)
        )
      )
    )
  )


(define apply-env
  (lambda (env var)
    (deref (apply-env-ref env var))))


(define apply-env-ref
  (lambda (env var)
    (cases ambiente env
      (ambiente-vacio () (eopl:error "No se encuentra la variable " var))
      (ambiente-extendido-ref (lid vec old-env)
                          (letrec
                              (
                               (buscar-variable (lambda (lid vec pos)
                                                  (cond
                                                    [(null? lid) (apply-env-ref old-env var)]
                                                    [(equal? (car lid) var) (a-ref pos vec)]
                                                    [else
                                                     (buscar-variable (cdr lid) vec (+ pos 1)  )]
                                                    )
                                                  )
                                                )
                               )
                            (buscar-variable lid vec 0)
                            )
                          
                          )
      
      )
    )
  )

(define ambiente-inicial
  (ambiente-extendido '(x y z) '(4 2 5)
                      (ambiente-extendido '(a b c) '(4 5 6)
                                          (ambiente-vacio))))

;;Evaluar expresion
(define evaluar-expresion
  (lambda (exp amb)
    (cases expresion exp
      ;; Literales
      (lit-exp (dato) dato)

      ;; Variables
      (var-exp (id) (apply-env amb id))

      ;; Booleanos
      (true-exp () #true)
      (false-exp () #false)

      ;; Primitivas
      (prim-exp (prim args)
                (let ((lista-numeros (map (lambda (x) (evaluar-expresion x amb)) args)))
                  (evaluar-primitiva prim lista-numeros)))

      ;; Condicionales
      (if-exp (condicion hace-verdadero hace-falso)
              (if (evaluar-expresion condicion amb)
                  (evaluar-expresion hace-verdadero amb)
                  (evaluar-expresion hace-falso amb)))

      ;; Ligaduras locales
      (let-exp (ids rands body)
               (let ((lvalues (map (lambda (x) (evaluar-expresion x amb)) rands)))
                 (evaluar-expresion body (ambiente-extendido ids lvalues amb))))

      ;; Procedimientos
      (proc-exp (ids body)
                (closure ids body amb))
      (app-exp (rator rands)
               (let ((lrands (map (lambda (x) (evaluar-expresion x amb)) rands))
                     (procV (evaluar-expresion rator amb)))
                 (if (procval? procV)
                     (cases procval procV
                       (closure (lid body old-env)
                                (if (= (length lid) (length lrands))
                                    (evaluar-expresion body
                                                       (ambiente-extendido lid lrands old-env))
                                    (eopl:error "El número de argumentos no es correcto, debe enviar"
                                                (length lid)
                                                "y usted ha enviado"
                                                (length lrands)))))
                     (eopl:error "No puede evaluarse algo que no sea un procedimiento" procV))))

      ;; Procedimientos recursivos
      (letrec-exp (procnames idss cuerpos cuerpo-letrec)
                  (evaluar-expresion cuerpo-letrec
                                     (ambiente-extendido-recursivo procnames idss cuerpos amb)))

      ;; Asignación
      ;; Begin
      (begin-exp (exp lexp)
                 (if (null? lexp)
                     (evaluar-expresion exp amb)
                     (begin
                       (evaluar-expresion exp amb)
                       (letrec ((evaluar-begin (lambda (lexp)
                                                 (cond
                                                   [(null? (cdr lexp)) (evaluar-expresion (car lexp) amb)]
                                                   [else
                                                    (begin
                                                      (evaluar-expresion (car lexp) amb)
                                                      (evaluar-begin (cdr lexp)))]))))
                         (evaluar-begin lexp)))))
      ;; Set
      (set-exp (id exp)
               (begin
                 (setref!
                  (apply-env-ref amb id)
                  (evaluar-expresion exp amb))
                 1))

      ;; Expresiones de listas
      (list-empty-exp ()
                       '()) ;; Lista vacía

      (list-exp (valor lista)
                (let ((v (evaluar-expresion valor amb))
                      (l (evaluar-expresion lista amb)))
                  (if (list? l)
                      (cons v l)
                      (eopl:error "Error: No es una lista válida" lista))))

      (list-length-exp (lista)
                       (let ((l (evaluar-expresion lista amb)))
                         (if (list? l)
                             (length l)
                             (eopl:error "Error: No es una lista válida" lista))))

      (list-first-exp (lista)
                      (let ((l (evaluar-expresion lista amb)))
                        (if (and (list? l) (not (null? l)))
                            (car l)
                            (eopl:error "Error: La lista está vacía o no es válida" lista))))

      (list-rest-exp (lista)
                     (let ((l (evaluar-expresion lista amb)))
                       (if (and (list? l) (not (null? l)))
                           (cdr l)
                           (eopl:error "Error: La lista está vacía o no es válida" lista))))

      (list-nth-exp (lista pos)
                    (let ((l (evaluar-expresion lista amb))
                          (n (evaluar-expresion pos amb)))
                      (if (and (list? l) (number? n) (< n (length l)) (>= n 0))
                          (list-ref l n)
                          (eopl:error "Error: Índice fuera de rango o no válido" pos))))


      ;; Expresiones de cond
      (cond-exp (clausulas else-exp amb)
        (let loop ((restantes clausulas))
          (if (null? restantes)
          ;; Si no hay más cláusulas, evalúa y devuelve el else-exp.
          (evaluar-expresion else-exp amb)
          ;; Procesa la primera cláusula.
          (let ((clausula (car restantes)))
            (if (and (pair? clausula) (= (length clausula) 2))
              (let ((condicion (car clausula))
                    (resultado (cadr clausula)))
                (if (evaluar-expresion condicion amb)
                    ;; Si la condición es verdadera, evalúa el resultado.
                    (evaluar-expresion resultado amb)
                    ;; Si es falsa, sigue con las siguientes cláusulas.
                    (loop (cdr restantes))))
              (eopl:error "Formato de cláusula inválido" clausula))))))



      )))


;;Manejo de primitivas
(define evaluar-primitiva
  (lambda (prim lval)
    (cases primitiva prim
      (sum-prim () (operacion-prim lval + 0))
      (minus-prim () (operacion-prim lval - 0))
      (mult-prim () (operacion-prim lval * 1))
      (div-prim () (operacion-prim lval / 1))
      (add-prim () (+ (car lval) 1))
      (sub-prim () (- (car lval) 1))
      (mayor-prim () (> (car lval) (cadr lval)))
      (mayorigual-prim () (>= (car lval) (cadr lval)))
      (menor-prim () (< (car lval) (cadr lval)))
      (menorigual-prim () (<= (car lval) (cadr lval)))
      (igual-prim () (= (car lval) (cadr lval)))
      )
    )
  )


(define operacion-prim
  (lambda (lval op term)
    (cond
      [(null? lval) term]
      [else
       (op
        (car lval)
        (operacion-prim (cdr lval) op term))
       ]
      )
    )
  )

;;Definiciones para los procedimientos
(define-datatype procval procval?
  (closure (lid (list-of symbol?))
           (body expresion?)
           (amb-creation ambiente?)))

;;Referencias

(define-datatype referencia referencia?
  (a-ref (pos number?)
         (vec vector?)))

;;Extractor de referencias
(define deref
  (lambda (ref)
    (primitiva-deref ref)))

(define primitiva-deref
  (lambda (ref)
    (cases referencia ref
      (a-ref (pos vec)
             (vector-ref vec pos)))))

;;Asignación/cambio referencias
(define setref!
  (lambda (ref val)
    (primitiva-setref! ref val)))

(define primitiva-setref!
  (lambda (ref val)
    (cases referencia ref
      (a-ref (pos vec)
             (vector-set! vec pos val)))))


;;Interpretador
(define interpretador
  (sllgen:make-rep-loop "-->" evaluar-programa
                        (sllgen:make-stream-parser
                         especificacion-lexica especificacion-gramatical)))


;;Pruebas Rackunit
(define (run-cond-tests)
  (let ((env (ambiente-vacio)))
    ;; Caso simple con una condición verdadera
    (test-equal? "Simple cond true"
      (evaluar-expresion ("cond" ("-" "x" "1") "-" "1" "else" "9" "end") env)
      1)

    ;; Caso simple con una condición falsa y else
    (test-equal? "Simple cond false with else"
      (evaluar-expresion ("cond" ("-" "x" "2") "-" "2" "else" "9" "end") env)
      9)

    ;; Caso con múltiples condiciones, la primera verdadera
    (test-equal? "Multiple conditions first true"
      (evaluar-expresion ("cond" ("-" "x" "1") "-" "1" ("-" "x" "2") "-" "2" "else" "9" "end") env)
      1)

    ;; Caso con múltiples condiciones, la segunda verdadera
    (test-equal? "Multiple conditions second true"
      (evaluar-expresion ("cond" ("-" "x" "2") "-" "2" ("-" "x" "1") "-" "1" "else" "9" "end") env)
      1)

    ;; Caso con múltiples condiciones, ninguna verdadera, usa else
    (test-equal? "Multiple conditions none true with else"
      (evaluar-expresion ("cond" ("-" "x" "2") "-" "2" ("-" "x" "3") "-" "4" "else" "9" "end") env)
      9)

    ;; Caso con cond anidado
    (test-equal? "Nested cond"
      (evaluar-expresion ("cond" ("cond" ("-" "x" "1") "-" "1" "else" "0" "end") "-" "2" "else" "9" "end") env)
      2)

    ;; Caso con cond vacío, solo else
    (test-equal? "Empty cond with else"
      (evaluar-expresion ("cond" "else" "9" "end") env)
      9)

    (display "All cond tests passed.\n")))

(run-cond-tests)
(interpretador)