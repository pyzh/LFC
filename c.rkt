;    LFC
;    Copyright (C) 2018  Zaoqi
;
;    This program is free software: you can redistribute it and/or modify
;    it under the terms of the GNU Affero General Public License as published
;    by the Free Software Foundation, either version 3 of the License, or
;    (at your option) any later version.
;
;    This program is distributed in the hope that it will be useful,
;    but WITHOUT ANY WARRANTY; without even the implied warranty of
;    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;    GNU Affero General Public License for more details.
;
;    You should have received a copy of the GNU Affero General Public License
;    along with this program.  If not, see <http://www.gnu.org/licenses/>.
#lang typed/racket #:with-refinements
{define-syntax define-data
  {syntax-rules ()
    [(_ (t c ...) (ons f ...) ...)
     {begin
       {struct (c ...) ons (f ...) #:transparent} ...
       {define-type (t c ...) (U (ons c ...) ...)}}]
    [(_ t (ons f ...) ...)
     {begin
       {struct ons (f ...) #:transparent} ...
       {define-type t (U ons ...)}}]}}
{define-type (Maybe a) (U a False)}
{define-type (Map k v) (Immutable-HashTable k v)}
{: string-add-between (-> (Listof String) String String)}
{define (string-add-between xs a) (apply string-append (add-between xs a))}

{struct Id ([addr : (Listof String)] [Symbol : Symbol]) #:transparent}
{struct IdC ([String : String]) #:transparent}
{define-type IdU (U Id IdC)}

{define-data Line
  (Return [Value : Value])
  (Block [Lines : (Listof Line)])
  (DefVar [Id : Id] [Type : Type] [Value : Value])
  (DefVarGlobal [IdU : IdU] [Type : Type] [Value : Value])
  (VarSet! [Left : Left] [Value : Value])
  (DefFuncGlobal [IdU : IdU] [Func : Func])
  (DefStruct [IdU : IdU] [List : (Listof (Pairof Type IdU))])}
{struct Func ([args : (Listof (Pairof Type Id))] [result : Type] [Lines : (Listof Line)])}

{define-data Type
  (TypeArrow [args : (Listof Type)] [result : Type])
  (TypeIdC [IdC : IdC])
  (TypeStruct [IdU : IdU])}

{define-type Value (U Left Apply (Pairof Value (Listof Line)))}
{define-type Left (U IdU Dot (Pairof Left (Listof Line)))}
{struct Apply ([f : Value] [Values : (Listof Value)]) #:transparent}
{struct Dot ([Value : Value] [IdU : IdU]) #:transparent}

{define c 0}
{define (gen-lfc-str)
  (set! c (+ c 1))
  (string-append "LFC_"(number->string c)"_T")}

{define alphabet (list->set (string->list "qwertyuiopasdfghjklzxcvbnmQWERTYUIOPASDFGHJKLZXCVBNM"))}
{define alphabetdi (list->set (string->list "qwertyuiopasdfghjklzxcvbnmQWERTYUIOPASDFGHJKLZXCVBNM1234567890"))}
(: Id->IdC (-> Id IdC))
{define (Id->IdC x) (IdC (Id-String x))}
{: Id-String (-> Id String)}
{define (Id-String x)
  (string-append
   "LFC"
   (list->string
    {let loop ([xs (string->list (symbol->string (Id-Symbol x)))] [s : (U 'm 'b) 'b])
      (if (null? xs)
          (string->list (apply string-append (add-between (cons "_LFC" (Id-addr x)) "_")))
          {let ([x (car xs)] [xs (cdr xs)])
            {case s
              [(m)
               (if (set-member? alphabetdi x)
                   (cons x (loop xs 'm))
                   (loop xs 'b))]
              [(b)
               (if (set-member? alphabetdi x)
                   (cons #\_ (cons x (loop xs 'm)))
                   (loop xs 'b))]}})}))}

{: IdU-String (-> IdU String)}
{define (IdU-String i) (if (IdC? i) (IdC-String i) (Id-String i))}

{: declsS (-> (Listof String) String)}
{define declsS first}
{: globalS (-> (Listof String) String)}
{define globalS second}
{: mainS (-> (Listof String) String)}
{define mainS third}
{: localdeclsS (-> (Listof String) String)}
{define localdeclsS fourth}
{: localS (-> (Listof String) String)}
{define localS fifth}
{: valueS (-> (Listof String) String)}
{define valueS sixth}

{define-type typedefs (Mutable-HashTable Type (Pairof (Listof String) String))} ; decl / type ; List用來說明依賴，刪除重複。

{: typedefs-Lines->decls-global-main-localdecls-local
   (-> typedefs (Listof Line) (List String String String String String))}
{define (typedefs-Lines->decls-global-main-localdecls-local m ls)
  (typedefs-Line->decls-global-main-localdecls-local m (Block ls))}

{: typedefs-Line->decls-global-main-localdecls-local
   (-> typedefs Line (List String String String String String))}
{define (typedefs-Line->decls-global-main-localdecls-local m l)
  {cond
    [(Block? l)
     {let ([xs (map {λ ([x : Line]) (typedefs-Line->decls-global-main-localdecls-local m x)} (Block-Lines l))])
       (list
        (apply string-append (map declsS xs))
        (apply string-append (map globalS xs))
        (apply string-append (map mainS xs))
        (apply string-append (map localdeclsS xs))
        (apply string-append (map localS xs)))}]
    [(DefVar? l) (raise 'WIP)]
    [(DefFuncGlobal? l)
     {let ([f (DefFuncGlobal-Func l)] [n (IdU-String (DefFuncGlobal-IdU l))])
     {let ([args (map {λ ([x : (Pairof Type Id)]) (cons (typedefs-Type->type m (car x)) (cdr x))} (Func-args f))]
           [result (typedefs-Type->type m (Func-result f))]
           [ls (typedefs-Lines->decls-global-main-localdecls-local m (Func-Lines f))])
       (list
        (string-append (declsS ls) result" "n"("(string-add-between (map {ann car (-> (Pairof String Id) String)} args) ",")");")
        (globalS ls) ;WIP
        (mainS ls)
        ""
        "")}}]
    [else (raise 'WIP)]}}

{: typedefs-Value->decls-global-main-localdecls-local-value
   (-> typedefs Value (List String String String String String String))}
{define (typedefs-Value->decls-global-main-localdecls-local-value m v)
  {cond
    [(Id? v) (list "" "" "" "" "" (Id-String v))]
    [(IdC? v) (list "" "" "" "" "" (IdC-String v))]
    [(Dot? v)
     {let ([x (typedefs-Value->decls-global-main-localdecls-local-value m (Dot-Value v))])
       (list (declsS x) (globalS x) (mainS x) (localdeclsS x) (localS x) (string-append "("(valueS x)")."(IdU-String (Dot-IdU v))))}]
    [(Apply? v)
     {let ([f (typedefs-Value->decls-global-main-localdecls-local-value m (Apply-f v))]
           [xs (map {λ ([x : Value]) (typedefs-Value->decls-global-main-localdecls-local-value m x)} (Apply-Values v))])
       (list
        (apply string-append (declsS f) (map declsS xs))
        (apply string-append (globalS f) (map globalS xs))
        (apply string-append (mainS f) (map mainS xs))
        (apply string-append (localdeclsS f) (map localdeclsS xs))
        (apply string-append (localS f) (map localS xs))
        (string-append "("(valueS f)")("(string-add-between (map valueS xs) ",")")"))}]
    [(pair? v) (raise 'WIP)]
    [else (raise 'WIP)]}}

{: typedefs-Type->type
   (-> typedefs Type String)}
{define (typedefs-Type->type m t)
  (cdr
   (hash-ref!
    m t
    {λ ()
      {cond
        [(TypeIdC? t) (cons '() (IdC-String (TypeIdC-IdC t)))]
        [(TypeStruct? t)
         {let ([a (string-append "struct "(IdU-String (TypeStruct-IdU t)))])
           (cons `(,(string-append a";")) a)}]
        [(TypeArrow? t)
         (typedefs-Type->type m (TypeArrow-result t))
         {let ([args (map {λ ([x : Type]) (typedefs-Type->type m x) (hash-ref m x)} (TypeArrow-args t))]
               [result (hash-ref m (TypeArrow-result t))])
           (cons (append (apply append (car result) (map {ann car (-> (Pairof (Listof String) String) (Listof String))} args)) (list (raise 'WIP))) (raise 'WIP))}]
        [else (raise 'WIP)]}}))}
