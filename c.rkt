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

{struct Id ([addr : (Listof Natural)] [Symbol : Symbol]) #:transparent}
{struct IdC ([String : String]) #:transparent}
{define-type IdU (U Id IdC)}

{define-data Line
  (Return [Value : Value])
  (Block [Lines : (Listof Line)])
  (DefVar [Id : Id] [Value : Value])
  (VarSet! [Left : Left] [Value : Value])
  (DefFuncGlobal [IdU : IdU] [Func : Func])
  (DefStruct [IdU : IdU] [List : (Listof (Pairof Type IdU))])}

{define-data Type
  (TypeArrow [args : (Listof Type)] [result : Type])
  (TypeIdC [IdC : IdC])
  (TypeStruct [Id : Id])
  (TypeStructC [IdC : IdC])}

{define-type Value (U Left Apply Func (Pairof Value (Listof Line)))}
{define-type Left (U Id IdC Dot DotC (Pairof Left (Listof Line)))}
{struct Apply ([f : Value] [Values : (Listof Value)]) #:transparent}
{struct Dot ([Value : Value] [Id : Id]) #:transparent}
{struct DotC ([Value : Value] [IdC : IdC]) #:transparent}
{struct Func ([args : (Listof (Pairof Type Id))] [result : Type] [Lines : (Listof Line)])}

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
          (string->list (apply string-append (add-between (cons "_LFC" (map {λ (x) (number->string x)} (Id-addr x))) "_")))
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
    [else (raise 'WIP)]}}

{: typedefs-Value->decls-global-main-localdecls-local-value
   (-> typedefs Value (List String String String String String String))}
{define (typedefs-Value->decls-global-main-localdecls-local-value m v)
  {cond
    [(Id? v) (list "" "" "" "" "" (Id-String v))]
    [(IdC? v) (list "" "" "" "" "" (IdC-String v))]
    [(Dot? v)
     {let ([x (typedefs-Value->decls-global-main-localdecls-local-value m (Dot-Value v))])
       (list (declsS x) (globalS x) (mainS x) (localdeclsS x) (localS x) (string-append "("(valueS x)")."(Id-String (Dot-Id v))))}]
    [(DotC? v)
     {let ([x (typedefs-Value->decls-global-main-localdecls-local-value m (DotC-Value v))])
       (list (declsS x) (globalS x) (mainS x) (localdeclsS x) (localS x) (string-append "("(valueS x)")."(IdC-String (DotC-IdC v))))}]
    [(Apply? v)
     {let ([f (typedefs-Value->decls-global-main-localdecls-local-value m (Apply-f v))]
           [xs (map {λ ([x : Value]) (typedefs-Value->decls-global-main-localdecls-local-value m x)} (Apply-Values v))])
       (list
        (apply string-append (declsS f) (map declsS xs))
        (apply string-append (globalS f) (map globalS xs))
        (apply string-append (mainS f) (map mainS xs))
        (apply string-append (localdeclsS f) (map localdeclsS xs))
        (apply string-append (localS f) (map localS xs))
        (string-append "("(valueS f)")("(apply string-append (add-between (map valueS xs) ","))")"))}]
    [(Func? v)
     {let ([args (map {λ ([x : (Pairof Type Id)])
                        (cons (typedefs-Type->type m (car x))
                              (cdr x))} (Func-args v))])
       (raise 'WIP)}]
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
        [(TypeStruct? t) (cons '() (string-append "struct "(Id-String (TypeStruct-Id t))))]
        [(TypeStructC? t) (cons '() (string-append "struct "(IdC-String (TypeStructC-IdC t))))]
        [(TypeArrow? t)
         (typedefs-Type->type m (TypeArrow-result t))
         {let ([args (map {λ ([x : Type]) (typedefs-Type->type m x) (hash-ref m x)} (TypeArrow-args t))]
               [result (hash-ref m (TypeArrow-result t))])
           (cons (append (apply append (car result) (map {ann car (-> (Pairof (Listof String) String) (Listof String))} args)) (list (raise 'WIP))) (raise 'WIP))}]
        [else (raise 'WIP)]}}))}
