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
{struct CId ([String : String]) #:transparent}

{define-data Line
  (Return [Value : Value])
  (Block [Lines : (Listof Line)])
  (DefVar [Id : Id] [Value : Value])
  (VarSet! [Left : Left] [Value : Value])
  (DefStruct [Id : Id] [List : (Listof (Pairof Type Id))])}

{define-data Type
  (TypeC [CId : CId])
  (TypeStruct [Id : Id])
  (TypeCStruct [CId : CId])}

{define-type Value (U Left Apply Function (Pairof Value (Listof Line)))}
{define-type Left (U Id CId Dot DotC (Pairof Left (Listof Line)))}
{struct Apply ([f : Value] [List : (Listof Value)]) #:transparent}
{struct Dot ([Value : Value] [Id : Id]) #:transparent}
{struct DotC ([Value : Value] [CId : CId]) #:transparent}
{struct Function ([args : (Listof (Pairof Type Id))] [result : Type] [Lines : (Listof Line)])}

{define alphabet (list->set (string->list "qwertyuiopasdfghjklzxcvbnmQWERTYUIOPASDFGHJKLZXCVBNM"))}
{define alphabetdi (list->set (string->list "qwertyuiopasdfghjklzxcvbnmQWERTYUIOPASDFGHJKLZXCVBNM1234567890"))}
(: Id->CId (-> Id CId))
{define (Id->CId x) (CId (Id-String x))}
{: Id-String (-> Id String)}
{define (Id-String x)
  (list->string
   {let loop ([xs (string->list (symbol->string (Id-Symbol x)))] [s : (U 'h 'm 'b) 'h])
     (if (null? xs)
         (string->list (apply string-append (add-between (cons "_LFC" (map {λ (x) (number->string x)} (Id-addr x))) "_")))
         {let ([x (car xs)] [xs (cdr xs)])
           {case s
             [(h)
              (if (set-member? alphabet x)
                  (cons x (loop xs 'm))
                  (loop xs 'h))]
             [(m)
              (if (set-member? alphabetdi x)
                  (cons x (loop xs 'm))
                  (loop xs 'b))]
             [(b)
              (if (set-member? alphabetdi x)
                  (cons #\_ (cons x (loop xs 'm)))
                  (loop xs 'b))]}})})}

{define globalS first}
{define mainS second}
{define localS third}
{define valueS fourth}

{: typedefs-Line->global-main-local (-> (Mutable-HashTable Type String) Line (List String String String))}
{define (typedefs-Line->global-main-local m l)
  {cond
    [(Block? l)
     {let ([xs (map {λ ([x : Line]) (typedefs-Line->global-main-local m x)} (Block-Lines l))])
       (list (apply string-append (map {ann globalS (-> (List String String String) String)} xs))
             (apply string-append (map {ann mainS (-> (List String String String) String)} xs))
             (apply string-append (map {ann localS (-> (List String String String) String)} xs)))}]
    [(DefVar? l) (raise 'WIP)]
    [else (raise 'WIP)]}}

{: typedefs-Value->global-main-local-value (-> (Mutable-HashTable Type String) Value (List String String String String))}
{define (typedefs-Value->global-main-local-value m v)
  (cond
    [(Id? v) (list "" "" "" (CId-String (Id->CId v)))]
    [(CId? v) (list "" "" "" (CId-String v))]
    [(Dot? v) {let ([x (typedefs-Value->global-main-local-value m (Dot-Value v))])
                (list (globalS x) (mainS x) (localS x) (string-append "("(valueS x)")."(CId-String (Id->CId (Dot-Id v)))))}]
    [else (raise 'WIP)])}
