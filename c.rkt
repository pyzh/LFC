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
       {struct (c ...) ons (f ...)} ...
       {define-type (t c ...) (U (ons c ...) ...)}}]
    [(_ t (ons f ...) ...)
     {begin
       {struct ons (f ...)} ...
       {define-type t (U ons ...)}}]}}
{define-type (Maybe a) (U a False)}
{define-type (Map k v) (Immutable-HashTable k v)}

{struct Id ([addr : (Listof Natural)] [Symbol : Symbol])}
{struct CId ([String : String])}

{define-data Line
  (Block [Lines : (Listof Line)])
  (DefVar [Id : Id] [Value : Value])
  (VarSet! [Left : Left] [Value : Value])
  (DefStruct [Id : Id] [List : (Listof (Pairof Type Id))])}

{define-data Type
  (TypeF [CId : CId])
  (TypeStruct [Id : Id])
  (TypeFStruct [CId : CId])}

{define-type Value (U Left Apply)}
{define-type Left (U Id CId Dot DotF)}
{struct Apply ([f : Value] [List : (Listof Value)])}
{struct Dot ([x : Value] [f : Id])}
{struct DotF ([x : Value] [f : CId])}

{define alphabet (list->set (string->list "qwertyuiopasdfghjklzxcvbnmQWERTYUIOPASDFGHJKLZXCVBNM"))}
{define alphabetdi (list->set (string->list "qwertyuiopasdfghjklzxcvbnmQWERTYUIOPASDFGHJKLZXCVBNM1234567890"))}
(: Id->CId (-> Id CId))
{define (Id->CId x)
  (CId (list->string
        {let loop ([xs (string->list (symbol->string (Id-Symbol x)))] [s : (U 'h 'm 'b) 'h])
          (if (null? xs)
              (string->list (apply string-append (add-between (cons "_LFC" (map {λ (x) (number->string x)} (Id-addr x))) "_")))
              {let ([x (car xs)] [xs (cdr xs)])
                (case s
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
                       (loop xs 'b))])})}))}
                       