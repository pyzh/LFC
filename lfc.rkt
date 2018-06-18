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
;{define (any? x) #t}
;{define-syntax-rule {is? x t}
;  {with-handlers ([any? (λ (e) #f)]) {cast x t} #t}}
{define-syntax-rule {define/memroize (f x ...) v ...}
  {define f
    {let ([h (make-hash)])
      (define/memroize%help%ref h (x ...) {begin v ...})}}}
{define-syntax define/memroize%help%ref
  {syntax-rules ()
    [(_ h () v) (hash-ref! h '() {λ () v})]
    [(_ h (x . xs) v) (define/memroize%help%ref (hash-ref! h x make-hash) xs v)]}}

{struct Id ([String : String])}

{struct Val ([ValLeft : (Maybe ValLeftValue)] [ValValue : (Maybe ValValue)] [ValType : (Maybe ValType)] [ValFunc : (Maybe ValFunc)])}
{struct ValValue ([ValValueValue : ValValueValue] [Lines : Lines])}
{define-type ValValueValue (U Id)} ; WIP
{struct ValType ([Type : Type] [Lines : Lines])}
{struct ValFunc ()} ; WIP
{struct ValLeftValue ()} ; WIP

{define-type Lines (Listof Line)}
{define-data Line
  (DefVar [Id : Id] [Val : Val])
  (DefVarEmpty [Id : Id])
  (Set! [Left : Left] [Val : Val])
  (DefStruct [Id : Id] [List : (Listof (Pairof Type Id))])
  }

{struct Dot ([x : Val] [y : Id])}
{struct RefRead ([x : Val])}
{define-type Left (U Id Dot RefRead)} ; WIP

{define-type Expr
  (U
   (Refine [s : Symbol] (not (: s '!)))
   (Pairof Expr (Listof Expr))
   (Pairof '! (Pairof Expr (Listof Expr))) ; {m x ...}
   )}

{define-data Type
  (TypeF [String : String])
  (TypeStruct [String : String])
  (TypeUnion [String : String])
  (TypeArrow [args : (Listof Type)] [result : Type])
  (TypeRef [Type : Type])
  }

{define-type Macro (U)} ; WIP
