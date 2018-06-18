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

{struct Id ([String : String])}

{struct Val ([ValLeft : (Maybe ValLeftValue)] [ValValue : (Maybe ValValue)] [ValType : (Maybe ValType)] [ValFunc : (Maybe ValFunc)])}
{struct ValValue ([ValValueValue : ValValueValue] [Lines : Lines])}
{define-type ValValueValue (U Id)} ; WIP
{struct ValType ([Type : Type] [Lines : Lines])}
{struct ValFunc ([f : (-> (Listof Val) Val)])}
{struct ValLeftValue ([Left : Left] [Lines : Lines])} ; WIP

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
  (TypeVoid)
  (TypeF [Id : Id])
  (TypeStruct [Id : Id])
  (TypeUnion [Id : Id])
  (TypeArrow [args : (Listof Type)] [result : Type])
  (TypeRef [Type : Type])
  }

{struct Macro ([f : (-> (Listof Expr) Val)])}

{: compile (-> (Map Id Type) (Map Id (U Val Macro)) Expr Val)}
{define (compile type-env env x)
  {match x
    [(? symbol? x)
     {define r (make-c-id x)}
     (Val (ValLeftValue r '()) (ValValue r '()) (ValType (TypeF r) '()) #f)]
    [`(! ,f ,@xs)
     {match (hash-ref env f)
       [(Macro f) (f xs)]}]
    [`(,f ,@xs)
     {match (hash-ref env f)
       [(Val _ _ _ (ValFunc f)) (f (map {λ (x) (compile type-env env x)} xs))]}]
    [_ (raise 'WIP)]}}

{: make-c-id (-> Symbol Id)}
{define (make-c-id s) (Id (symbol->string s))} ; WIP
