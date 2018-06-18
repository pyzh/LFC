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

{struct Var ([String : String])}

{struct Val ([ValValue : (Maybe ValValue)] [ValType : (Maybe ValType)] [ValFunc : (Maybe ValFunc)])}
{struct ValValue ([ValValueValue : ValValueValue] [Lines : Lines])}
{define-type ValValueValue (U Var)} ; WIP
{struct ValType ([ValTypeValue : ValTypeValue] [Lines : Lines])}
{define-type ValTypeValue (U Var)} ; WIP
{struct ValFunc ()} ; WIP

{struct EvaledVal ([ValValueValue : (Maybe ValValueValue)] [ValTypeValue : ValTypeValue] [ValFunc : (Maybe ValFunc)])}

{define-type Lines (Listof Line)}
{define-type Line (U Define Set!)}
{struct Define ([Var : Var] [EvaledVal : EvaledVal])}
{struct Set! ([Var : Var] [EvaledVal : EvaledVal])}
{struct GlobalTypedef ([Var : Var] [ValTypeValue : ValTypeValue])}
{struct GlobalTypedefArrow ([Var : Var] [ValTypeValues : (Listof ValTypeValue)] [ValTypeValue : ValTypeValue])}

{define-type Expr
  (U
   (Refine [s : Symbol] (not (: s '!)))
   (Pairof Expr (Listof Expr))
   (Pairof '! (Pairof Expr (Listof Expr))) ; {m x ...}
   )}

{define-type Type (U)} ; WIP
{define-type Macro (U)} ; WIP

{: compile (-> (Map Var (U (Pairof 't Type) (Pairof 'v Val) (Pairof 'm Macro))) Expr Val)}
{define (compile env x)
  {match x
    [(? symbol? x) (assert {let ([s (symbol->string x)]) (and (c-id? x) (Var x))})]
    [_ (raise 'WIP)]}}
{define (c-id? x) (raise 'WIP)}
