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
{define (IdU? x) (or (Id? x) (IdC? x))}

{define-data Line
  (Return [Value : Value])
  (Line2 [x : Line] [y : Line])
  (DefVar [Id : Id] [Type : Type] [Value : Value])
  (DefVarGlobal [IdU : IdU] [Type : Type] [Value : Value])
  (Set! [Left : Left] [Value : Value])
  (DefFuncGlobal [IdU : IdU] [Func : Func])
  (DefUnion [IdU : IdU] [List : (Listof (Pairof Type IdU))])
  (DefStruct [IdU : IdU] [List : (Listof (Pairof Type IdU))])}
{struct Func ([args : (Listof (Pairof Type Id))] [result : Type] [Line : Line])}

{define-data Type
  (TypeArrow [args : (Listof Type)] [result : Type])
  (TypeIdC [IdC : IdC])
  (TypeStruct [IdU : IdU])
  (TypeUnion [IdU : IdU])
  (TypeRef [Type : Type])
  (TypeAny)
  (TypeVoid)
  (TypeNat8)
  (TypeNat16)
  (TypeNat32)
  (TypeNat64)
  (TypeInt8)
  (TypeInt16)
  (TypeInt32)
  (TypeInt64)
  (TypeFloat)
  (TypeDouble)
  }

{define-type Value (U Void Left Apply (Pairof Value Line))}
{define-type Left (U IdU Dot (Pairof Left Line))}
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
{define LFC-ID (make-parameter (symbol->string (gensym '||)))}
{define-syntax-rule {with-new-LFC-ID  . x}
  {parameterize ([LFC-ID (symbol->string (gensym '||))]) . x}}
{define (Id-String x)
  (string-append
   "LFC"(LFC-ID)
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

{: size (Immutable-HashTable Symbol String)}
{define size
  (make-immutable-hash
   (map {λ ([x : String]) {match (string-split x ":") [(list x y) (cons (string->symbol x) y)]}}
        (string-split (port->string (open-input-file "size.conf")) "\n")))}
{: S (-> Symbol String)}
{define (S n) (hash-ref size n)}
{: compile (-> Line String)} 
{define (compile l)
  {with-new-LFC-ID
      '||
    {define decls '("")}
    {define globals '("")}
    {define mains ""}
    {: structs (Mutable-HashTable IdU (List (Listof (U IdC TypeStruct)) (Listof String)))} ; id -> deps / global-lines
    {define structs (make-hash)}
    {: typedefs (Mutable-HashTable Type (Pairof (Listof String) String))} ; type -> decl / type
    {define typedefs (make-hash)}

    {define-syntax-rule {append! x a} {set! x (append x a)}}
    {define-syntax-rule {string-append! x a} {set! x (string-append x a)}}

  
    (raise 'WIP)

    {: Line->localdecls-locals (-> Line (List String String))}
    {define (Line->localdecls-locals l)
      {match l
        [(Return x)
         {match (Value->localdecls-locals-value x)
           [(list d l v)
            (if (false? v)
                (list d (string-append l "return;"))
                (list d (string-append l "return "v";")))]}]
        [(Line2 x y)
         {match* ((Line->localdecls-locals x) (Line->localdecls-locals x))
           [((list d0 l0) (list d1 l1)) (list (string-append d0 d1) (string-append l0 l1))]}]
        [(DefVar Id Type Value)
         {let ([s (Id-String Id)] [t (Type->type Type)])
           {match (Value->localdecls-locals-value Value)
             [(list lds ls a)
              (if (or (equal? t "void") (equal? a #f))
                  (list lds ls)
                  (list (string-append lds t" "s";")
                        (string-append ls s"="a)))]}}]
        [(DefVarGlobal IdU Type Value)
         {let ([s (IdU-String IdU)] [t (Type->type Type)])
           {match (Value->localdecls-locals-value Value)
             [(list lds ls a)
              {append! decls (list lds)}
              {string-append! mains ls}
              (if (or (equal? t "void") (equal? a #f))
                  (void)
                  {begin
                    {append! decls (list (string-append t" "s";"))}
                    {string-append! mains (string-append s"="a)}})
              (list "" "")]}}]
        [(Set! l v)
         {match* ((Value->localdecls-locals-value l) (Value->localdecls-locals-value v))
           [((list ds ls _) (list ds2 ls2 #f)) (list (string-append ds ds2) (string-append ls ls2))]
           [((list ds ls (? string? l)) (list ds2 ls2 (? string? v)))
            (list (string-append ds ds2) (string-append ls ls2 l"="v";"))]}]
        [(DefFuncGlobal id f) (raise 'WIP)]
        [(DefUnion id tis) (raise 'WIP)]
        [(DefStruct id tis) (raise 'WIP)]}}
    {: Value->localdecls-locals-value (-> Value (List String String (Maybe String)))}
    {define (Value->localdecls-locals-value v)
      {match v
        [(? void?) (list "" "" #f)]
        [(? IdU? v) (list "" "" (IdU-String v))]
        [(Dot Value IdU)
         {let ([i (IdU-String IdU)])
           {match (Value->localdecls-locals-value Value)
             [(list lds ls (? string? v)) (list lds ls (string-append "("v")."i))]}}]
        [(cons v l)
         {let ([l (Line->localdecls-locals l)] [v (Value->localdecls-locals-value v)])
           {match* (l v)
             [((list dl ll) (list dv lv v)) (list (string-append dl dv) (string-append ll lv) v)]}}]
        [_ (raise 'WIP)]
        }}
    {: Type->type (-> Type String)}
    {define (Type->type t) (cdr (%Type->type t))}
    {: %Type->type (-> Type (Pairof (Listof String) String))}
    {define (%Type->type t)
      (hash-ref!
       typedefs t
       {λ ()
         {match t
           [(TypeArrow args result)
            {let ([args (map %Type->type args)] [result (%Type->type result)] [s (gen-lfc-str)])
              (cons
               (append
                (apply append (map {ann car (-> (Pairof (Listof String) String) (Listof String))} args))
                (car result)
                (list (string-append
                       "typedef "(cdr result)" (*"s")("(string-add-between (map {ann cdr (-> (Pairof (Listof String) String) String)}
                                                                                args) ",")");")))
               s
               )}]
           [_
            (cons
             '()
             {match t
               [(TypeIdC IdC) (IdC-String IdC)]
               [(TypeStruct IdU) (string-append "struct "(IdU-String IdU))]
               [(TypeUnion IdU) (string-append "union "(IdU-String IdU))]
               [(TypeRef (TypeAny)) "void*"]
               [(TypeRef Type) (string-append "("(Type->type Type)")*")]
               [(TypeVoid) "void"]
               [(TypeNat8) (S 'n8)]
               [(TypeNat16) (S 'n16)]
               [(TypeNat32) (S 'n32)]
               [(TypeNat64) (S 'n64)]
               [(TypeInt8) (S 'i8)]
               [(TypeInt16) (S 'i16)]
               [(TypeInt32) (S 'i32)]
               [(TypeInt64) (S 'i64)]
               [(TypeFloat) "float"]
               [(TypeDouble) "double"]})]}})}
  
    {: %R (-> (Setof String) (Listof String) (Listof String))}
    {define (%R s xs)
      {cond
        [(null? xs) '()]
        [(set-member? s (car xs)) (%R s (cdr xs))]
        [else (cons (car xs) (%R (set-add s (car xs)) (cdr xs)))]}}
    {: R (-> (Listof String) (Listof String))}
    {define (R xs) (%R (set) xs)}
    (string-append
     (apply string-append (R decls))
     (apply string-append (R globals))
     "int main(){"mains"return 0;}")
    }}
