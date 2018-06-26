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
{require (only-in typed/racket [map %map])}
{: map {All (a b) (-> (-> a b) (Listof a) (Listof b))}}
{define (map f xs)
  (%map f xs)}
{define-syntax-rule {record x ...} {struct x ... #:transparent}}
{define-syntax define-data
  {syntax-rules ()
    [(_ (t c ...) (ons f ...) ...)
     {begin
       {record (c ...) ons (f ...)} ...
       {define-type (t c ...) (U (ons c ...) ...)}}]
    [(_ t (ons f ...) ...)
     {begin
       {record ons (f ...)} ...
       {define-type t (U ons ...)}}]}}
{define-type (Maybe a) (U a False)}
{define-type (Map k v) (Immutable-HashTable k v)}
{: string-add-between (-> (Listof String) String String)}
{define (string-add-between xs a) (apply string-append (add-between xs a))}

{record Id ([addr : (Listof String)] [Symbol : Symbol])}
{record IdC ([String : String])}
{define-type IdU (U Id IdC)}
{define (IdU? x) (or (Id? x) (IdC? x))}
{define-data Line
  (LineNothing)
  (Apply [f : Value] [Values : (Listof Value)])
  (Return [Value : Value])
  (If [Value : Value] [t : Line] [f : Line])
  (While [Value : Value] [Line : Line])
  (Line2 [x : Line] [y : Line])
  (DefVar [Id : Id] [Type : Type] [Value : Value])
  (DefVarGlobal [IdU : IdU] [Type : Type] [Value : Value])
  (Set! [Left : Left] [Value : Value])
  (DefEnum [IdU : IdU] [List : (Listof (Pairof Integer IdU))])
  (DefFunc [IdU : IdU] [Func : Func])
  (DefUnion [IdU : IdU] [List : (Listof (Pairof Type IdU))])
  (DefStruct [IdU : IdU] [List : (Listof (Pairof Type IdU))])}
{struct Func ([args : (Listof (Pairof Type Id))] [result : Type] [Line : Line])}
{define-type TypePrim (U TypeAny TypeVoid TypeNat8 TypeNat16 TypeNat32 TypeNat64
                         TypeInt8 TypeInt16 TypeInt32 TypeInt64
                         TypeFloat TypeDouble)}
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
{record Dot ([Value : Value] [IdU : IdU])}

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
{define (compile _L_)
  {with-new-LFC-ID
      '||
    {define heads '("")}
    {define decls '("")}
    {define globals '("")}
    {define mains ""}
    {define-type SU (Pairof (U 'struct 'union) IdU)}
    {: SUs (Mutable-HashTable SU (Pairof (Listof SU) String))}
    ; id -> deps / global-line
    {define SUs (make-hash)}
    {: typedefs (Mutable-HashTable Type (Pairof (Listof String) String))} ; type -> decl / type
    {define typedefs (make-hash)}

    {define-syntax-rule {append! x a} {set! x (append x a)}}
    {define-syntax-rule {add-tail! x a} {append! x (list a)}}
    {define-syntax-rule {string-append! x a} {set! x (string-append x a)}}

    {: Line->localdecls-locals (-> Line (List String String))}
    {define (Line->localdecls-locals l)
      {match l
        [(LineNothing) (list "" "")]
        [(? Apply? v) {match (Value->localdecls-locals-value v) [(list d l (? string? v)) (list d (string-append l v";"))]}]
        [(Return x)
         {match (Value->localdecls-locals-value x)
           [(list d l v)
            (if (false? v)
                (list d (string-append l "return;"))
                (list d (string-append l "return "v";")))]}]
        [(If v t f)
         {match* ((Value->localdecls-locals-value v) (Line->localdecls-locals t) (Line->localdecls-locals f))
           [((list dv lv (? string? v)) (list dt lt) (list df lf))
            (list "" (string-append "if(({"dv lv v";})){"dt lt"}else{"df lf"}"))]}]
        [(While v l)
         {match* ((Value->localdecls-locals-value v) (Line->localdecls-locals l))
           [((list dv lv (? string? v)) (list d l))
            (list "" (string-append "while(({"dv lv v"})){"d l"}"))]}]
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
              {add-tail! decls lds}
              {string-append! mains ls}
              (if (or (equal? t "void") (equal? a #f))
                  (void)
                  {begin
                    {add-tail! decls (string-append t" "s";")}
                    {string-append! mains (string-append s"="a)}})
              (list "" "")]}}]
        [(DefEnum n xs)
         {define s (IdU-String n)}
         {add-tail!
          heads
          (string-append
           "typedef enum "s"{"(string-add-between (map {λ ([x : (Pairof Integer IdU)])
                                                         (string-append (IdU-String (cdr x))"="(number->string (car x)))} xs) ",")
           "}"s";")}
         (list "" "")]
        [(Set! l v)
         {match* ((Value->localdecls-locals-value l) (Value->localdecls-locals-value v))
           [((list ds ls _) (list ds2 ls2 #f)) (list (string-append ds ds2) (string-append ls ls2))]
           [((list ds ls (? string? l)) (list ds2 ls2 (? string? v)))
            (list (string-append ds ds2) (string-append ls ls2 l"="v";"))]}]
        [(DefFunc id f);([args : (Listof (Pairof Type Id))] [result : Type] [Line : Line])
         {match f
           [(Func args result line)
            {match (Line->localdecls-locals line)
              [(list ds ls)
               {let ([h
                      (string-append
                       (Type->type result)" "(IdU-String id)
                       "("(string-add-between
                           (map {λ ([x : (Pairof Type Id)]) (string-append (Type->type (car x))" "(Id-String (cdr x)))} args) ",")")")])
                 {add-tail! globals (string-append h"{"ds ls"}")}
                 {add-tail! decls (string-append h";")}}]}]}
         (list "" "")]
        [(DefUnion id tis) (DUS 'union id tis) (list "" "")]
        [(DefStruct id tis) (DUS 'struct id tis) (list "" "")]}}
    {: DUS (-> (U 'struct 'union) IdU (Listof (Pairof Type IdU)) Void)}
    {define (DUS t idu tis)
      {let ([is (IdU-String idu)] [k (cons t idu)])
        (assert (not (hash-has-key? SUs k)))
        {hash-set!
         SUs k
         (cons
          (apply append (map {λ ([x : (Pairof Type IdU)]) (DUS%Type->D (car x))} tis))
          (string-append
           "typedef "(symbol->string t)" "is"{"
           (apply string-append
                  (map {λ ([x : (Pairof Type IdU)])
                         (string-append (Type->type (car x))" "(IdU-String (cdr x))";")} tis))
           "}"is";"))}}}
    {: DUS%Type->D (-> Type (Listof SU))}
    {define DUS%Type->D
      {match-lambda
        [(TypeStruct IdU) (list (cons 'struct IdU))]
        [(TypeUnion IdU) (list (cons 'union IdU))]
        [_ '()]}}
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
        [(Apply f xs)
         {let ([f (Value->localdecls-locals-value f)] [xs (map Value->localdecls-locals-value xs)])
           (list (string-append (first f) (apply string-append (map {ann first (-> (List String String (Maybe String)) String)} xs)))
                 (string-append (second f) (apply string-append (map {ann second (-> (List String String (Maybe String)) String)} xs)))
                 (string-append "("{cast (third f) String}")("
                                (string-add-between {cast (map {ann third (-> (List String String (Maybe String)) (Maybe String))} xs) (Listof String)}
                                                    ",")")"))}]}}
    {: Type->type (-> Type String)}
    {define (Type->type t) (cdr (%Type->type t))}
    {: %Type->type (-> Type (Pairof (Listof String) String))}
    {define (%Type->type t)
      (hash-ref!
       typedefs t
       {λ ()
         {match t
           [(TypeStruct IdU)
            {let ([s (string-append "struct "(IdU-String IdU))])
              (cons (list (string-append s";")) s)}]
           [(TypeUnion IdU)
            {let ([s (string-append "union "(IdU-String IdU))])
              (cons (list (string-append s";")) s)}]
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

    {match-define (list D L) (Line->localdecls-locals _L_)}
    {add-tail! decls D}
    {string-append! mains L}

    {set!
     decls
     (append
      (apply
       append
       (map {ann cadr (-> (Pairof Type (Pairof (Listof String) String)) (Listof String))} (hash->list typedefs)))
      decls)}


    {: SU->G (-> SU (Listof String))}
    {define (SU->G k)
      (if (hash-has-key? SUs k)
          {match (hash-ref SUs k)
            [(list deps ss) (append (apply append (map SU->G deps)) (list ss))]}
          '())}
    {set! globals (append (apply append (map SU->G (hash-keys SUs))) globals)}
    
    {: %R (-> (Setof String) (Listof String) (Listof String))}
    {define (%R s xs)
      {cond
        [(null? xs) '()]
        [(set-member? s (car xs)) (%R s (cdr xs))]
        [else (cons (car xs) (%R (set-add s (car xs)) (cdr xs)))]}}
    {: R (-> (Listof String) (Listof String))}
    {define (R xs) (%R (set) xs)}
    (string-append
     (apply string-append (R (append heads decls globals)))
     "int main(){"mains"return 0;}")
    }}


{define-type CExp
  (U
   String
   {Refine [x : Symbol] (not (: x '!))}
   (Pairof CExp (Listof CExp))
   (Pairof '! (Pairof CExp (Listof CExp)))
   )}
;--
