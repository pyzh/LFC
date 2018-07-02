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
{define-type TypePrim (U TypeAny TypeVoid TypeNat8 TypeNat16 TypeNat32 TypeNat64
                         TypeInt8 TypeInt16 TypeInt32 TypeInt64
                         TypeFloat TypeDouble)}
{define-type TypeVar (U IdU String)}
{define (TypeVar? x) (or (IdU? x) (string? x))}
{define-type TypeSimple {Refine [t : Type] (not (or (: t TypeTypeVar) (: t TypeStructUnion) (: t TypeU)))}}
{define-data Type
  (TypeArrow [args : (Maybe (Listof Type))] [result : Type]) ; Maybe=>類型推導
  (TypeIdC [IdC : IdC])
  (TypeStruct [IdU : IdU])
  (TypeUnion [IdU : IdU])
  (TypeEnum [IdU : IdU])
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
  (TypeTypeVar [TypeVar : (Maybe TypeVar)]) ; 類型推導
  (TypeStructUnion) ; 類型推導
  (TypeU [Set : (Setof TypeSimple)]) ; 類型推導
  }
{define-type Value (U Void Left Apply Value+Line Ann Func ValueSimple)}
{record Value+Line ([Value : Value] [Line : Line])}
{define-type Left (U IdU Dot (Pairof Left Line))}
{record Dot ([Value : Value] [IdU : IdU])}
{record Ann ([Value : Value] [Type : Type])} ; 類型推導
{struct Func ([args : (Listof (Pairof Type Id))] [result : Type] [Value : Value])}
{define-data ValueSimple
  (ValueRational [Rational : Exact-Rational])
  (ValueInteger [Integer : Integer])
  (ValueChar [Char : Char])
  (ValueString [String : String])}
{define (ValueSimple? x) (or (ValueRational? x) (ValueInteger? x) (ValueChar? x) (ValueString? x))}

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
    {define-type StructUnion (Pairof (U 'struct 'union) IdU)}
    {: StructUnions (Mutable-HashTable StructUnion (Pairof (Listof StructUnion) String))}
    ; id -> deps / global-line
    {define StructUnions (make-hash)}
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
        [(DefFunc id f)
         {match f
           [(Func args result value)
            {match (Value->localdecls-locals-value value)
              [(list ds ls v)
               {let ([h
                      (string-append
                       (Type->type result)" "(IdU-String id)
                       "("(string-add-between
                           (map {λ ([x : (Pairof Type Id)]) (string-append (Type->type (car x))" "(Id-String (cdr x)))} args) ",")")")])
                 {add-tail! globals (string-append h"{"ds ls"return"(if (false? v) "" (string-append " "v))";}")}
                 {add-tail! decls (string-append h";")}}]}]}
         (list "" "")]
        [(DefUnion id tis) (DUS 'union id tis) (list "" "")]
        [(DefStruct id tis) (DUS 'struct id tis) (list "" "")]}}
    {: DUS (-> (U 'struct 'union) IdU (Listof (Pairof Type IdU)) Void)}
    {define (DUS t idu tis)
      {let ([is (IdU-String idu)] [k (cons t idu)])
        (assert (not (hash-has-key? StructUnions k)))
        {hash-set!
         StructUnions k
         (cons
          (apply append (map {λ ([x : (Pairof Type IdU)]) (DUS%Type->D (car x))} tis))
          (string-append
           "typedef "(symbol->string t)" "is"{"
           (apply string-append
                  (map {λ ([x : (Pairof Type IdU)])
                         (string-append (Type->type (car x))" "(IdU-String (cdr x))";")} tis))
           "}"is";"))}}}
    {: DUS%Type->D (-> Type (Listof StructUnion))}
    {define DUS%Type->D
      {match-lambda
        [(TypeStruct IdU) (list (cons 'struct IdU))]
        [(TypeUnion IdU) (list (cons 'union IdU))]
        [_ '()]}}
    {: Value->localdecls-locals-value (-> Value (List String String (Maybe String)))}
    {define (Value->localdecls-locals-value v)
      {match v
        [(? ValueSimple?) (list "" "" (ValueSimple->value v))]
        [(? void?) (list "" "" #f)]
        [(? IdU? v) (list "" "" (IdU-String v))]
        [(Dot Value IdU)
         {let ([i (IdU-String IdU)])
           {match (Value->localdecls-locals-value Value)
             [(list lds ls (? string? v)) (list lds ls (string-append "("v")."i))]}}]
        [(Value+Line v l)
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
    {: ValueSimple->value (-> ValueSimple String)}
    {define ValueSimple->value
      {match-lambda
        [(ValueRational n) (number->string n)] ; bugs
        [(ValueInteger n) (number->string n)] ; bugs
        [(ValueChar c) 
         {define p (open-output-string)}
         (write (string c) p)
         (string-append "'" (get-output-string p) "'")]
        [(ValueString s)
         {define p (open-output-string)}
         (write s p)
         (string-append "\"" (get-output-string p) "\"")]}}
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
           [(TypeEnum IdU)
            {let ([s (string-append "enum "(IdU-String IdU))])
              (cons (list (string-append s";")) s)}]
           [(TypeArrow (? list? args) result)
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


    {: StructUnion->Globals (-> StructUnion (Listof String))}
    {define (StructUnion->Globals k)
      (if (hash-has-key? StructUnions k)
          {match (hash-ref StructUnions k)
            [(list deps ss) (append (apply append (map StructUnion->Globals deps)) (list ss))]}
          '())}
    {set! globals (append (apply append (map StructUnion->Globals (hash-keys StructUnions))) globals)}
    
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
{define-type Tbinds
  (List (Mutable-HashTable TypeVar Type) ;值的類型
        (List (Mutable-HashTable (U TypeStruct TypeUnion) (Mutable-HashTable IdU Type)) ;確定的struct/union的成員的類型
              (Boxof (Listof (List TypeTypeVar IdU Type))) ;不確定的struct/union的成員的類型
              (Mutable-HashTable (U TypeStruct TypeUnion) (Listof IdU)) ;聲名
              ))}
{define TU (TypeTypeVar #f)}
{: Tbinds.unknown-StructUnion-add! (-> Tbinds TypeTypeVar IdU Type Void)}
{define (Tbinds.unknown-StructUnion-add! B t i f)
  (set-box! (second (second B)) (cons (list t i f) (unbox (second (second B)))))}
{: Tbinds.StructUnion-add! (-> Tbinds (U TypeStruct TypeUnion) IdU Type Void)}
{define (Tbinds.StructUnion-add! B t i f)
  (hash-update!
   (hash-ref! (first (second B)) t {λ () {ann (make-hash) (Mutable-HashTable IdU Type)}})
   i {λ ([x : Type]) (Tbinds.unify! B x f)} {λ () TU})}
{: Tbinds.StructUnion! (-> Tbinds (U TypeStruct TypeUnion) (Listof IdU) Void)}
{define (Tbinds.StructUnion! B i xs)
  (assert (not (hash-has-key? (third (second B)) i)))
  (hash-set! (third (second B)) i xs)}
{: Tbinds.add! (-> Tbinds TypeVar Type Void)}
{define (Tbinds.add! B i t)
  (hash-update!	(car B) i {λ ([x : Type]) (Tbinds.unify! B x t)} {λ () TU})}
{:  Tbinds.unify! (-> Tbinds Type Type Type)}
{define (Tbinds.unify! B t1 t2)
  {match t1
    [(TypeTypeVar #f) t2]
    [(TypeTypeVar (? TypeVar? i))
     (if (hash-has-key? (car B) i)
         (Tbinds.unify! B t2 (hash-ref (car B) i))
         {begin
           (Tbinds.add! B i t2)
           t2})]
    [(TypeU s1)
     {match t2
       [(TypeU s2)
        {let ([s (set-intersect s1 s2)])
          (assert (not (set-empty? s)))
          (TypeU s)}]
       [_ (assert (set-member? s1 t2)) t2]}]
    [_
     {match t2
       [(TypeU _) (Tbinds.unify! B t2 t1)]
       [(TypeTypeVar #f) t1]
       [(TypeTypeVar (? TypeVar? i))
        (if (hash-has-key? (car B) i)
            (Tbinds.unify! B t1 (hash-ref (car B) i))
            {begin
              (Tbinds.add! B i t1)
              t1})]
       [(TypeStructUnion)
        {match t1
          [(or (TypeStruct _) (TypeUnion _) (TypeStructUnion)) t1]}]
       [_
        {match t1
          [(TypeArrow args result)
           {match t2
             [(TypeArrow args2 result2)
              {cond
                [(false? args) (TypeArrow args2 (Tbinds.unify! B result result2))]
                [(false? args2) (TypeArrow args (Tbinds.unify! B result result2))]
                [else
                 (assert (= (length args) (length args2)))
                 (TypeArrow (map {λ ([x : Type] [y : Type]) (Tbinds.unify! B x y)} args args2) (Tbinds.unify! B result result2))]}]}]
          [(TypeRef a)
           {match t2
             [(TypeRef r)
              (TypeRef (Tbinds.unify! B a r))]}]
          [(TypeStructUnion)
           {match t2
             [(or (TypeStruct _) (TypeUnion _) (TypeStructUnion)) t2]}]
          [_ (assert (equal? t1 t2)) t1]}]}]}}
{: Tbinds.var! (-> Tbinds TypeTypeVar)}
{define (Tbinds.var! B) (TypeTypeVar (symbol->string (gensym)))}
{: Tbinds.Value! (-> Tbinds Value Value)}
{define (Tbinds.Value! B v) (Tbinds.Value%Ann! B v (TypeTypeVar #f))}
{: Tbinds.Value%Ann! (-> Tbinds Value Type Value)}
{define (Tbinds.Value%Ann! B v t)
  {match v
    [(? ValueSimple?) (raise 'WIP)]
    [(? IdU?) (Tbinds.add! B v t)]
    [(Apply f xs)
     {let ([ts (build-list (length xs) {λ (_) (Tbinds.var! B)})])
       {let ([xs (map {λ ([t : Type] [v : Value]) (Tbinds.Value%Ann! B v t)} ts xs)])
         (Apply (Tbinds.Value%Ann! B f (TypeArrow ts t)) xs)}}]
    [(Value+Line v l) (Value+Line (Tbinds.Value%Ann! B v t) (Tbinds.Line! B l))]
    [(Ann v t2)
     {let ([nt (Tbinds.unify! B t t2)])
       (Tbinds.Value%Ann! B v nt)}]
    [(? void?) (Tbinds.unify! B (TypeVoid) t) v]
    [(Dot v i)
     {let* ([struct-s (symbol->string (gensym))] [struct-type (TypeTypeVar struct-s)])
       {let ([v (Tbinds.Value%Ann! B v (Tbinds.unify! B (TypeStructUnion) struct-type))])
         {let ([struct-type2 (hash-ref (car B) struct-s)])
           {match struct-type2
             [(or (TypeStruct _) (TypeUnion _)) (Tbinds.StructUnion-add! B struct-type2 i t)]
             [_ (Tbinds.unknown-StructUnion-add! B struct-type i t)]}}}}]}}
{: Tbinds.Line! (-> Tbinds Line Line)}
{define (Tbinds.Line! B l)
  {match l
    [(LineNothing) l]
    [(Apply f xs) (Apply (Tbinds.Value! B f) (map {λ ([x : Value]) (Tbinds.Value! B x)} xs))]
    [(If v t f) (If (Tbinds.Value! B v) (Tbinds.Line! B t) (Tbinds.Line! B f))]
    [(While v l) (While (Tbinds.Value! B v) (Tbinds.Line! B l))]
    [(Line2 x y) (Line2 (Tbinds.Line! B x) (Tbinds.Line! B y))]
    [(DefVar i t v) (Tbinds.add! B i t) (DefVar i TU (Tbinds.Value! B v))]
    [(DefVarGlobal i t v) (Tbinds.add! B i t) (DefVarGlobal i TU (Tbinds.Value! B v))]
    [(Set! l v) (Set! {cast (Tbinds.Value! B l) Left} (Tbinds.Value! B v))]
    [(DefEnum i xs)
     {for ([x xs])
       (Tbinds.add! B (cdr x) (TypeEnum i))}
     l]
    [(DefFunc i f)
     {match f
       [(Func args result v)
        {for ([arg args])
          (Tbinds.add! B (cdr arg) (car arg))}
        (DefFunc i (Func args result (Tbinds.Value%Ann! B v result)))]}]
    [(DefUnion i xs)
     {for ([x xs])
       (Tbinds.StructUnion-add! B (TypeUnion i) (cdr x) (car x))}
     (Tbinds.StructUnion! B (TypeUnion i) (map {ann cdr (-> (Pairof Type IdU) IdU)} xs))
     l]
    [(DefStruct i xs) {for ([x xs])
                        (Tbinds.StructUnion-add! B (TypeStruct i) (cdr x) (car x))}
                      (Tbinds.StructUnion! B (TypeStruct i) (map {ann cdr (-> (Pairof Type IdU) IdU)} xs))
                      l]}}
{: type-end-line! (-> Any Line Line)};Any=>WIP
{define (type-end-line! M l) (raise 'WIP)}
