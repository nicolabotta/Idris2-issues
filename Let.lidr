> module Let

> %default total
> %unbound_implicits off

> infixr 7 <++>

> M         :  Type -> Type
> fM        :  Functor M

> X         :  (t : Nat) -> Type
> Y         :  (t : Nat) -> X t -> Type
> next      :  (t : Nat) -> (x : X t) -> Y t x -> M (X (S t))

> Val       :  Type
> zero      :  Val
> (<+>)     :  Val -> Val -> Val
> (<=)      :  Val -> Val -> Type
> plusMon   :  {v1, v2, v3, v4 : Val} -> v1 <= v2 -> v3 <= v4 -> (v1 <+> v3) <= (v2 <+> v4)
> lteRefl   :  {v : Val} -> v <= v
> lteTrans  :  {v1, v2, v3 : Val} -> v1 <= v2 -> v2 <= v3 -> v1 <= v3

> reward    :  (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Val

> meas      :  M Val -> Val
> measMon   :  {A : Type} -> Functor M => (f, g : A -> Val) -> ((a : A) -> f a <= g a) ->
>              (ma : M A) -> meas (map f ma) <= meas (map g ma)

> Policy : (t : Nat) -> Type
> Policy t = (x : X t) -> Y t x

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> PolicySeq t Z
>   (::)  :  {t, n : Nat} -> Policy t -> PolicySeq (S t) n -> PolicySeq t (S n)

> (<++>) : {A : Type} -> (f, g : A -> Val) -> A -> Val
> f <++> g = \ a => f a <+> g a

> val : {t, n : Nat} -> Functor M => PolicySeq t n -> X t -> Val
> val {t}  Nil      x  =  zero
> val {t} (p :: ps) x  =  let y    :  Y t x
>                                  =  p x in
>                         let mx'  :  M (X (S t))
>                                  =  next t x y in          
>                         meas (map {f = M} (reward t x y <++> val ps) mx')

> OptPolicySeq  :  {t, n : Nat} -> Functor M => PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) -> (x : X t) -> val ps' x <= val ps x

> OptExt  :  {t, n : Nat} -> Functor M => PolicySeq (S t) n -> Policy t -> Type
> OptExt {t} ps p  =  (p' : Policy t) -> (x : X t) -> val (p' :: ps) x <= val (p :: ps) x

> Bellman  :  {t, n : Nat} -> Functor M => 
>             (ps   :  PolicySeq (S t) n) -> OptPolicySeq ps ->
>             (p    :  Policy t)          -> OptExt ps p ->
>             OptPolicySeq (p :: ps)
>
> Bellman {t} ps ops p oep (p' :: ps') x  =
>   let y'   :  Y t x
>            =  p' x in
>   let mx'  :  M (X (S t))
>            =  next t x y' in
>   let f'   :  ((x' : X (S t)) -> Val)
>            =  \ x' => reward t x y' x' <+> val ps' x' in
>   let f    :  ((x' : X (S t)) -> Val)
>            =  \ x' => reward t x y' x' <+> val ps x' in
>   let s0   :  ((x' : X (S t)) -> f' x' <= f x')
>            =  \ x' => plusMon Let.lteRefl (ops ps' x') in
>   let s1   :  (val (p' :: ps') x <= val (p' :: ps) x)
>            =  measMon f' f s0 mx' in
>   let s2   :  (val (p' :: ps) x <= val (p :: ps) x)
>            =  oep p' x in
>   lteTrans s1 s2

> {-

> ---}
