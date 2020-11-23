> module Mismatch

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
> val {t} (p :: ps) x  =  meas (map {f = M} (reward t x y <++> val ps) mx')
>   where y    :  Y t x
>         y    =  p x 
>         mx'  :  M (X (S t))
>         mx'  =  next t x y 

> OptPolicySeq  :  {t, n : Nat} -> Functor M => PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) -> (x : X t) -> val ps' x <= val ps x

> OptExt  :  {t, n : Nat} -> Functor M => PolicySeq (S t) n -> Policy t -> Type
> OptExt {t} ps p  =  (p' : Policy t) -> (x : X t) -> val (p' :: ps) x <= val (p :: ps) x

> Bellman  :  {t, n : Nat} -> Functor M => 
>             (ps   :  PolicySeq (S t) n) -> OptPolicySeq ps ->
>             (p    :  Policy t)          -> OptExt ps p ->
>             OptPolicySeq (p :: ps)
>
> Bellman {t} ps ops p oep (p' :: ps') x  =  lteTrans s1 s2 where
>   y'   :  Y t x
>   y'   =  p' x
>   mx'  :  M (X (S t))
>   mx'  =  next t x y' 
>   f'   :  ((x' : X (S t)) -> Val)
>   f'   =  \ x' => reward t x y' x' <+> val ps' x'
>   f    :  ((x' : X (S t)) -> Val)
>   f    =  \ x' => reward t x y' x' <+> val ps x'
>   s0   :  ((x' : X (S t)) -> f' x' <= f x')
>   s0   =  \ x' => plusMon Mismatch.lteRefl (ops ps' x')
>   s1   :  (val (p' :: ps') x <= val (p' :: ps) x) 
>   s1   =  measMon f' f s0 mx'
>   s2   :  (val (p' :: ps) x <= val (p :: ps) x) 
>   s2   =  oep p' x 

> nilOptPolicySeq  :  Functor M => OptPolicySeq Nil
> nilOptPolicySeq Nil x  =  Mismatch.lteRefl

> optExt      :  {t, n : Nat} -> PolicySeq (S t) n -> Policy t

> optExtSpec  :  {t, n : Nat} -> Functor M => 
>                (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)

> bi  :  (t : Nat) -> (n : Nat) -> PolicySeq t n
> bi t  Z     =  Nil
> bi t (S n)  =  optExt ps :: ps
>   where ps  :  PolicySeq (S t) n
>         ps  =  bi (S t) n

> biLemma  :  Functor M => (t : Nat) -> (n : Nat) -> OptPolicySeq (bi t n)
> biLemma t  Z     =  nilOptPolicySeq
> biLemma t (S n)  =  Bellman ps ops p oep 
>   where  ps   :  PolicySeq (S t) n
>          ps   =  bi (S t) n
>          ops  :  OptPolicySeq ps
>          ops  =  biLemma (S t) n
>          p    :  Policy t
>          p    =  optExt ps
>          oep  :  OptExt ps p
>          oep  =  optExtSpec ps

