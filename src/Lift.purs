module Data.DeepOver(class DeepOver, over, under) where

import Data.Bifunctor  (class Bifunctor, bimap )
import Data.Function   (identity               )
import Data.Functor    (class Functor, (<$>)   )
import Data.Profunctor (class Profunctor, dimap)
import Data.Symbol     (class IsSymbol         )
import Prim.Row        (class Cons, class Lacks)
import Record          (delete, get, insert    )
import Type.Proxy      (Proxy(..)              )

class DeepOver x n xf nf | n x xf -> nf, nf xf x -> n where
    over   :: (x -> n) -> (n -> x) -> xf  -> nf
    under  :: (x -> n) -> (n -> x) -> nf  -> xf

instance DeepOver x n x n where
    over   wrap _      x = wrap   x 
    under  _    unwrap n = unwrap n
else
instance (DeepOver x n a na, DeepOver x n b nb, Profunctor f) => DeepOver x n (f a b) (f na nb) where
    over  wrap unwrap xf  = dimap (under  wrap unwrap) (over   wrap unwrap) xf
    under wrap unwrap nf  = dimap (over   wrap unwrap) (under   wrap unwrap) nf
else
instance (Bifunctor f, DeepOver x n a na, DeepOver x n b nb) => DeepOver x n (f a b) (f na nb) where
    over  wrap unwrap xf = bimap (over   wrap unwrap) (over   wrap unwrap) xf
    under wrap unwrap nf = bimap (under  wrap unwrap) (under  wrap unwrap) nf
else
instance (DeepOver x n xf nf, Functor f) => DeepOver x n (f xf) (f nf) where
    over  wrap unwrap xf = over   wrap unwrap <$> xf
    under wrap unwrap nf = under  wrap unwrap <$> nf
else
instance (IsSymbol l, Lacks l r, Lacks l nr, Cons l a r s, Cons l na nr ns, DeepOver x n a na, DeepOver x n (Record r) (Record nr)) => DeepOver x n (Record s) (Record ns) where
    over  wrap unwrap s = ns
        where
            ns = insert (Proxy :: Proxy l) na nr
            nr = over   wrap unwrap r
            r  = delete (Proxy :: Proxy l)  s
            na = over   wrap unwrap a
            a  = get    (Proxy :: Proxy l) s
    under wrap unwrap ns = s
        where
            s  = insert (Proxy :: Proxy l) a r
            r  = under  wrap unwrap nr
            nr = delete (Proxy :: Proxy l)  ns
            a  = under  wrap unwrap na
            na = get    (Proxy :: Proxy l) ns
else
instance DeepOver x n a a where
    over  _ _ = identity
    under _ _ = identity