/*
 * Copyright 2022 Stephen Tetley
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

pub class TraversableWithIndex[t : Type -> Type] with Traversable[t] {

    ///
    /// Returns the result of applying the applicative mapping function `f` to all the elements of the
    /// data structure `t`.
    ///
    pub def traverseWithIndex(f: (Int32, a) -> m[b] \ ef, t: t[a]): m[t[b]] \ ef with Applicative[m]

}

instance TraversableWithIndex[List] {
    pub def traverseWithIndex(f: (Int32, a) -> m[b] \ ef, l: List[a]): m[List[b]] \ ef with Applicative[m] =
        TraversableWithIndexHelper.traverseWithIndexList(f, l)

}

instance TraversableWithIndex[Chain] {
    pub def traverseWithIndex(f: (Int32, a) -> m[b] \ ef, l: Chain[a]): m[Chain[b]] \ ef with Applicative[m] =
        TraversableWithIndexHelper.traverseWithIndexChain(f, l)

}


namespace TraversableWithIndex {

    pub def forWithIndex(t: t[a], f: (Int32, a) -> m[b] \ ef): m[t[b]] \ ef with Applicative[m], TraversableWithIndex[t] = 
        TraversableWithIndex.traverseWithIndex(f, t)

    /// mapAccumLeftWithIndex

    pub def mapAccumLeftWithIndex(f: (Int32, acc, a) -> (acc, b) \ ef, start: acc, t: t[a]): (acc, t[b]) \ ef with TraversableWithIndex[t] =
        region r {
            let acc = ref start @ r;
            let Identity(tb) = t |> TraversableWithIndex.traverseWithIndex((ix, x) -> {
                let st = deref acc;
                let (acc1, b) = f(ix, st, x);
                acc := acc1;
                Identity(b)
            });
            (deref acc, tb)
        }

} 

namespace TraversableWithIndexHelper {
    
    use Functor.{<$>};
    use Applicative.{<*>};


    pub def traverseWithIndexList(f: (Int32, a) -> m[b] \ ef, l: List[a]): m[List[b]] \ ef with Applicative[m] =
        def loop(ix, ll, k) = match ll {
            case Nil     => k(Applicative.point(Nil))
            case x :: xs => loop(ix+1, xs, ks -> k(((z, zs) -> z :: zs) <$> f(ix, x) <*> ks))
        };
        loop(0, l, upcast(ks -> ks))

    pub def traverseWithIndexChain(f: (Int32, a) -> m[b] \ ef, c: Chain[a]): m[Chain[b]] \ ef with Applicative[m] =
        use Chain.ViewLeft.{NoneLeft, SomeLeft};
        def loop(ix, cc, k) = match cc {
            case NoneLeft        => k(Applicative.point(Chain.empty()))
            case SomeLeft(x, xs) => loop(ix+1, Chain.viewLeft(xs), ks -> k(Chain.cons <$> f(ix, x) <*> ks))
        };
        loop(0, Chain.viewLeft(c), upcast(ks -> ks))


}


