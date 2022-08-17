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
    pub def traverseWithIndex(f: (Int32, a) -> m[b] & ef, t: t[a]): m[t[b]] & ef with Applicative[m]

}

instance TraversableWithIndex[List] {
    pub def traverseWithIndex(f: (Int32, a) -> m[b] & ef, l: List[a]): m[List[b]] & ef with Applicative[m] =
        TraversableWithIndexHelper.traverseWithIndexList(f, l)

}

instance TraversableWithIndex[Chain] {
    pub def traverseWithIndex(f: (Int32, a) -> m[b] & ef, l: Chain[a]): m[Chain[b]] & ef with Applicative[m] =
        TraversableWithIndexHelper.traverseWithIndexChain(f, l)

}


namespace TraversableWithIndex {

    pub def forWithIndex(t: t[a], f: (Int32, a) -> m[b] & ef): m[t[b]] & ef with Applicative[m], TraversableWithIndex[t] = 
        TraversableWithIndex.traverseWithIndex(f, t)

    /// mapAccumLeftWithIndex

    pub def mapAccumLeftWithIndex(f: (Int32, acc, a) -> (acc, b) & ef, start: acc, t: t[a]): (acc, t[b]) & ef with TraversableWithIndex[t] =
        runContStateLeft(TraversableWithIndex.traverseWithIndex((ix, x1) -> ContStateLeft((k, s) -> let (s1, b) = f(ix, s, x1); k(b, s1)), t), start) as & ef


    enum ContStateLeft[ka: Type, s: Type, a: Type]((a -> s -> ka & Impure) -> s -> ka & Impure)

    def applyLeft1(ma: ContStateLeft[ka, s, a], st: s, cont: a -> s -> ka & Impure): ka & Impure =
        let ContStateLeft(f) = ma;
        f(cont, st)

    def runContStateLeft(ma: ContStateLeft[(s, a), s, a], st: s): (s, a) & Impure =
        let ContStateLeft(f) = ma;
        let cont = (a, s) -> (s, a) as & Impure;
        f(cont, st)


    instance Functor[ContStateLeft[ka, s]] {
        pub def map(f: a -> b & ef, ma: ContStateLeft[ka, s, a]): ContStateLeft[ka, s, b] & ef =
            ContStateLeft((k, s) ->
                applyLeft1(ma, s, (a, s1) -> k(f(a) as & Impure, s1))
            ) as & ef
    }

    instance Applicative[ContStateLeft[ka, s]] {
        pub def point(x: a): ContStateLeft[ka, s, a] =
            ContStateLeft((k, s) -> k(x, s))

        pub def ap(mf: ContStateLeft[ka, s, a -> b & ef], ma: ContStateLeft[ka, s, a]): ContStateLeft[ka, s, b] & ef =
            ContStateLeft((k, s) ->
                applyLeft1(mf, s, (f, s1) ->
                    applyLeft1(ma, s1, (a, s2) ->
                        k(f(a) as & Impure, s2)))
            ) as & ef
    }


    /// mapAccumRightWithIndex

    pub def mapAccumRightWithIndex(f: (Int32, acc, a) -> (acc, b) & ef, start: acc, t: t[a]): (acc, t[b]) & ef with TraversableWithIndex[t] =
        runContStateRight(TraversableWithIndex.traverseWithIndex((ix, x1) -> ContStateRight((k, s) -> let (s1, b) = f(ix, s, x1); k(b, s1)), t), start) as & ef
    
    enum ContStateRight[ka: Type, s: Type, a: Type]((a -> s -> ka & Impure) -> s -> ka & Impure)

    def applyRight1(ma: ContStateRight[ka, s, a], st: s, cont: a -> s -> ka & Impure): ka & Impure =
        let ContStateRight(f) = ma;
        f(cont, st)

    def runContStateRight(ma: ContStateRight[(s, a), s, a], st: s): (s, a) & Impure =
        let ContStateRight(f) = ma;
        let cont = (a, s) -> (s, a) as & Impure;
        f(cont, st)

    instance Functor[ContStateRight[ka, s]] {
        pub def map(f: a -> b & ef, ma: ContStateRight[ka, s, a]): ContStateRight[ka, s, b] & ef =
            ContStateRight((k, s) ->
                applyRight1(ma, s, (a, s1) -> k(f(a) as & Impure, s1))
            ) as & ef
    }

    instance Applicative[ContStateRight[ka, s]] {
        pub def point(x: a): ContStateRight[ka, s, a] = ContStateRight((k, s) -> k(x, s))

        pub def ap(mf: ContStateRight[ka, s, a -> b & ef], ma: ContStateRight[ka, s, a]): ContStateRight[ka, s, b] & ef =
            ContStateRight((k, s) ->
                applyRight1(ma, s, (a, s1) ->
                    applyRight1(mf, s1, (f, s2) ->
                        k(f(a) as & Impure, s2)))
            ) as & ef
    }


} 

namespace TraversableWithIndexHelper {
    
    use Functor.{<$>};
    use Applicative.{<*>};


    pub def traverseWithIndexList(f: (Int32, a) -> m[b] & ef, l: List[a]): m[List[b]] & ef with Applicative[m] =
        def loop(ix, ll, k) = match ll {
            case Nil     => k(Applicative.point(Nil))
            case x :: xs => loop(ix+1, xs, ks -> k(((z, zs) -> z :: zs) <$> f(ix, x) <*> ks))
        };
        loop(0, l, upcast(ks -> ks))

    pub def traverseWithIndexChain(f: (Int32, a) -> m[b] & ef, c: Chain[a]): m[Chain[b]] & ef with Applicative[m] =
        use Chain.ViewLeft.{NoneLeft, SomeLeft};
        def loop(ix, cc, k) = match cc {
            case NoneLeft        => k(Applicative.point(Chain.empty()))
            case SomeLeft(x, xs) => loop(ix+1, Chain.viewLeft(xs), ks -> k(Chain.cons <$> f(ix, x) <*> ks))
        };
        loop(0, Chain.viewLeft(c), upcast(ks -> ks))


}


