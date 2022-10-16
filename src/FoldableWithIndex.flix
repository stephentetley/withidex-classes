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

class FoldableWithIndex[t : Type -> Type] with Foldable[t] {

    ///
    /// Left-associative fold of a structure.
    /// Applies `f` to a start value `s` and all elements in `t` going from left to right.
    ///
    /// override to reduce pairing!
    pub def foldLeftWithIndex(f: (Int32, b, a) -> b \ ef, s: b, t: t[a]): b \ ef = 
        Foldable.foldLeft((bix, a) -> {let (b, ix) = bix; (f(ix, b, a), ix+1)}, (s, 0), t) |> fst
    ///
    /// Right-associative fold of a structure.
    /// Applies `f` to a start value `s` and all elements in `t` going from right to left.
    ///
    pub def foldRightWithIndex(f: (Int32, a, b) -> b \ ef, s: b, t: t[a]): b \ ef =
        Foldable.foldRight((a, bix) -> {let (b, ix) = bix; (f(ix, a, b), ix+1)}, (s, 0), t) |> fst

    // ///
    // /// Right-associative fold of a structure.
    // /// Applies `f` to a start value `s` and all elements in `t` going from right to left.
    // ///
    // /// A `foldRightWithCont` allows early termination by not calling the continuation.
    // ///
    // pub def foldRightWithContIndex(f: (Int32, a, Unit -> b \ ef) -> b \ ef, s: b, t: t[a]): b \ ef = 
    //     Foldable.foldRightWithCont((a, bix) -> {let (b, ix) = bix; (f(ix, a, b), ix+1)}, (s, 0), t) |> fst


    ///
    /// Returns the result of mapping each element and combining the results.
    ///
    pub def foldMapWithIndex(f: (Int32, a) -> b \ ef, t: t[a]): b \ ef with Monoid[b] =
        FoldableWithIndex.foldLeftWithIndex((ix, acc, x) -> Monoid.combine(acc, f(ix, x)), Monoid.empty(), t)

    ///
    /// A monadic version of `foldLeft`.
    ///
    /// Applies the monadic `f` to a start value `s` and all elements in `t` going
    /// from left to right.
    ///
    pub def foldLeftMWithIndex(f: (Int32, b, a) -> m[b] \ ef, s: b, t: t[a]): m[b] \ ef with Monad[m] =
        let f1 = (ix, x, acc) -> z -> Monad.flatMap(acc, f(ix, z, x));
        s |> FoldableWithIndex.foldRightWithIndex(f1, upcast(x1 -> Applicative.point(x1)), t)


    ///
    /// A monadic version of `foldRight`.
    ///
    /// Applies the monadic `f` to a start value `s` and all elements in `t` going
    /// from right to left.
    ///
    pub def foldRightMWithIndex(f: (Int32, a, b) -> m[b] \ ef, s: b, t: t[a]): m[b] \ ef with Monad[m] =
        let f1 = (ix, k, x) -> z -> Monad.flatMap(k, f(ix, x, z));
        s |> FoldableWithIndex.foldLeftWithIndex(f1, upcast(x1 -> Applicative.point(x1)), t)

    ///
    /// A monadic version of `foreach`.
    ///
    /// Apply `f` to every value in `t`. `f` is applied for its monadic effect,
    /// the answer it produces is discarded.
    ///
    pub def foreachMWithIndex(f: (Int32, a) -> m[b] \ ef, t: t[a]): m[Unit] \ ef with Monad[m] =
        use Applicative.{point, *>};
        FoldableWithIndex.foldLeftMWithIndex((ix, acc, a) -> f(ix, a) *> point(acc), (), t)

    ///
    /// Returns the number of elements in `t` that satisfy the predicate `f`.
    ///
    pub def countWithIndex(f: (Int32, a) -> Bool \ ef, t: t[a]): Int32 \ ef =
        FoldableWithIndex.foldLeftWithIndex((acc, ix, x) -> if (f(ix, x)) acc + 1 else acc, 0, t)

    ///
    /// Returns the sum of all elements in `t` according to the function `f`.
    ///
    pub def sumWithIndex(f: (Int32, a) -> Int32 \ ef, t: t[a]): Int32 \ ef =
        FoldableWithIndex.foldLeftWithIndex((acc, ix, x) -> acc + f(ix, x), 0, t)

    ///
    /// Returns the product of all elements in `t` according to the function `f`.
    ///
    pub def productWith(f: (Int32, a) -> Int32 \ ef, t: t[a]): Int32 \ ef =
        if (Foldable.isEmpty(t))
            1
        else
            FoldableWithIndex.foldLeftWithIndex((acc, ix, x) -> acc * f(ix, x), 1, t)


    // ///
    // /// Returns `true` if and only if at least one element in `t` satisfies the predicate `f`.
    // ///
    // /// Returns `false` if `t` is empty.
    // ///
    // pub def exists(f: (Int32, a) -> Bool \ ef, t: t[a]): Bool \ ef =
    //     FoldableWithIndex.foldRightWithCont((x, k) -> f(ix, x) or k(), false, t)

}

instance FoldableWithIndex[List] {
    pub override def foldLeftWithIndex(f: (Int32, b, a) -> b \ ef, s: b, l: List[a]): b \ ef = 
        def loop(acc, ix, ll) = match ll {
            case Nil     => acc
            case x :: xs => loop(f(ix, acc, x), ix+1, xs)
        };
        loop(s, 0, l)

    pub override def foldRightWithIndex(f: (Int32, a, b) -> b \ ef, s: b, l: List[a]): b \ ef =
        def loop(ix, ll, k) = match ll {
            case Nil     => k(s)
            case x :: xs => loop(ix+1, xs, ks -> k(f(ix, x, ks)))
        };
        loop(0, l, upcast(identity)) // NB: Cast required because the identity continuation is pure,
                                  // but the intermediate continuations are effect polymorphic

    pub override def foreachMWithIndex(f: (Int32, a) -> m[b] \ ef, l: List[a]): m[Unit] \ ef with Monad[m] =
        use Applicative.{point};
        def loop(_, ix, ll) = match ll {
            case Nil     => point()
            case x :: rs => loop(Functor.ignore(f(ix, x)), ix+1, rs)
        };
        loop(point(), 0, l)

}


instance FoldableWithIndex[Nel] {
    pub override def foldLeftWithIndex(f: (Int32, b, a) -> b \ ef, s: b, l: Nel[a]): b \ ef = 
        let Nel(x, ll) = l;
        FoldableWithIndex.foldLeftWithIndex(f, s, x :: ll)

    pub override def foldRightWithIndex(f: (Int32, a, b) -> b \ ef, s: b, l: Nel[a]): b \ ef =
        let Nel(x, ll) = l;
        FoldableWithIndex.foldRightWithIndex(f, s, x :: ll) 

    pub override def foreachMWithIndex(f: (Int32, a) -> m[b] \ ef, l: Nel[a]): m[Unit] \ ef with Monad[m] =
        let Nel(x, ll) = l;
        FoldableWithIndex.foreachMWithIndex(f, x :: ll)

}

instance FoldableWithIndex[Chain] {
    pub override def foldLeftWithIndex(f: (Int32, b, a) -> b \ ef, s: b, c: Chain[a]): b \ ef = 
        use Chain.ViewLeft.{SomeLeft, NoneLeft};
        use Chain.{viewLeft};
        def loop(acc, ix, vw) = match vw {
            case NoneLeft          => acc
            case SomeLeft(x, rest) => loop(f(ix, acc, x), ix+1, viewLeft(rest))
        };
        loop(s, 0, viewLeft(c))

    // Don't use viewRight because we don't immediately know the length of the chain (finding 
    // it would need an extra traversal)
    pub override def foldRightWithIndex(f: (Int32, a, b) -> b \ ef, s: b, c: Chain[a]): b \ ef =
        use Chain.ViewLeft.{SomeLeft, NoneLeft};
        use Chain.{viewLeft};
        def loop(ix, vw, k) = match vw {
            case NoneLeft        => k(s)
            case SomeLeft(x, xs) => loop(ix+1, viewLeft(xs), ks -> k(f(ix, x, ks)))
        };
        loop(0, viewLeft(c), upcast(identity)) // NB: Cast required because the identity continuation is pure,
                                            // but the intermediate continuations are effect polymorphic


    pub override def foreachMWithIndex(f: (Int32, a) -> m[b] \ ef, c: Chain[a]): m[Unit] \ ef with Monad[m] =
        use Applicative.{point};
        use Chain.ViewLeft.{SomeLeft, NoneLeft};
        use Chain.{viewLeft};
        def loop(_, ix, vw) = match vw {
            case NoneLeft          => point()
            case SomeLeft(x, rest) => loop(Functor.ignore(f(ix, x)), ix+1, viewLeft(rest))
        };
        loop(point(), 0, viewLeft(c))

}


instance FoldableWithIndex[Nec] {
    pub override def foldLeftWithIndex(f: (Int32, b, a) -> b \ ef, s: b, l: Nec[a]): b \ ef = 
        use Nec.ViewLeft.{SomeLeft, OneLeft};
        use Nec.{viewLeft};
        def loop(acc, ix, vw) = match vw {
            case OneLeft(x)        => f(ix, acc, x)
            case SomeLeft(x, rest) => loop(f(ix, acc, x), ix+1, viewLeft(rest))
        };
        loop(s, 0, viewLeft(l))

    // Don't use viewRigt because we don't immediately know the length of the chain (finding 
    // it would need an extra traversal)
    pub override def foldRightWithIndex(f: (Int32, a, b) -> b \ ef, s: b, l: Nec[a]): b \ ef =
        use Nec.ViewLeft.{SomeLeft, OneLeft};
        use Nec.{viewLeft};
        def loop(ix, vw, k) = match vw {
            case OneLeft(x)      => f(ix, x, s)
            case SomeLeft(x, xs) => loop(ix+1, viewLeft(xs), ks -> k(f(ix, x, ks)))
        };
        loop(0, viewLeft(l), upcast(identity)) // NB: Cast required because the identity continuation is pure,
                                            // but the intermediate continuations are effect polymorphic


    pub override def foreachMWithIndex(f: (Int32, a) -> m[b] \ ef, l: Nec[a]): m[Unit] \ ef with Monad[m] =
        use Applicative.{point};
        use Nec.ViewLeft.{SomeLeft, OneLeft};
        use Nec.{viewLeft};
        def loop(_, ix, vw) = match vw {
            case OneLeft(x)        => Functor.ignore(f(ix, x))
            case SomeLeft(x, rest) => loop(Functor.ignore(f(ix, x)), ix+1, viewLeft(rest))
        };
        loop(point(), 0, viewLeft(l))

}


namespace ListHelper {
    
    pub def foldRightWithContIndex(f: (Int32, a, Unit -> b \ ef) -> b \ ef, s: b, l: List[a]): b \ ef =
        def loop(acc, ix, ll) = match ll {
            case Nil     => acc
            case x :: xs => f(ix, x, _ -> loop(acc, ix+1, xs))
        };
        loop(s, 0, l)
}
