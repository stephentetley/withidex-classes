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
    pub def traverseWithIndex(f: (a, Int32) -> m[b] & ef, t: t[a]): m[t[b]] & ef with Applicative[m]

}

instance TraversableWithIndex[List] {
    pub def traverseWithIndex(f: (a, Int32) -> m[b] & ef, l: List[a]): m[List[b]] & ef with Applicative[m] =
        def loop(ix, ll, k) = match ll {
            case Nil     => k(Applicative.point(Nil))
            case x :: xs => loop(ix+1, xs, ks -> k(TraversableWithIndexHelper.consA(f(x, ix), ks)))
        };
        loop(0, l, ks -> ks as & ef)

}

namespace TraversableWithIndexHelper {
    
    pub def consA(mx: f[a], ml: f[List[a]]): f[List[a]] with Applicative[f] =
        (((x, xs) -> x :: xs) `Functor.map` mx) `Applicative.ap` ml
}


