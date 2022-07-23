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

pub class FunctorWithIndex[m : Type -> Type] with Functor[m] {

    ///
    /// Applies the function `f` to `x` preserving its structure.
    ///
    pub def mapWithIndex(f: (a, Int32) -> b & ef, x: m[a]): m[b] & ef

}

instance FunctorWithIndex[List] {
    pub def mapWithIndex(f: (a, Int32) -> b & ef, l: List[a]): List[b] & ef = 
        def loop(ix, ll, k) = match ll {
            case Nil     => k(Nil)
            case x :: rs => {
                let a = f(x, ix);
                loop(ix+1, rs, ks -> k(a :: ks))
            }
        };
        loop(0, l, identity)

}




