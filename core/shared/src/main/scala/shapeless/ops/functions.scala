/*
 * Copyright (c) 2013-15 Miles Sabin 
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package shapeless
package ops

object function {
  /**
   * Type class supporting conversion of arbitrary functions to functions of a single `HList`
   * argument. 
   * 
   * @author Miles Sabin
   */
  trait FnToProduct[-F] extends DepFn1[F] {
    type Out
    def apply(f: F): Out
  }

  object FnToProduct extends FnToProductInstances {
    type Aux[F, P] = FnToProduct[F] :=> P
    def apply[F <: AnyRef](implicit to: FnToProduct[F]): to.type = to

    private[shapeless] def instance[F, P](toProduct: F => P): FnToProduct[F] :=> P =
      new FnToProduct[F] {
        type Out = P
        def apply(f: F) = toProduct(f)
      }
  }

  /**
   * Type class supporting conversion of functions of a single `HList` argument to ordinary functions. 
   * 
   * @author Miles Sabin
   */
  trait FnFromProduct[F] extends DepFn1[F]
    
  object FnFromProduct extends FnFromProductInstances {
    type Aux[F, O] = FnFromProduct[F] :=> O
    def apply[F](implicit from: FnFromProduct[F]): from.type = from

    private[shapeless] def instance[P, F](fromProduct: P => F): FnFromProduct[P] :=> F =
      new FnFromProduct[P] {
        type Out = F
        def apply(f: P) = fromProduct(f)
      }
  }
}
