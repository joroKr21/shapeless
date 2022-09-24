/*
 * Copyright (c) 2011-14 Miles Sabin 
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

package shapeless.examples

/**
 * Type-level encoding of GCD.
 * 
 * @author George Leontiev
 */
object GCDExamples {
  import shapeless._
  import nat._
  import ops.nat._
  import test._

  trait GCD[X <: Nat, Y <: Nat] extends DepFn {
    type Out <: Nat
  }

  object GCD {
    def gcd[N <: Nat](x: Nat, y: Nat)(implicit gcd: GCD[x.N, y.N] :=> N, wn: Witness.Aux[N]): N = wn.value

    implicit def gcd0[X <: Nat]: GCD[X, X] :=> X =
      new GCD[X, X] { type Out = X }

    implicit def gcd1[X <: Nat, Y <: Nat, Z <: Nat, O <: Nat](
      implicit
      lt: X < Y,
      diff: Diff[Y, X] :=> Z,
      gcd: GCD[X, Z] :=> O
    ): GCD[X, Y] :=> O =
      new GCD[X, Y] { type Out = O }

    implicit def gcd2[X <: Nat, Y <: Nat, O <: Nat](
      implicit
      lt: Y < X,
      gcd: GCD[Y, X] :=> O
    ): GCD[X, Y] :=> O =
      new GCD[X, Y] { type Out = O}
  }

  import GCD._

  val g1 = gcd(2, 3)
  typed[_1](g1)

  val g2 = gcd(4, 10)
  typed[_2](g2)

  val g3 = gcd(15, 6)
  typed[_3](g3)

  val g4 = gcd(8, 12)
  typed[_4](g4)
}
