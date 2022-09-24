/*
 * Copyright (c) 2011-16 Miles Sabin
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

import scala.annotation.tailrec
import scala.reflect.macros.whitebox
import scala.language.experimental.macros

object nat {
  type <[A <: Nat, B <: Nat] = LT[A, B]
  type >[A <: Nat, B <: Nat] = GT[A, B]
  type <=[A <: Nat, B <: Nat] = LTEq[A, B]
  type >=[A <: Nat, B <: Nat] = GTEq[A, B]

  /**
   * Type class witnessing that `B` is the predecessor of `A`.
   * 
   * @author Miles Sabin
   */
  trait Pred[A <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Pred {
    type Aux[A <: Nat, B <: Nat] = Pred[A] :=> B
    def apply[A <: Nat](implicit pred: Pred[A]): pred.type = pred
    implicit def pred[B <: Nat]: Pred[Succ[B]] :=> B = new Pred[Succ[B]] { type Out = B }
  }

  /**
   * Type class witnessing that `C` is the sum of `A` and `B`.
   * 
   * @author Miles Sabin
   */
  trait Sum[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Sum {
    type Aux[A <: Nat, B <: Nat, C <: Nat] = Sum[A, B] :=> C
    def apply[A <: Nat, B <: Nat](implicit sum: Sum[A, B]): sum.type = sum

    implicit def sum1[B <: Nat]: Sum[_0, B] :=> B =
      new Sum[_0, B] { type Out = B }

    implicit def sum2[A <: Nat, B <: Nat, C <: Nat](
      implicit sum: Sum[A, Succ[B]] :=> C
    ): Sum[Succ[A], B] :=> C =
      new Sum[Succ[A], B] { type Out = C }
  }

  /**
   * Type class witnessing that `C` is the difference of `A` and `B`.
   * 
   * @author Miles Sabin
   */
  trait Diff[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Diff {
    type Aux[A <: Nat, B <: Nat, C <: Nat] = Diff[A, B] :=> C
    def apply[A <: Nat, B <: Nat](implicit diff: Diff[A, B]): diff.type = diff

    implicit def diff1[A <: Nat]: Diff[A, _0] :=> A =
      new Diff[A, _0] { type Out = A }

    implicit def diff2[A <: Nat, B <: Nat, C <: Nat](
      implicit diff: Diff[A, B] :=> C
    ): Diff[Succ[A], Succ[B]] :=> C =
      new Diff[Succ[A], Succ[B]] { type Out = C }
  }

  /**
   * Type class witnessing that `C` is the product of `A` and `B`.
   * 
   * @author Miles Sabin
   */
  trait Prod[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Prod {
    type Aux[A <: Nat, B <: Nat, C <: Nat] = Prod[A, B] :=> C
    def apply[A <: Nat, B <: Nat](implicit prod: Prod[A, B]): prod.type = prod

    implicit def prod1[B <: Nat]: Prod[_0, B] :=> _0 =
      new Prod[_0, B] { type Out = _0 }

    implicit def prod2[A <: Nat, B <: Nat, C <: Nat, D <: Nat](
      implicit
      prod: Prod[A, B] :=> C,
      sum: Sum[B, C] :=> D
    ): Prod[Succ[A], B] :=> D =
      new Prod[Succ[A], B] { type Out = D }
  }

  /**
   * Type class witnessing that `Out` is the quotient of `A` and `B`.
   *
   * @author Tom Switzer
   */
  trait Div[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Div {
    type Aux[A <: Nat, B <: Nat, C <: Nat] = Div[A, B] :=> C
    def apply[A <: Nat, B <: Nat](implicit div: Div[A, B]): div.type = div

    implicit def div1[A <: Nat]: Div[_0, A] :=> _0 =
      new Div[_0, A] { type Out = _0 }

    implicit def div2[A <: Nat, B <: Nat](implicit lt: A < B): Div[A, B] :=> _0 =
      new Div[A, B] { type Out = _0 }

    implicit def div3[A <: Nat, B <: Nat, C <: Nat, D <: Nat](
      implicit
      diff: Diff[Succ[A], B] :=> C,
      div: Div[C, B] :=> D
    ): Div[Succ[A], B] :=> Succ[D] =
        new Div[Succ[A], B] { type Out = Succ[D] }
  }

  /**
   * Typeclass witnessing that `Out` is `A` mod `B`.
   *
   * @author Tom Switzer
   */
  trait Mod[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Mod {
    type Aux[A <: Nat, B <: Nat, C <: Nat] = Mod[A, B] :=> C
    def apply[A <: Nat, B <: Nat](implicit mod: Mod[A, B]): mod.type = mod

    implicit def modAux[A <: Nat, B <: Nat, C <: Nat, D <: Nat, E <: Nat](
      implicit
      div: Div[A, B] :=> C,
      prod: Prod[C, B] :=> D,
      diff: Diff[A, D] :=> E
    ): Mod[A, B] :=> E =
        new Mod[A, B] { type Out = E }
  }

  /**
   * Type class witnessing that `A` is less than `B`.
   * 
   * @author Miles Sabin
   */
  trait LT[A <: Nat, B <: Nat] extends Serializable
  object LT extends LT0 {
    def apply[A <: Nat, B <: Nat](implicit lt: A < B): lt.type = lt
    implicit def lt1[B <: Nat]: _0 < Succ[B] = new LT[_0, Succ[B]] {}
    implicit def lt2[A <: Nat, B <: Nat](implicit lt: A < B): Succ[A] < Succ[B] =
      new LT[Succ[A], Succ[B]] {}
  }

  trait LT0 {
    type <[A <: Nat, B <: Nat] = LT[A, B]
    implicit def lt3[A <: Nat]: A < Succ[A] = new LT[A, Succ[A]] {}
  }

  /**
   * Type class witnessing that `A` is less than or equal to `B`.
   * 
   * @author Miles Sabin
   */
  trait LTEq[A <: Nat, B <: Nat] extends Serializable
  object LTEq extends LTEq0 {
    def apply[A <: Nat, B <: Nat](implicit lteq: A <= B): lteq.type = lteq
    implicit def ltEq1[A <: Nat]: A <= A = new LTEq[A, A] {}
    implicit def ltEq2[A <: Nat]: A <= Succ[A] = new LTEq[A, Succ[A]] {}
  }

  trait LTEq0 {
    type <=[A <: Nat, B <: Nat] = LTEq[A, B]
    implicit def ltEq3[B <: Nat]: _0 <= B = new LTEq[_0, B] {}
    implicit def ltEq4[A <: Nat, B <: Nat](implicit lteq: A <= B): Succ[A] <= Succ[B] =
      new LTEq[Succ[A], Succ[B]] {}
  }

  /**
   * Type class witnessing that `A` is greater than `B`.
   *
   * @author ryoppy
   */
  type GT[A <: Nat, B <: Nat] = LT[B, A]
  object GT {
    def apply[A <: Nat, B <: Nat](implicit gt: GT[A, B]): gt.type = gt
    type >[A <: Nat, B <: Nat] = GT[A, B]
  }

  /**
   * Type class witnessing that `A` is greater than or equal to `B`.
   *
   * @author ryoppy
   */
  type GTEq[A <: Nat, B <: Nat] = LTEq[B, A]
  object GTEq {
    def apply[A <: Nat, B <: Nat](implicit gteq: GTEq[A, B]): gteq.type = gteq
    type >=[A <: Nat, B <: Nat] = GTEq[A, B]
  }

  /**
   * Type class witnessing that `Out` is `A` min `B`.
   *
   * @author George Leontiev
   */
  trait Min[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Min {
    type Aux[A <: Nat, B <: Nat, C <: Nat] = Min[A, B] :=> C
    def apply[A <: Nat, B <: Nat](implicit min: Min[A, B]): min.type = min

    implicit def minAux0[A <: Nat, B <: Nat, C <: Nat](implicit lteq: A <= B): Min[A, B] :=> A =
      new Min[A, B] { type Out = A }
    implicit def minAux1[A <: Nat, B <: Nat, C <: Nat](implicit lt: B < A): Min[A, B] :=> B =
      new Min[A, B] { type Out = B }
  }

  /**
   * Type class witnessing that `Out` is `A` max `B`.
   *
   * @author Alexander Konovalov
   */
  trait Max[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Max {
    type Aux[A <: Nat, B <: Nat, C <: Nat] = Max[A, B] :=> C
    def apply[A <: Nat, B <: Nat](implicit max: Max[A, B]): max.type = max

    implicit def maxAux0[A <: Nat, B <: Nat, C <: Nat](implicit lteq: A <= B): Max[A, B] :=> B =
      new Max[A, B] { type Out = B }
    implicit def maxAux1[A <: Nat, B <: Nat, C <: Nat](implicit lt: B < A): Max[A, B] :=> A =
      new Max[A, B] { type Out = A }
  }

  /**
   * Type class witnessing that `Out` is `X` raised to the power `N`.
   *
   * @author George Leontiev
   */
  trait Pow[N <: Nat, X <: Nat] extends DepFn {
    type Out <: Nat
  }

  object Pow {
    import shapeless.nat._1

    type Aux[N <: Nat, X <: Nat, Z <: Nat] = Pow[N, X] :=> Z
    def apply[A <: Nat, B <: Nat](implicit pow: Pow[A, B]): pow.type = pow

    implicit def pow1[A <: Nat]: Pow[Succ[A], _0] :=> _0 =
      new Pow[Succ[A], _0] { type Out = _0 }

    implicit def pow2[A <: Nat]: Pow[_0, Succ[A]] :=> _1 =
      new Pow[_0, Succ[A]] { type Out = _1 }

    implicit def pow3[N <: Nat, X <: Nat, Z <: Nat, Y <: Nat](
      implicit
      ev: Pow[N, X] :=> Z,
      ev2: Prod[Z, X] :=> Y
    ): Pow[Succ[N], X] :=> Y =
      new Pow[Succ[N], X] { type Out = Y }
  }

  /**
   * Type class witnessing that `Out` is range `A` to `B`, inclusive of `A` and exclusive of `B`.
   *
   * @author Andreas Koestler
   */
  trait Range[A <: Nat, B <: Nat] extends DepFn0 {
    type Out <: HList
  }

  object Range {
    import shapeless.ops.hlist._

    type Aux[A <: Nat, B <: Nat, O <: HList] = Range[A, B] :=> O
    def apply[A <: Nat, B <: Nat](implicit range: Range[A, B]): range.type = range

    implicit def range1[A <: Nat]: Range[A, A] :=> HNil =
      new Range[A, A] {
        type Out = HNil
        def apply() = HNil
      }

    implicit def range2[A <: Nat, B <: Nat, L <: HList, O <: HList](
      implicit
      w: Witness.Aux[B],
      r: Range[A, B] :=> L,
      prep: Prepend[L, B :: HNil] :=> O
    ): Range[A, Succ[B]] :=> O =
      new Range[A, Succ[B]] {
        type Out = O
        def apply() = r() :+ w.value
      }
  }

  /**
   * Type class implementing Euclidean algorithm for calculating the GCD
   *
   * @author Andreas Koestler
   */
  trait LowPriorityGCD {
    implicit def defaultCase[A <: Nat, B <: Nat, T <: Nat](
      implicit
      mod: Mod[A, B] :=> T,
      gcd: GCD[B, T]
    ): GCD[A, B] :=> gcd.Out =
      new GCD[A, B] {
        type Out = gcd.Out
      }
  }

  trait GCD[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object GCD extends LowPriorityGCD {
    type Aux[A <: Nat, B <: Nat, Out <: Nat] = GCD[A, B] :=> Out
    def apply[A <: Nat, B <: Nat](implicit gcd: GCD[A, B]): gcd.type = gcd

    implicit def terminationCase[A <: Nat]: GCD[A, _0] :=> A =
      new GCD[A, _0] {
        type Out = A
      }
  }

  /**
   * Type class for calculating the Least Common Multiple
   *
   * @author Andreas Koestler
   */
  trait LCM[A <: Nat, B <: Nat] extends DepFn {
    type Out <: Nat
  }

  object LCM {
    type Aux[A <: Nat, B <: Nat, Out <: Nat] = LCM[A, B] :=> Out
    def apply[A <: Nat, B <: Nat](implicit lcm: LCM[A, B]): lcm.type = lcm

    implicit def lcm[A <: Nat, B <: Nat, M <: Nat, N <: Nat, Res <: Nat](
      implicit
      prod: Prod[A, B] :=> M,
      gcd: GCD[A, B] :=> N,
      div: Div[M, N]
    ): LCM[A, B] :=> div.Out = new LCM[A, B] {
      type Out = div.Out
    }
  }

  /**
    * Type class witnessing that `Out` is an HList of `Nat` numbers ranging from
    * `A` to `B`.
    *
    * This differs from the `Range` type class in that it accepts another
    * type class, `Bound`, at both the start and end of the range (instead of
    * bare `Nat` types). This allows the flexibility to specify inclusive or
    * exclusive range boundaries for either end of the range.
    *
    * Reversed ranges are also possible (i.e. starting the range with a larger
    * number than it ends with), and results in an HList that counts from the
    * beginning of the range _down to_ the end of the range.
    *
    * @author Jeff Wilde
    */
  trait BoundedRange[A <: BoundedRange.Bound, B <: BoundedRange.Bound] extends DepFn0 {
    type Out <: HList
  }

  object BoundedRange {
    def apply[A <: BoundedRange.Bound, B <: BoundedRange.Bound](implicit range: BoundedRange[A,B]): range.type  = range

    trait Bound extends DepFn0 {
      type Out <: Nat
    }

    /**
      * Type class witnessing that the `Nat` `A` is the inclusive bound of
      * a range, i.e. the beginning or end of a range that includes `A`.
      *
      * @author Jeff Wilde
      */
    trait Inclusive[A] extends Bound

    trait SoftInclusive[A] extends Bound

    /**
      * Type class witnessing that the `Nat` `A` is the exclusive bound of
      * a range, i.e. the beginning or end of a range that does not include `A`.
      *
      * @author Jeff Wilde
      */
    trait Exclusive[A] extends Bound


    import shapeless.ops.hlist._

    type AuxF[A <: BoundedRange.Bound, B <: BoundedRange.Bound, Out <: HList] =
      BoundedRange[A, B] :=> Out

    //
    // nil ranges (both nil starting and recursive terminators)

    implicit def nilClosed[A <: Nat](
      implicit w: Witness.Aux[A]
    ): BoundedRange[Inclusive[A], Inclusive[A]] :=> (A :: HNil) =
      new BoundedRange[Inclusive[A], Inclusive[A]] {
        type Out = A :: HNil
        def apply() = w.value :: HNil
      }

    implicit def nilOpen[A <: Nat](
      implicit w: Witness.Aux[A]
    ): BoundedRange[Exclusive[A], Exclusive[A]] :=> HNil =
      new BoundedRange[Exclusive[A], Exclusive[A]] {
        type Out = HNil
        def apply() = HNil
      }

    implicit def nilLeftOpenRightClosed[A <: Nat](
      implicit w: Witness.Aux[A]
    ): BoundedRange[Exclusive[A], Inclusive[A]] :=> (A :: HNil) =
      new BoundedRange[Exclusive[A], Inclusive[A]] {
        type Out = A :: HNil
        def apply() = w.value :: HNil
      }

    implicit def nilLeftClosedRightOpen[A <: Nat](
      implicit w: Witness.Aux[A]
    ): BoundedRange[Inclusive[A], Exclusive[A]] :=> (A :: HNil) =
      new BoundedRange[Inclusive[A], Exclusive[A]] {
        type Out = A :: HNil
        def apply() = w.value :: HNil
      }

    //
    // nil ranges (recursive terminators only)

    implicit def nilLeftOpenRightSoft[A <: Nat]: BoundedRange[Exclusive[A], SoftInclusive[A]] :=> HNil =
      new BoundedRange[Exclusive[A], SoftInclusive[A]] {
        type Out = HNil
        def apply() = HNil
      }

    implicit def nilLeftClosedRightSoft[A <: Nat](
      implicit w: Witness.Aux[A]
    ): BoundedRange[Inclusive[A], SoftInclusive[A]] :=> (A :: HNil) =
      new BoundedRange[Inclusive[A], SoftInclusive[A]] {
        type Out = A :: HNil
        def apply() = w.value :: HNil
      }

    //
    // intermediate recursive ranges

    implicit def leftOpenRightSoft[A <: Nat, B <: Nat, Sub <: HList](
      implicit
      w: Witness.Aux[Succ[B]],
      subRange: BoundedRange[Exclusive[A], SoftInclusive[B]] :=> Sub
    ): BoundedRange[Exclusive[A], SoftInclusive[Succ[B]]] :=> (Succ[B] :: Sub) =
      new BoundedRange[Exclusive[A], SoftInclusive[Succ[B]]] {
        type Out = Succ[B] :: Sub
        def apply() = w.value :: subRange()
      }

    implicit def leftClosedRightSoft[A <: Nat, B <: Nat, Sub <: HList](
      implicit
      w: Witness.Aux[Succ[B]],
      subRange: BoundedRange[Inclusive[A], SoftInclusive[B]] :=> Sub
    ): BoundedRange[Inclusive[A], SoftInclusive[Succ[B]]] :=> (Succ[B] :: Sub) =
      new BoundedRange[Inclusive[A], SoftInclusive[Succ[B]]] {
        type Out =  Succ[B] :: Sub
        def apply() = w.value :: subRange()
      }

    //
    // public starting ranges

    implicit def closed[A <: Nat, B <: Nat, Sub <: HList, Rev <: HList](
      implicit
      w: Witness.Aux[Succ[B]],
      subRange: BoundedRange[Inclusive[A], SoftInclusive[B]] :=> Sub,
      reverse: ReversePrepend[Sub, Succ[B] :: HNil] :=> Rev
    ): BoundedRange[Inclusive[A], Inclusive[Succ[B]]] :=> Rev =
      new BoundedRange[Inclusive[A], Inclusive[Succ[B]]] {
        type Out = Rev
        def apply() = reverse(subRange(), w.value :: HNil)
      }

    implicit def open[A <: Nat, B <: Nat, Sub <: HList, Rev <: HList](
      implicit
      subRange: BoundedRange[Exclusive[A], SoftInclusive[B]] :=> Sub,
      reverse: Reverse[Sub] :=> Rev
    ): BoundedRange[Exclusive[A], Exclusive[Succ[B]]] :=> Rev =
      new BoundedRange[Exclusive[A], Exclusive[Succ[B]]] {
        type Out = Rev
        def apply() = reverse(subRange())
      }

    implicit def leftOpenRightClosed[A <: Nat, B <: Nat, Sub <: HList, Rev <: HList](
      implicit
      w: Witness.Aux[Succ[B]],
      subRange: BoundedRange[Exclusive[A], SoftInclusive[B]] :=> Sub,
      reverse: ReversePrepend[Sub, Succ[B] :: HNil] :=> Rev
    ): BoundedRange[Exclusive[A], Inclusive[Succ[B]]] :=> Rev =
      new BoundedRange[Exclusive[A], Inclusive[Succ[B]]] {
        type Out = Rev
        def apply() = reverse(subRange(), w.value :: HNil)
      }

    implicit def leftClosedRightOpen[A <: Nat, B <: Nat, Sub <: HList, Rev <: HList](
      implicit
      subRange: BoundedRange[Inclusive[A], SoftInclusive[B]] :=> Sub,
      reverse: Reverse[Sub] :=> Rev
    ): BoundedRange[Inclusive[A], Exclusive[Succ[B]]] :=> Rev =
      new BoundedRange[Inclusive[A], Exclusive[Succ[B]]] {
        type Out =  Rev
        def apply() = reverse(subRange())
      }

    //
    // reversed starting ranges

    implicit def openReverse[A <: Nat, B <: Nat, Sub <: HList](
      implicit subRange: BoundedRange[Exclusive[B], SoftInclusive[A]] :=> Sub
    ): BoundedRange[Exclusive[Succ[A]], Exclusive[B]] :=> Sub =
      new BoundedRange[Exclusive[Succ[A]], Exclusive[B]] {
        type Out = Sub
        def apply() = subRange()
      }

    implicit def leftClosedRightOpenReverse[A <: Nat, B <: Nat, Sub <: HList](
      implicit
      wA: Witness.Aux[Succ[A]],
      subRange: BoundedRange[Exclusive[B], SoftInclusive[A]] :=> Sub
    ): BoundedRange[Inclusive[Succ[A]], Exclusive[B]] :=> (Succ[A] :: Sub) =
      new BoundedRange[Inclusive[Succ[A]], Exclusive[B]] {
        type Out =  Succ[A] :: Sub
        def apply() = wA.value :: subRange()
      }

    implicit def leftOpenRightClosedReverse[A <: Nat, B <: Nat, Sub <: HList](
      implicit subRange: BoundedRange[Inclusive[B], SoftInclusive[A]] :=> Sub
    ): BoundedRange[Exclusive[Succ[A]], Inclusive[B]] :=> Sub =
      new BoundedRange[Exclusive[Succ[A]], Inclusive[B]] {
        type Out =  Sub
        def apply() = subRange()
      }

    implicit def closedReverse[A <: Nat, B <: Nat, Sub <: HList](
      implicit
      wA: Witness.Aux[Succ[A]],
      subRange: BoundedRange[Inclusive[B], SoftInclusive[A]] :=> Sub
    ): BoundedRange[Inclusive[Succ[A]], Inclusive[B]] :=> (Succ[A] :: Sub) =
      new BoundedRange[Inclusive[Succ[A]], Inclusive[B]] {
        type Out =  Succ[A] :: Sub
        def apply() = wA.value :: subRange()
      }

    object Bound {

      implicit def inclusive[A <: Nat](implicit w: Witness.Aux[A]): Inclusive[A] =
        new Inclusive[A] {
          type Out = A
          def apply() = w.value
        }

      implicit def exclusive[A <: Nat](implicit w: Witness.Aux[A]): Exclusive[A] =
        new Exclusive[A] {
          type Out = A
          def apply() = w.value
        }
    }
  }

  /**
   * Type class supporting conversion of type-level Nats to value level Ints.
   * 
   * @author Miles Sabin
   */
  sealed abstract class ToInt[N <: Nat] extends Serializable {
    def apply(): Int
  }

  object ToInt {
    def apply[N <: Nat](implicit toInt: ToInt[N]): ToInt[N] = toInt

    final class Inst[N <: Nat](i: Int) extends ToInt[N] {
      def apply(): Int = i
    }

    implicit val toInt0: ToInt[_0] = new Inst[_0](0)
    implicit def toIntSuccM[N <: Nat]: ToInt[N] = macro ToIntMacros.applyImpl[N]
  }

  class ToIntMacros(val c: whitebox.Context) extends CaseClassMacros {
    import c.universe._

    val _0Tpe: Type = typeOf[_0]
    val succTpe: Type = typeOf[Succ[_]].typeConstructor
    val succSym: Symbol = succTpe.typeSymbol
    val succPre: Type = prefix(succTpe)

    def applyImpl[N <: Nat](implicit nTag: WeakTypeTag[N]): Tree = {
      val tpe = nTag.tpe.dealias

      @tailrec
      def count(u: Type, acc: Int): Int =
        if (u <:< _0Tpe) acc
        else u.baseType(succSym) match {
          case TypeRef(pre, _, List(n)) if pre =:= succPre => count(n, acc + 1)
          case _ => abort(s"$tpe is not a Nat type")
        }

      q"new ${weakTypeOf[ToInt.Inst[N]]}(${count(tpe, 0)})"
    }
  }
}
