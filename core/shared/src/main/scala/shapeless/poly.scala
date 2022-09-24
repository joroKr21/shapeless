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

import language.experimental.macros

import reflect.macros.whitebox

// Typically the contents of this object will be imported via val alias `poly` in the shapeless package object.
object PolyDefns extends Cases {
  import shapeless.ops.{ hlist => hl }

  type @=>[C <: Case[_, _], R] = C {
    type Result = R
  }

  /**
   * Type-specific case of a polymorphic function.
   *
   * @author Miles Sabin
   */
  abstract class Case[P, L <: HList] extends Serializable {
    type Result
    val value: L => Result
    def apply(t: L): Result = value(t)
    def apply()(implicit ev: HNil =:= L): Result = value(HNil)
    def apply[T](t: T)(implicit ev: (T :: HNil) =:= L): Result = value(t :: HNil)
    def apply[T, U](t: T, u: U)(implicit ev: (T :: U :: HNil) =:= L): Result = value(t :: u :: HNil)
  }

  object Case extends CaseInst {
    type Aux[P, L <: HList, Result] = Case[P, L] @=> Result
    type Hom[P, T] = Case[P, T :: HNil] @=> T

    def apply[P, L <: HList, R](v: L => R): Case[P, L] @=> R =
      new Case[P, L] {
        type Result = R
        val value = v
      }

    implicit def materializeFromValue1[P, F[_], T]: Case[P, F[T] :: HNil] =
      macro PolyMacros.materializeFromValueImpl[P, F[T], T]

    implicit def materializeFromValue2[P, T]: Case[P, T :: HNil] =
      macro PolyMacros.materializeFromValueImpl[P, T, T]
  }

  type Case0[P] = Case[P, HNil]
  object Case0 {
    type Aux[P, T] = Case[P, HNil] @=> T
    def apply[P, T](v: T): Case0[P] @=> T = Case(_ => v)
  }

  /**
   * Represents the composition of two polymorphic function values.
   *
   * @author Miles Sabin
   */
  class Compose[F, G](f: F, g: G) extends Poly
  object Compose {
    implicit def composeCase[C, F <: Poly, G <: Poly, T, U, V](
      implicit
      unpack: Unpack2[C, Compose, F, G],
      cG: Case1[G, T] @=> U,
      cF: Case1[F, U] @=> V
    ): Case1[C, T] @=> V =
      Case(t => cF(cG.value(t)))
  }

  /**
   * Represents rotating a polymorphic function by N places to the left
   *
   * @author Stacy Curl
   */
  class RotateLeft[P, N](p: P) extends Poly
  object RotateLeft {
    implicit def rotateLeftCase[C, P <: Poly, N <: Nat, L <: HList, LOut, RL <: HList](
      implicit
      unpack: Unpack2[C, RotateLeft, P, N],
      rotateRight: hl.RotateRight[RL, N] :=> L,
      cP: Case[P, L] @=> LOut
    ): Case[C, RL] @=> LOut =
      Case(rl => cP(rotateRight(rl)))
  }

  /**
   * Represents rotating a polymorphic function by N places to the right
   *
   * @author Stacy Curl
   */
  class RotateRight[P, N](p: P) extends Poly
  object RotateRight {
    implicit def rotateLeftCase[C, P <: Poly, N <: Nat, L <: HList, LOut, RL <: HList](
      implicit
      unpack: Unpack2[C, RotateRight, P, N],
      rotateLeft: hl.RotateLeft[RL, N] :=> L,
      cP: Case[P, L] @=> LOut
    ): Case[C, RL] @=> LOut =
      Case(rl => cP(rotateLeft(rl)))
  }

  final case class BindFirst[F, Head](head: Head) extends Poly
  object BindFirst {
    implicit def bindFirstCase[BF, F, Head, Tail <: HList, R](
        implicit
        unpack2: BF <:< BindFirst[F, Head],
        witnessBF: Witness.Aux[BF],
        finalCall: Case[F, Head :: Tail] @=> R
    ): Case[BF, Tail] @=> R = Case { tail =>
      finalCall.value(witnessBF.value.head :: tail)
    }
  }

  final case class Curried[F, ParameterAccumulator <: HList](parameters: ParameterAccumulator) extends Poly1

  private[PolyDefns] sealed trait LowPriorityCurried {
    implicit def partialApplied[
      Self,
      F,
      ParameterAccumulator <: HList,
      CurrentParameter,
      AllParameters <: HList,
      RestParameters <: HList,
      CurrentLength <: Nat
    ](implicit
      constraint: Self <:< Curried[F, ParameterAccumulator],
      witnessSelf: Witness.Aux[Self],
      finalCall: Case[F, AllParameters],
      length: ops.hlist.Length[CurrentParameter :: ParameterAccumulator] :=> CurrentLength,
      reverseSplit: ops.hlist.ReverseSplit.Aux[AllParameters, CurrentLength, CurrentParameter :: ParameterAccumulator, RestParameters],
      hasRestParameters: RestParameters <:< (_ :: _)
    ): Case1[Self, CurrentParameter] @=> Curried[F, CurrentParameter :: ParameterAccumulator] = Case1 {
      nextParameter => Curried(nextParameter :: witnessSelf.value.parameters)
    }
  }

  object Curried extends LowPriorityCurried {
    implicit def lastParameter[Self, F, LastParameter, ParameterAccumulator <: HList, AllParameters <: HList, Result](
        implicit
        constraint: Self <:< Curried[F, ParameterAccumulator],
        witnessSelf: Witness.Aux[Self],
        reverse: ops.hlist.Reverse[LastParameter :: ParameterAccumulator] :=> AllParameters,
        finalCall: Case[F, AllParameters] @=> Result
    ): Case1[Self, LastParameter] @=> Result = Case1 {
      lastParameter => finalCall(reverse(lastParameter :: witnessSelf.value.parameters))
    }
  }

  /**
   * Base class for lifting a `Function1` to a `Poly1`
   */
  class ->[T, R](f: T => R) extends Poly1 {
    implicit def subT[U <: T]: Case[U] @=> R = at[U](f)
  }

  trait LowPriorityLiftFunction1 extends Poly1 {
    implicit def default[T]: Case[T] @=> HNil = at[T](_ => HNil : HNil)
  }

  /**
   * Base class for lifting a `Function1` to a `Poly1` over the universal domain, yielding an `HList` with the result as
   * its only element if the argument is in the original functions domain, `HNil` otherwise.
   */
  class >->[T, R](f: T => R) extends LowPriorityLiftFunction1 {
    implicit def subT[U <: T]: Case[U] @=> (R :: HNil) = at[U](f(_) :: HNil)
  }

  trait LowPriorityLiftU extends Poly {
    implicit def default[L <: HList] = new ProductCase[L] {
      type Result = HNil
      val value = _ => HNil
    }
  }

  /**
   * Base class for lifting a `Poly` to a `Poly` over the universal domain, yielding an `HList` with the result as it's
   * only element if the argument is in the original functions domain, `HNil` otherwise.
   */
  class LiftU[P <: Poly](p: P) extends LowPriorityLiftU {
    implicit def defined[L <: HList](implicit caseT: Case[P, L]) = new ProductCase[L] {
      type Result = caseT.Result :: HNil
      val value = caseT(_) :: HNil
    }
  }

  /**
   * Base trait for natural transformations.
   *
   * @author Miles Sabin
   */
  trait ~>[F[_], G[_]] extends Poly1 {
    def apply[T](f: F[T]): G[T]
    implicit def caseUniv[T]: Case[F[T]] @=> G[T] = at[F[T]](apply(_))
  }

  object ~> {
    implicit def inst1[F[_], G[_], T](f: F ~> G): F[T] => G[T] = f(_)
    implicit def inst2[G[_], T](f: Id ~> G): T => G[T] = f(_)
    implicit def inst3[F[_], T](f: F ~> Id): F[T] => T = f(_)
    implicit def inst4[T](f: Id ~> Id): T => T = f[T](_)
  }

  /** Natural transformation with a constant type constructor on the right hand side. */
  type ~>>[F[_], R] = ~>[F, Const[R]#λ]

  /** Polymorphic identity function. */
  object identity extends (Id ~> Id) {
    def apply[T](t: T): T = t
  }
}

/**
 * Base trait for polymorphic values.
 *
 * @author Miles Sabin
 */
trait Poly extends PolyApply with Serializable {
  import poly._
  type λ = this.type

  def compose(f: Poly) = new Compose[this.type, f.type](this, f)
  def andThen(f: Poly) = new Compose[f.type, this.type](f, this)
  def rotateLeft[N <: Nat] = new RotateLeft[this.type, N](this)
  def rotateRight[N <: Nat] = new RotateRight[this.type, N](this)

  /** The type of the case representing this polymorphic function at argument types `L`. */
  type ProductCase[L <: HList] = Case[this.type, L]
  object ProductCase extends Serializable {
    /** The type of a case of this polymorphic function of the form `L => R` */
    type Aux[L <: HList, Result] = ProductCase[L] @=> Result

    /** The type of a case of this polymorphic function of the form `T => T` */
    type Hom[T] = ProductCase[T :: HNil] @=> T

    def apply[L <: HList, R](v: L => R): ProductCase[L] @=> R = new ProductCase[L] {
      type Result = R
      val value = v
    }
  }

  def use[T, L <: HList, R](t: T)(implicit cb: CaseBuilder[T, L, R]): ProductCase[L] @=> R = cb(t)

  trait CaseBuilder[T, L <: HList, R] extends Serializable {
    def apply(t: T): ProductCase[L] @=> R
  }

  trait LowPriorityCaseBuilder {
    implicit def valueCaseBuilder[T]: CaseBuilder[T, HNil, T] =
      t => ProductCase(_ => t)
  }

  object CaseBuilder extends LowPriorityCaseBuilder {
    import ops.function.FnToProduct

    implicit def fnCaseBuilder[F, H, T <: HList, Result](
      implicit fntp: FnToProduct[F] :=> ((H :: T) => Result)
    ): CaseBuilder[F, H :: T, Result] =
      f => ProductCase(fntp(f)(_))
  }

  def caseAt[L <: HList](implicit c: ProductCase[L]): c.type = c
  def apply[R](implicit c: ProductCase[HNil] @=> R): R = c()
}

/**
 * Provides implicit conversions from polymorphic function values to monomorphic function values, eg. for use as
 * arguments to ordinary higher order functions.
 *
 * @author Miles Sabin
 */
object Poly extends PolyInst {
  import PolyDefns._

  implicit def inst0(p: Poly)(implicit cse: p.ProductCase[HNil]) : cse.Result = cse()
  final def bindFirst[Head](p: Poly, head: Head): BindFirst[p.type, Head] = new BindFirst[p.type, Head](head)
  final def curried(p: Poly): Curried[p.type, HNil] = new Curried[p.type, HNil](HNil)
}

/**
 * Trait simplifying the creation of polymorphic values.
 */
trait Poly0 extends Poly {
  type Case0[T] = ProductCase.Aux[HNil, T]

  def at[T](t: T): Case0[T] = new ProductCase[HNil] {
    type Result = T
    val value = (l : HNil) => t
  }
}

class PolyMacros(val c: whitebox.Context) {
  import c.universe._
  import PolyDefns.Case

  def materializeFromValueImpl[P: WeakTypeTag, FT: WeakTypeTag, T: WeakTypeTag]: Tree = {
    val pTpe = weakTypeOf[P]
    val ftTpe = weakTypeOf[FT]
    val tTpe = weakTypeOf[T]
    val recTpe = weakTypeOf[Case[P, FT :: HNil]]

    if (c.openImplicits.tail.exists(_.pt =:= recTpe))
      c.abort(c.enclosingPosition, s"Diverging implicit expansion for Case.Aux[$pTpe, $ftTpe :: HNil]")

    pTpe match {
      case SingleType(_, f) => q"$f.caseUniv[$tTpe]"
      case _ => c.abort(c.enclosingPosition, "Can only materialize cases from singleton values")
    }
  }
}
