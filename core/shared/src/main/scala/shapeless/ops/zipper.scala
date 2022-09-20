/*
 * Copyright (c) 2012-15 Miles Sabin
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

import hlist.{ IsHCons, ReversePrepend, Split, SplitLeft }

object zipper {
  trait Right[Z] extends DepFn1[Z]
  object Right {
    type Aux[Z, Out] = Right[Z] :=> Out
    def apply[Z](implicit right: Right[Z]): right.type = right

    implicit def right[C, L <: HList, RH, RT <: HList, P]: Right[Zipper[C, L, RH :: RT, P]] :=> Zipper[C, RH :: L, RT, P] =
      new Right[Zipper[C, L, RH :: RT, P]] {
        type Out = Zipper[C, RH :: L, RT, P]
        def apply(z: Zipper[C, L, RH :: RT, P]) = Zipper(z.suffix.head :: z.prefix, z.suffix.tail, z.parent)
      }
  }

  trait Left[Z] extends DepFn1[Z]
  object Left {
    type Aux[Z, Out] = Left[Z] :=> Out
    def apply[Z](implicit left: Left[Z]): left.type = left

    implicit def left[C, LH, LT <: HList, R <: HList, P]: Left[Zipper[C, LH :: LT, R, P]] :=> Zipper[C, LT, LH :: R, P] =
      new Left[Zipper[C, LH :: LT, R, P]] {
        type Out = Zipper[C, LT, LH :: R, P]
        def apply(z: Zipper[C, LH :: LT, R, P]) = Zipper(z.prefix.tail, z.prefix.head :: z.suffix, z.parent)
      }
  }

  trait First[Z] extends DepFn1[Z]
  object First {
    type Aux[Z, Out] = First[Z] :=> Out
    def apply[Z](implicit first: First[Z]): first.type = first

    implicit def first[C, L <: HList, R <: HList, RP <: HList, P](
      implicit rp: ReversePrepend[L, R] :=> RP
    ): First[Zipper[C, L, R, P]] :=> Zipper[C, HNil, RP, P] =
      new First[Zipper[C, L, R, P]] {
        type Out = Zipper[C, HNil, RP, P]
        def apply(z: Zipper[C, L, R, P]) = Zipper(HNil, z.prefix reverse_::: z.suffix, z.parent)
      }
  }

  trait Last[Z] extends DepFn1[Z]
  object Last {
    type Aux[Z, Out] = Last[Z] :=> Out
    def apply[Z](implicit last: Last[Z]): last.type = last

    implicit def last[C, L <: HList, R <: HList, RP <: HList, P](
      implicit rp: ReversePrepend[R, L] :=> RP
    ): Last[Zipper[C, L, R, P]] :=> Zipper[C, RP, HNil, P] =
      new Last[Zipper[C, L, R, P]] {
        type Out = Zipper[C, RP, HNil, P]
        def apply(z: Zipper[C, L, R, P]) = Zipper(z.suffix reverse_::: z.prefix, HNil, z.parent)
      }
  }

  trait RightBy[Z, N <: Nat] extends DepFn1[Z]
  object RightBy {
    type Aux[Z, N <: Nat, Out] = RightBy[Z, N] :=> Out
    def apply[Z, N <: Nat](implicit rightBy: RightBy[Z, N]): rightBy.type = rightBy

    implicit def rightBy[C, L <: HList, R <: HList, P, N <: Nat, LP <: HList, RS <: HList](
      implicit
      split: Split.Aux[R, N, LP, RS],
      reverse: ReversePrepend[LP, L]
    ): RightBy[Zipper[C, L, R, P], N] :=> Zipper[C, reverse.Out, RS, P] =
      new RightBy[Zipper[C, L, R, P], N] {
        type Out = Zipper[C, reverse.Out, RS, P]
        def apply(z: Zipper[C, L, R, P]) = {
          val p :: s :: HNil = z.suffix.splitP[N]
          Zipper(p reverse_::: z.prefix, s, z.parent)
        }
      }
  }

  trait LeftBy[Z, N <: Nat] extends DepFn1[Z]
  object LeftBy {
    type Aux[Z, N <: Nat, Out] = LeftBy[Z, N] :=> Out
    def apply[Z, N <: Nat](implicit leftBy: LeftBy[Z, N]): leftBy.type = leftBy

    implicit def leftBy[C, L <: HList, R <: HList, P, N <: Nat, RP <: HList, LS <: HList](
      implicit
      split: Split.Aux[L, N, RP, LS],
      reverse: ReversePrepend[RP, R]
    ): LeftBy[Zipper[C, L, R, P], N] :=> Zipper[C, LS, reverse.Out, P] =
      new LeftBy[Zipper[C, L, R, P], N] {
        type Out = Zipper[C, LS, reverse.Out, P]
        def apply(z: Zipper[C, L, R, P]) = {
          val p :: s :: HNil = z.prefix.splitP[N]
          Zipper(s, p reverse_::: z.suffix, z.parent)
        }
      }
  }

  trait RightTo[Z, T] extends DepFn1[Z]
  object RightTo {
    type Aux[Z, T, Out] = RightTo[Z, T] :=> Out
    def apply[Z, T](implicit rightTo: RightTo[Z, T]): rightTo.type = rightTo

    implicit def rightTo[C, L <: HList, R <: HList, P, T, LP <: HList, RS <: HList](
      implicit
      split: SplitLeft.Aux[R, T, LP, RS],
      reverse: ReversePrepend[LP, L]
    ): RightTo[Zipper[C, L, R, P], T] :=> Zipper[C, reverse.Out, RS, P] =
      new RightTo[Zipper[C, L, R, P], T] {
        type Out = Zipper[C, reverse.Out, RS, P]
        def apply(z: Zipper[C, L, R, P]) = {
          val p :: s :: HNil = z.suffix.splitLeftP[T]
          Zipper(p reverse_::: z.prefix, s, z.parent)
        }
      }
  }

  trait LeftTo[Z, T] extends DepFn1[Z]
  object LeftTo {
    type Aux[Z, T, Out] = LeftTo[Z, T] :=> Out
    def apply[Z, T](implicit leftTo: LeftTo[Z, T]): leftTo.type = leftTo

    implicit def leftTo[C, L <: HList, R <: HList, P, T, RP <: HList, R0 <: HList](
      implicit
      split: SplitLeft.Aux[L, T, RP, R0],
      reverse: ReversePrepend[RP, R],
      cons: IsHCons[R0]
    ): LeftTo[Zipper[C, L, R, P], T] :=> Zipper[C, cons.T, cons.H :: reverse.Out, P] =
      new LeftTo[Zipper[C, L, R, P], T] {
        type Out = Zipper[C, cons.T, cons.H :: reverse.Out, P]
        def apply(z: Zipper[C, L, R, P]) = {
          val p :: s :: HNil = z.prefix.splitLeftP[T]
          Zipper(s.tail, s.head :: (p reverse_::: z.suffix), z.parent)
        }
      }
  }

  trait Up[Z] extends DepFn1[Z]
  object Up {
    type Aux[Z, Out] = Up[Z] :=> Out
    def apply[Z](implicit up: Up[Z]): up.type = up

    implicit def up[C, L <: HList, R <: HList, P](
      implicit
      rz: Reify[Zipper[C, L, R, Some[P]]] :=> C,
      pp: Put[P, C]
    ): Up[Zipper[C, L, R, Some[P]]] :=> pp.Out =
      new Up[Zipper[C, L, R, Some[P]]] {
        type Out = pp.Out
        def apply(z: Zipper[C, L, R, Some[P]]) = pp(z.parent.get, z.reify)
      }
  }

  trait Down[Z] extends DepFn1[Z]
  object Down {
    type Aux[Z, Out] = Down[Z] :=> Out
    def apply[Z](implicit down: Down[Z]): down.type = down

    implicit def hlistDown[C, L <: HList, RH <: HList, RT <: HList, P]:
      Down[Zipper[C, L, RH :: RT, P]] :=> Zipper[RH, HNil, RH, Some[Zipper[C, L, RH :: RT, P]]] =
        new Down[Zipper[C, L, RH :: RT, P]] {
          type Out = Zipper[RH, HNil, RH, Some[Zipper[C, L, RH :: RT, P]]]
          def apply(z: Zipper[C, L, RH :: RT, P]) = Zipper(HNil, z.suffix.head, Some(z))
        }

    implicit def genericDown[C, L <: HList, RH, RT <: HList, P, RHL <: HList](implicit gen: Generic.Aux[RH, RHL]):
      Down[Zipper[C, L, RH :: RT, P]] :=> Zipper[RH, HNil, RHL, Some[Zipper[C, L, RH :: RT, P]]] =
        new Down[Zipper[C, L, RH :: RT, P]] {
          type Out = Zipper[RH, HNil, RHL, Some[Zipper[C, L, RH :: RT, P]]]
          def apply(z: Zipper[C, L, RH :: RT, P]) = Zipper(HNil, gen.to(z.suffix.head), Some(z))
        }
  }

  trait Root[Z] extends DepFn1[Z]
  object Root extends {
    type Aux[Z, Out] = Root[Z] :=> Out
    def apply[Z](implicit root: Root[Z]): root.type = root

    implicit def rootRoot[C, L <: HList, R <: HList]: Root[Zipper[C, L, R, None.type]] :=> Zipper[C, L, R, None.type] =
      new Root[Zipper[C, L, R, None.type]] {
        type Out = Zipper[C, L, R, None.type]
        def apply(z: Zipper[C, L, R, None.type]) = z
      }

    implicit def nonRootRoot[C, L <: HList, R <: HList, P, U](
      implicit
      up: Up[Zipper[C, L, R, Some[P]]] :=> U,
      pr: Root[U]
    ): Root[Zipper[C, L, R, Some[P]]] :=> pr.Out =
      new Root[Zipper[C, L, R, Some[P]]] {
        type Out = pr.Out
        def apply(z: Zipper[C, L, R, Some[P]]) = pr(z.up)
      }
  }

  trait Get[Z] extends DepFn1[Z]
  object Get {
    type Aux[Z, Out] = Get[Z] :=> Out
    def apply[Z](implicit get: Get[Z]): get.type = get

    implicit def get[C, L <: HList, RH, RT <: HList, P]: Get[Zipper[C, L, RH :: RT, P]] :=> RH =
      new Get[Zipper[C, L, RH :: RT, P]] {
        type Out = RH
        def apply(z: Zipper[C, L, RH :: RT, P]) = z.suffix.head
      }
  }

  trait Put[Z, E] extends DepFn2[Z, E]
  object Put {
    type Aux[Z, E, Out] = Put[Z, E] :=> Out
    def apply[Z, E](implicit put: Put[Z, E]): put.type = put

    implicit def genericPut[C, L <: HList, RH, RT <: HList, P, E, CL <: HList](
      implicit
      gen: Generic.Aux[C, CL],
      rp: ReversePrepend[L, E :: RT] :=> CL
    ): Put[Zipper[C, L, RH :: RT, P], E] :=> Zipper[C, L, E :: RT, P] =
      new Put[Zipper[C, L, RH :: RT, P], E] {
        type Out = Zipper[C, L, E :: RT, P]
        def apply(z: Zipper[C, L, RH :: RT, P], e: E) = Zipper(z.prefix, e :: z.suffix.tail, z.parent)
      }

    implicit def hlistPut[C <: HList, L <: HList, RH, RT <: HList, P, E, CL <: HList](
      implicit rp: ReversePrepend[L, E :: RT] :=> CL
    ): Put[Zipper[C, L, RH :: RT, P], E] :=> Zipper[CL, L, E :: RT, P] =
      new Put[Zipper[C, L, RH :: RT, P], E] {
        type Out = Zipper[CL, L, E :: RT, P]
        def apply(z: Zipper[C, L, RH :: RT, P], e: E) = Zipper(z.prefix, e :: z.suffix.tail, z.parent)
      }
  }

  trait Modify[Z, E1, E2] extends DepFn2[Z, E1 => E2]
  object Modify {
    type Aux[Z, E1, E2, Out] = Modify[Z, E1, E2] :=> Out
    def apply[Z, E1, E2](implicit modify: Modify[Z, E1, E2]): modify.type = modify

    implicit def modify[C, L <: HList, RH1, RT <: HList, P, RH2](
      implicit
      get: Get[Zipper[C, L, RH1 :: RT, P]] :=> RH1,
      put: Put[Zipper[C, L, RH1 :: RT, P], RH2] :=> Zipper[C, L, RH2 :: RT, P]
    ): Modify[Zipper[C, L, RH1 :: RT, P], RH1, RH2] :=> Zipper[C, L, RH2 :: RT, P] =
        new Modify[Zipper[C, L, RH1 :: RT, P], RH1, RH2] {
          type Out = Zipper[C, L, RH2 :: RT, P]
          def apply(z: Zipper[C, L, RH1 :: RT, P], f: RH1 => RH2) = put(z, f(get(z)))
        }
  }

  trait Insert[Z, E] extends DepFn2[Z, E]
  object Insert {
    type Aux[Z, E, Out] = Insert[Z, E] :=> Out
    def apply[Z, E](implicit insert: Insert[Z, E]): insert.type = insert

    implicit def hlistInsert[C <: HList, L <: HList, R <: HList, P, E, CL <: HList](
      implicit rp: ReversePrepend[E :: L, R] :=> CL
    ): Insert[Zipper[C, L, R, P], E] :=> Zipper[CL, E :: L, R, P] =
      new Insert[Zipper[C, L, R, P], E] {
        type Out = Zipper[CL, E :: L, R, P]
        def apply(z: Zipper[C, L, R, P], e: E) = Zipper(e :: z.prefix, z.suffix, z.parent)
      }
  }

  trait Delete[Z] extends DepFn1[Z]
  object Delete {
    type Aux[Z, Out] = Delete[Z] :=> Out
    def apply[Z](implicit delete: Delete[Z]): delete.type = delete

    implicit def hlistDelete[C <: HList, L <: HList, RH, RT <: HList, P, CL <: HList](
      implicit rp: ReversePrepend[L, RT] :=> CL
    ): Delete[Zipper[C, L, RH :: RT, P]] :=> Zipper[CL, L, RT, P] =
      new Delete[Zipper[C, L, RH :: RT, P]] {
        type Out = Zipper[CL, L, RT, P]
        def apply(z: Zipper[C, L, RH :: RT, P]) = Zipper(z.prefix, z.suffix.tail, z.parent)
      }
  }

  trait Reify[Z] extends DepFn1[Z]
  object Reify {
    type Aux[Z, Out] = Reify[Z] :=> Out
    def apply[Z](implicit reify: Reify[Z]): reify.type = reify

    implicit def hlistReify[LR <: HList, L <: HList, R <: HList, P](
      implicit rp: ReversePrepend[L, R] :=> LR
    ): Reify[Zipper[LR, L, R, P]] :=> LR =
      new Reify[Zipper[LR, L, R, P]] {
        type Out = LR
        def apply(z: Zipper[LR, L, R, P]) = z.prefix reverse_::: z.suffix
      }

    implicit def genericReify[C, L <: HList, R <: HList, P, CL <: HList](
      implicit
      gen: Generic.Aux[C, CL],
      rp: ReversePrepend[L, R] :=> CL
    ): Reify[Zipper[C, L, R, P]] :=> C =
      new Reify[Zipper[C, L, R, P]] {
        type Out = C
        def apply(z: Zipper[C, L, R, P]) = gen.from(z.prefix reverse_::: z.suffix)
      }
  }
}
