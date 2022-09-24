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

import scala.annotation.implicitNotFound

object tuple {
  import shapeless.ops.{ hlist => hl }

  /**
   * Type class witnessing that this tuple is composite and providing access to head and tail.
   *
   * @author Miles Sabin
   */
  trait IsComposite[P] extends Serializable {
    type H
    type T
    def head(p: P) : H
    def tail(p: P) : T
  }

  object IsComposite {
    type Aux[P, H0, T0] = IsComposite[P] { type H = H0; type T = T0 }
    def apply[P](implicit isComp: IsComposite[P]): isComp.type = isComp

    implicit def isComposite[P, L <: HList, H0, T <: HList](
      implicit
      gen: Generic.Aux[P, L],
      isHCons: hl.IsHCons.Aux[L, H0, T],
      tp: hl.Tupler[T]
    ): Aux[P, H0, tp.Out] = new IsComposite[P] {
      type H = H0
      type T = tp.Out
      def head(p: P) = isHCons.head(gen.to(p))
      def tail(p: P) = tp(isHCons.tail(gen.to(p)))
    }
  }

  /**
   * Type class supporting prepending to this tuple.
   *
   * @author Miles Sabin
   */
  trait Prepend[T, U] extends DepFn2[T, U]
  object Prepend {
    type Aux[T, U, Out] = Prepend[T, U] :=> Out
    def apply[T, U](implicit prepend: Prepend[T, U]): prepend.type = prepend

    implicit def prepend[T, L1 <: HList, U, L2 <: HList, L3 <: HList](
      implicit
      gent: Generic.Aux[T, L1],
      genu: Generic.Aux[U, L2],
      prepend: hl.Prepend[L1, L2] :=> L3,
      tp: hl.Tupler[L3]
    ): Prepend[T, U] :=> tp.Out = new Prepend[T, U] {
      type Out = tp.Out
      def apply(t: T, u: U) = prepend(gent.to(t), genu.to(u)).tupled
    }
  }

  /**
   * Type class supporting reverse prepending to this tuple.
   *
   * @author Miles Sabin
   */
  trait ReversePrepend[T, U] extends DepFn2[T, U]
  object ReversePrepend {
    type Aux[T, U, Out] = ReversePrepend[T, U] :=> Out
    def apply[T, U](implicit prepend: ReversePrepend[T, U]): prepend.type = prepend

    implicit def prepend[T, L1 <: HList, U, L2 <: HList, L3 <: HList](
      implicit
      gent: Generic.Aux[T, L1],
      genu: Generic.Aux[U, L2],
      prepend: hl.ReversePrepend[L1, L2] :=> L3,
      tp: hl.Tupler[L3]
    ): ReversePrepend[T, U] :=> tp.Out = new ReversePrepend[T, U] {
      type Out = tp.Out
      def apply(t: T, u: U) = prepend(gent.to(t), genu.to(u)).tupled
    }
  }

  /**
   * Type class supporting access to the ''nth'' element of this tuple. Available only if this tuple has at least
   * ''n'' elements.
   *
   * @author Miles Sabin
   */
  trait At[T, N <: Nat] extends DepFn1[T]
  object At {
    type Aux[T, N <: Nat, Out] = At[T, N] :=> Out
    def apply[T, N <: Nat](implicit at: At[T, N]): at.type = at

    implicit def at[T, L1 <: HList, N <: Nat](
      implicit
      gen: Generic.Aux[T, L1],
      at: hl.At[L1, N]
    ): At[T, N] :=> at.Out = new At[T, N] {
        type Out = at.Out
        def apply(t: T) = at(gen.to(t))
      }
  }

  /**
   * Type class supporting access to the last element of this tuple. Available only if this tuple has at least one
   * element.
   *
   * @author Miles Sabin
   */
  trait Last[T] extends DepFn1[T]
  object Last {
    type Aux[T, Out] = Last[T] :=> Out
    def apply[T](implicit last: Last[T]): last.type = last

    implicit def last[T, L <: HList](
      implicit
      gen: Generic.Aux[T, L],
      last: hl.Last[L]
    ): Last[T] :=> last.Out = new Last[T] {
      type Out = last.Out
      def apply(t: T) = gen.to(t).last
    }
  }

  /**
   * Type class supporting access to all but the last element of this tuple. Available only if this tuple has at
   * least one element.
   *
   * @author Miles Sabin
   */
  trait Init[T] extends DepFn1[T]
  object Init {
    type Aux[T, Out] = Init[T] :=> Out
    def apply[T](implicit init: Init[T]): init.type = init

    implicit def init[T, L1 <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      init: hl.Init[L1] :=> L2,
      tp: hl.Tupler[L2]
    ): Init[T] :=> tp.Out = new Init[T] {
      type Out = tp.Out
      def apply(t: T) = init(gen.to(t)).tupled
    }
  }

  /**
   * Type class supporting access to the first element of this tuple of type `U`. Available only if this tuple
   * contains an element of type `U`.
   *
   * @author Miles Sabin
   */
  trait Selector[T, U] extends DepFn1[T] {
    type Out = U
  }

  object Selector {
    type Aux[T, U] = Selector[T, U]
    def apply[T, U](implicit selector: Selector[T, U]): Aux[T, U] = selector

    implicit def select[T, L <: HList, U](
      implicit
      gen: Generic.Aux[T, L],
      selector: hl.Selector[L, U]
    ): Selector[T, U] = new Selector[T, U] {
      def apply(t: T) = gen.to(t).select[U]
    }
  }

  /**
   * Type class supporting access to the all elements of this tuple of type `U`.
   *
   * @author Miles Sabin
   */
  trait Filter[T, U] extends DepFn1[T]
  object Filter {
    type Aux[T, U, Out] = Filter[T, U] :=> Out
    def apply[T, U](implicit filter: Filter[T, U]): filter.type = filter

    implicit def filterTuple[T, L1 <: HList, U, L2 <: HList, O](
      implicit
      gen: Generic.Aux[T, L1],
      filter: hl.Filter[L1, U] :=> L2,
      tp: hl.Tupler[L2] :=> O
    ): Filter[T, U] :=> O = new Filter[T, U] {
      type Out = O
      def apply(t: T) = tp(filter(gen.to(t)))
    }
  }

  /**
   * Type class supporting access to the all elements of this tuple of type different than `U`.
   *
   * @author Miles Sabin
   */
  trait FilterNot[T, U] extends DepFn1[T]
  object FilterNot {
    type Aux[T, U, Out] = FilterNot[T, U] :=> Out
    def apply[T, U](implicit filter: FilterNot[T, U]): filter.type = filter

    implicit def filterNotTuple[T, L1 <: HList, U, L2 <: HList, O](
      implicit
      gen: Generic.Aux[T, L1],
      filterNot: hl.FilterNot[L1, U] :=> L2,
      tp: hl.Tupler[L2] :=> O
    ): FilterNot[T, U] :=> O = new FilterNot[T, U] {
      type Out = O
      def apply(t: T) = tp(filterNot(gen.to(t)))
    }
  }

  /**
   * Type class supporting removal of an element from this tuple. Available only if this tuple contains an
   * element of type `U`.
   *
   * @author Miles Sabin
   */
  trait Remove[T, U] extends DepFn1[T]
  object Remove {
    type Aux[T, U, Out] = Remove[T, U] :=> Out
    def apply[T, E](implicit remove: Remove[T, E]): remove.type = remove

    implicit def removeTuple[T, L1 <: HList, U, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      remove: hl.Remove[L1, U] :=> (U, L2),
      tp: hl.Tupler[L2]
    ): Remove[T, U] :=> (U, tp.Out) = new Remove[T, U] {
      type Out = (U, tp.Out)
      def apply(t: T) = {
        val (u, rem) = remove(gen.to(t))
        (u, tp(rem))
      }
    }
  }

  /**
   * Type class supporting removal of a sublist from this tuple. Available only if this tuple contains a
   * sublist of type `SL`.
   *
   * The elements of `SL` do not have to be contiguous in this tuple.
   *
   * @author Miles Sabin
   */
  trait RemoveAll[T, S] extends DepFn1[T]
  object RemoveAll {
    type Aux[T, S, Out] = RemoveAll[T, S] :=> Out
    def apply[T, S](implicit remove: RemoveAll[T, S]): remove.type = remove

    implicit def removeAllTuple[T, ST, SL <: HList, L1 <: HList, L2 <: HList](
      implicit
      gent: Generic.Aux[T, L1],
      gens: Generic.Aux[ST, SL],
      removeAll: hl.RemoveAll[L1, SL] :=> (SL, L2),
      tp: hl.Tupler[L2]
    ): RemoveAll[T, ST] :=> (ST, tp.Out) = new RemoveAll[T, ST] {
      type Out = (ST, tp.Out)
      def apply(t: T) = {
        val (e, rem) = removeAll(gent.to(t))
        (gens.from(e), tp(rem))
      }
    }
  }

  /**
   * Type class supporting replacement of the first element of type V from this tuple with an element of type U.
   * Available only if this tuple contains an element of type `V`.
   *
   * @author Miles Sabin
   */
  trait Replacer[T, U, V] extends DepFn2[T, V]
  object Replacer {
    type Aux[T, U, V, Out] = Replacer[T, U, V] :=> Out
    def apply[T, U, V](implicit replacer: Replacer[T, U, V]): replacer.type = replacer

    implicit def replaceTuple[T, L1 <: HList, U, V, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      replace: hl.Replacer[L1, U, V] :=> (U, L2),
      tp: hl.Tupler[L2]
    ): Replacer[T, U, V] :=> (U, tp.Out) = new Replacer[T, U, V] {
      type Out = (U, tp.Out)
      def apply(t: T, v: V) = {
        val (u, rep) = replace(gen.to(t), v)
        (u, tp(rep))
      }
    }
  }

  /**
   * Type class supporting replacement of the Nth element of this tuple with an element of type V. Available only if
   * this tuple contains at least N elements.
   *
   * @author Miles Sabin
   */
  trait ReplaceAt[T, N <: Nat, U] extends DepFn2[T, U]
  object ReplaceAt {
    type Aux[T, N <: Nat, U, Out] = ReplaceAt[T, N, U] :=> Out
    def apply[T, N <: Nat, V](implicit replacer: ReplaceAt[T, N, V]): replacer.type = replacer

    implicit def replaceTuple[T, L1 <: HList, N <: Nat, U, V, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      replaceAt: hl.ReplaceAt[L1, N, U] :=> (V, L2),
      tp: hl.Tupler[L2]
    ): ReplaceAt[T, N, U] :=> (V, tp.Out) = new ReplaceAt[T, N, U] {
      type Out = (V, tp.Out)
      def apply(t: T, u: U) = {
        val (v, rep) = replaceAt(gen.to(t), u)
        (v, tp(rep))
      }
    }
  }

  /**
   * Type class supporting replacement of the first element of type U from this tuple with the result of
   * its transformation via a given function into a new element of type V.
   * Available only if this tuple contains an element of type `U`.
   *
   * @author Howard Branch
   */
  trait Modifier[T, U, V] extends DepFn2[T, U => V]
  object Modifier {
    type Aux[T, U, V, Out] = Modifier[T, U, V] :=> Out
    def apply[T, U, V](implicit modifier: Modifier[T, U, V]): modifier.type = modifier

    implicit def modifyTuple[T, L1 <: HList, U, V, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      modify: hl.Modifier[L1, U, V] :=> (U, L2),
      tp: hl.Tupler[L2]
    ): Modifier[T, U, V] :=> (U, tp.Out) = new Modifier[T, U, V] {
      type Out = (U, tp.Out)
      def apply(t: T, f: U => V) = {
        val (u, rep) = modify(gen.to(t), f)
        (u, tp(rep))
      }
    }
  }

  /**
   * Type class supporting replacement of the `N`th element of this `Tuple` with the result of
   * calling `F` on it.
   * Available only if this `Tuple` contains at least `N` elements.
   *
   * @author Andreas Koestler
   */
  trait ModifierAt[T, N <: Nat, U, V] extends DepFn2[T, U => V]
  object ModifierAt {
    type Aux[T, N <: Nat, U, V, Out] = ModifierAt[T, N, U, V] :=> Out
    def apply[T, N <: Nat, U, V](implicit modifier: ModifierAt[T, N, U, V]): modifier.type = modifier

    implicit def modifyTuple[S, T, U, V, N <: Nat, L <: HList, OutL <: HList](
      implicit
      gen: Generic.Aux[T, L],
      modifier: hl.ModifierAt[L, N, U, V] :=> (S, OutL),
      tup: hl.Tupler[OutL]
    ): ModifierAt[T, N, U, V] :=> (S, tup.Out) = new ModifierAt[T, N, U, V] {
      type Out = (S, tup.Out)
      def apply(t: T, f: U => V) = {
        val (u, rep) = modifier(gen.to(t), f);
        (u, tup(rep))
      }
    }
  }
  /**
   * Type class supporting retrieval of the first ''n'' elements of this tuple. Available only if this tuple has at
   * least ''n'' elements.
   *
   * @author Miles Sabin
   */
  trait Take[T, N <: Nat] extends DepFn1[T]
  object Take {
    type Aux[T, N <: Nat, Out] = Take[T, N] :=> Out
    def apply[T, N <: Nat](implicit take: Take[T, N]): take.type = take

    implicit def tupleTake[T, L1 <: HList, N <: Nat, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      take: hl.Take[L1, N] :=> L2,
      tp: hl.Tupler[L2]
    ): Take[T, N] :=> tp.Out = new Take[T, N] {
      type Out = tp.Out
      def apply(t: T) = tp(take(gen.to(t)))
    }
  }

  /**
   * Type class supporting removal of the first ''n'' elements of this tuple. Available only if this tuple has at
   * least ''n'' elements.
   *
   * @author Miles Sabin
   */
  trait Drop[T, N <: Nat] extends DepFn1[T]
  object Drop {
    type Aux[T, N <: Nat, Out] = Drop[T, N] :=> Out
    def apply[T, N <: Nat](implicit drop: Drop[T, N]): drop.type = drop

    implicit def tupleDrop[T, L1 <: HList, N <: Nat, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      drop: hl.Drop[L1, N] :=> L2,
      tp: hl.Tupler[L2]
    ): Drop[T, N] :=> tp.Out = new Drop[T, N] {
      type Out = tp.Out
      def apply(t: T) = tp(drop(gen.to(t)))
    }
  }

  /**
   * Type class supporting splitting this tuple at the ''nth'' element returning the prefix and suffix as a pair.
   * Available only if this tuple has at least ''n'' elements.
   *
   * @author Miles Sabin
   */
  trait Split[T, N <: Nat] extends DepFn1[T]
  object Split {
    type Aux[T, N <: Nat, Out] = Split[T, N] :=> Out
    def apply[T, N <: Nat](implicit split: Split[T, N]): split.type = split

    implicit def tupleSplit[T, L <: HList, N <: Nat, LP <: HList, LS <: HList](
      implicit
      gen: Generic.Aux[T, L],
      split: hl.Split.Aux[L, N, LP, LS],
      tpp: hl.Tupler[LP],
      tps: hl.Tupler[LS]
    ): Split[T, N] :=> (tpp.Out, tps.Out) = new Split[T, N] {
      type Out = (tpp.Out, tps.Out)
      def apply(t: T) = {
        val p :: s :: HNil = split.product(gen.to(t))
        (tpp(p), tps(s))
      }
    }
  }

  /**
   * Type class supporting splitting this tuple at the ''nth'' element returning the reverse prefix and suffix as a
   * pair. Available only if this tuple has at least ''n'' elements.
   *
   * @author Miles Sabin
   */
  trait ReverseSplit[T, N <: Nat] extends DepFn1[T]
  object ReverseSplit {
    type Aux[T, N <: Nat, Out] = ReverseSplit[T, N] :=> Out
    def apply[T, N <: Nat](implicit split: ReverseSplit[T, N]): split.type = split

    implicit def tupleReverseSplit[T, L <: HList, N <: Nat, LP <: HList, LS <: HList](
      implicit
      gen: Generic.Aux[T, L],
      split: hl.ReverseSplit.Aux[L, N, LP, LS],
      tpp: hl.Tupler[LP],
      tps: hl.Tupler[LS]
    ): ReverseSplit[T, N] :=> (tpp.Out, tps.Out) = new ReverseSplit[T, N] {
      type Out = (tpp.Out, tps.Out)
      def apply(t: T) = {
        val p :: s :: HNil = split.product(gen.to(t))
        (tpp(p), tps(s))
      }
    }
  }

  /**
   * Type class supporting splitting this tuple at the first occurrence of an element of type `U` returning the prefix
   * and suffix as a pair. Available only if this tuple contains an element of type `U`.
   *
   * @author Miles Sabin
   */
  trait SplitLeft[T, U] extends DepFn1[T]
  object SplitLeft {
    type Aux[T, U, Out] = SplitLeft[T, U] :=> Out
    def apply[T, U](implicit split: SplitLeft[T, U]): split.type = split

    implicit def tupleSplitLeft[T, L <: HList, U, LP <: HList, LS <: HList](
      implicit
      gen: Generic.Aux[T, L],
      split: hl.SplitLeft.Aux[L, U, LP, LS],
      tpp: hl.Tupler[LP],
      tps: hl.Tupler[LS]
    ): SplitLeft[T, U] :=> (tpp.Out, tps.Out) = new SplitLeft[T, U] {
      type Out = (tpp.Out, tps.Out)
      def apply(t: T) = {
        val p :: s :: HNil = split.product(gen.to(t))
        (tpp(p), tps(s))
      }
    }
  }

  /**
   * Type class supporting splitting this tuple at the first occurrence of an element of type `U` returning the reverse
   * prefix and suffix as a pair. Available only if this tuple contains an element of type `U`.
   *
   * @author Miles Sabin
   */
  trait ReverseSplitLeft[T, U] extends DepFn1[T]
  object ReverseSplitLeft {
    type Aux[T, U, Out] = ReverseSplitLeft[T, U] :=> Out
    def apply[T, U](implicit split: ReverseSplitLeft[T, U]): split.type = split

    implicit def tupleReverseSplitLeft[T, L <: HList, U, LP <: HList, LS <: HList](
      implicit
      gen: Generic.Aux[T, L],
      split: hl.ReverseSplitLeft.Aux[L, U, LP, LS],
      tpp: hl.Tupler[LP],
      tps: hl.Tupler[LS]
    ): ReverseSplitLeft[T, U] :=> (tpp.Out, tps.Out) = new ReverseSplitLeft[T, U] {
      type Out = (tpp.Out, tps.Out)
      def apply(t: T) = {
        val p :: s :: HNil = split.product(gen.to(t))
        (tpp(p), tps(s))
      }
    }
  }

  /**
   * Type class supporting splitting this tuple at the last occurrence of an element of type `U` returning the prefix
   * and suffix as a pair. Available only if this tuple contains an element of type `U`.
   *
   * @author Miles Sabin
   */
  trait SplitRight[T, U] extends DepFn1[T]

  object SplitRight {
    type Aux[T, U, Out] = SplitRight[T, U] :=> Out
    def apply[T, U](implicit split: SplitRight[T, U]): split.type = split

    implicit def tupleSplitRight[T, L <: HList, U, LP <: HList, LS <: HList](
      implicit
      gen: Generic.Aux[T, L],
      split: hl.SplitRight.Aux[L, U, LP, LS],
      tpp: hl.Tupler[LP],
      tps: hl.Tupler[LS]
    ): SplitRight[T, U] :=> (tpp.Out, tps.Out) = new SplitRight[T, U] {
      type Out = (tpp.Out, tps.Out)
      def apply(t: T) = {
        val p :: s :: HNil = split.product(gen.to(t))
        (tpp(p), tps(s))
      }
    }
  }

  /**
   * Type class supporting splitting this tuple at the last occurrence of an element of type `U` returning the reverse
   * prefix and suffix as a pair. Available only if this tuple contains an element of type `U`.
   *
   * @author Miles Sabin
   */
  trait ReverseSplitRight[T, U] extends DepFn1[T]
  object ReverseSplitRight {
    type Aux[T, U, Out] = ReverseSplitRight[T, U] :=> Out
    def apply[T, U](implicit split: ReverseSplitRight[T, U]): split.type = split

    implicit def tupleReverseSplitRight[T, L <: HList, U, LP <: HList, LS <: HList](
      implicit
      gen: Generic.Aux[T, L],
      split: hl.ReverseSplitRight.Aux[L, U, LP, LS],
      tpp: hl.Tupler[LP],
      tps: hl.Tupler[LS]
    ): ReverseSplitRight[T, U] :=> (tpp.Out, tps.Out) = new ReverseSplitRight[T, U] {
      type Out = (tpp.Out, tps.Out)
      def apply(t: T) = {
        val p :: s :: HNil = split.product(gen.to(t))
        (tpp(p), tps(s))
      }
    }
  }

  /**
   * Type class supporting reversing this tuple.
   *
   * @author Miles Sabin
   */
  trait Reverse[T] extends DepFn1[T]
  object Reverse {
    type Aux[T, Out] = Reverse[T] :=> Out
    def apply[T](implicit reverse: Reverse[T]): reverse.type = reverse

    implicit def tupleReverseAux[T, L1 <: HList, L2 <: HList, Out](
      implicit
      gen: Generic.Aux[T, L1],
      reverse: hl.Reverse[L1] :=> L2,
      tp: hl.Tupler[L2]
    ): Reverse[T] :=> tp.Out = new Reverse[T] {
      type Out = tp.Out
      def apply(t: T) = tp(reverse(gen.to(t)))
    }
  }

  /**
   * Type class supporting mapping a higher ranked function over this tuple.
   *
   * @author Miles Sabin
   */
  trait Mapper[T, P] extends DepFn1[T]
  object Mapper {
    type Aux[T, P, Out] = Mapper[T, P] :=> Out
    def apply[T, P](implicit mapper: Mapper[T, P]): mapper.type = mapper

    implicit def mapper[T, P, L1 <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      mapper: hl.Mapper[P, L1] :=> L2,
      tp: hl.Tupler[L2]
    ): Mapper[T, P] :=> tp.Out = new Mapper[T, P] {
      type Out = tp.Out
      def apply(t: T) = tp(mapper(gen.to(t)))
    }
  }

  /**
   * Type class supporting flatmapping a higher ranked function over this tuple.
   *
   * @author Miles Sabin
   */
  trait FlatMapper[T, P] extends DepFn1[T]
  object FlatMapper {
    import poly.Compose

    type Aux[T, P, Out] = FlatMapper[T, P] :=> Out
    def apply[T, P](implicit mapper: FlatMapper[T, P]): mapper.type = mapper

    implicit def mapper[T, P, L1 <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      mapper: hl.FlatMapper[Compose[productElements.type, P], L1] :=> L2,
      tp: hl.Tupler[L2]
    ): FlatMapper[T, P] :=> tp.Out = new FlatMapper[T, P] {
      type Out = tp.Out
      def apply(t: T) = tp(mapper(gen.to(t)))
    }
  }

  /**
   * Type class supporting mapping a constant valued function over this tuple.
   *
   * @author Miles Sabin
   */
  trait ConstMapper[T, C] extends DepFn2[T, C]
  object ConstMapper {
    type Aux[T, C, Out] = ConstMapper[T, C] :=> Out
    def apply[T, C](implicit mapper: ConstMapper[T, C]): mapper.type = mapper

    implicit def mapper[T, C, L1 <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      mapper: hl.ConstMapper[C, L1] :=> L2,
      tp: hl.Tupler[L2]
    ): ConstMapper[T, C] :=> tp.Out = new ConstMapper[T, C] {
      type Out = tp.Out
      def apply(t: T, c: C) = tp(mapper(c, gen.to(t)))
    }
  }

  /**
   * Type class supporting mapping a polymorphic function over this tuple and then folding the result using a
   * monomorphic function value.
   *
   * @author Miles Sabin
   */
  trait MapFolder[T, R, P] extends Serializable { // Nb. Not a dependent function signature
    def apply(t: T, in: R, op: (R, R) => R): R
  }

  object MapFolder {
    def apply[T, R, P](implicit folder: MapFolder[T, R, P]): MapFolder[T, R, P] = folder

    implicit def mapper[T, L <: HList, R, P](
      implicit
      gen: Generic.Aux[T, L],
      mapper: hl.MapFolder[L, R, P]
    ): MapFolder[T, R, P] =
      (t, in, op) => mapper(gen.to(t), in, op)
  }

  /**
   * Type class supporting left-folding a polymorphic binary function over this tuple.
   *
   * @author Miles Sabin
   */
  trait LeftFolder[T, U, P] extends DepFn2[T, U]
  object LeftFolder {
    type Aux[T, U, P, Out] = LeftFolder[T, U, P] :=> Out
    def apply[T, U, P](implicit folder: LeftFolder[T, U, P]): folder.type = folder

    implicit def folder[T, L <: HList, U, P](
      implicit
      gen: Generic.Aux[T, L],
      folder: hl.LeftFolder[L, U, P]
    ): LeftFolder[T, U, P] :=> folder.Out = new LeftFolder[T, U, P] {
      type Out = folder.Out
      def apply(t: T, u: U) = folder(gen.to(t), u)
    }
  }

  /**
   * Type class supporting right-folding a polymorphic binary function over this tuple.
   *
   * @author Miles Sabin
   */
  trait RightFolder[T, U, P] extends DepFn2[T, U]
  object RightFolder {
    type Aux[T, U, P, Out] = RightFolder[T, U, P] :=> Out
    def apply[T, U, P](implicit folder: RightFolder[T, U, P]): folder.type = folder

    implicit def folder[T, L <: HList, U, P](
      implicit
      gen: Generic.Aux[T, L],
      folder: hl.RightFolder[L, U, P]
    ): RightFolder[T, U, P] :=> folder.Out = new RightFolder[T, U, P] {
      type Out = folder.Out
      def apply(t: T, u: U) = folder(gen.to(t), u)
    }
  }

  /**
   * Type class supporting left-reducing a polymorphic binary function over this tuple.
   *
   * @author Miles Sabin
   */
  trait LeftReducer[T, P] extends DepFn1[T]
  object LeftReducer {
    type Aux[T, P, Out] = LeftReducer[T, P] :=> Out
    def apply[T, P](implicit reducer: LeftReducer[T, P]): reducer.type = reducer

    implicit def folder[T, L <: HList, P](
      implicit
      gen: Generic.Aux[T, L],
      folder: hl.LeftReducer[L, P]
    ): LeftReducer[T, P] :=> folder.Out = new LeftReducer[T, P] {
      type Out = folder.Out
      def apply(t: T) = folder(gen.to(t))
    }
  }

  /**
   * Type class supporting right-reducing a polymorphic binary function over this tuple.
   *
   * @author Miles Sabin
   */
  trait RightReducer[T, P] extends DepFn1[T]
  object RightReducer {
    type Aux[T, P, Out] = RightReducer[T, P] :=> Out
    def apply[T, P](implicit reducer: RightReducer[T, P]): reducer.type = reducer

    implicit def folder[T, L <: HList, P](
      implicit
      gen: Generic.Aux[T, L],
      folder: hl.RightReducer[L, P]
    ): RightReducer[T, P] :=> folder.Out = new RightReducer[T, P] {
      type Out = folder.Out
      def apply(t: T) = folder(gen.to(t))
    }
  }

  /**
   * Type class supporting transposing this tuple.
   *
   * @author Miles Sabin
   */
  trait Transposer[T] extends DepFn1[T]
  object Transposer {
    type Aux[T, Out] = Transposer[T] :=> Out
    def apply[T](implicit transposer: Transposer[T]): transposer.type = transposer

    implicit def transpose[T, L1 <: HList, L2 <: HList, L3 <: HList, L4 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      mpe: hl.Mapper[productElements.type, L1] :=> L2,
      tps: hl.Transposer[L2] :=> L3,
      mtp: hl.Mapper[tupled.type, L3] :=> L4,
      tp: hl.Tupler[L4]
    ): Transposer[T] :=> tp.Out = new Transposer[T] {
      type Out = tp.Out
      def apply(t: T) = ((gen.to(t) map productElements).transpose map tupled).tupled
    }
  }

  /**
   * Type class supporting zipping this this tuple of monomorphic function values with its argument tuple of
   * correspondingly typed function arguments returning the result of each application as a tuple. Available only if
   * there is evidence that the corresponding function and argument elements have compatible types.
   *
   * @author Miles Sabin
   */
  trait ZipApply[FT, AT] extends DepFn2[FT, AT]
  object ZipApply {
    type Aux[FT, AT, Out] = ZipApply[FT, AT] :=> Out
    def apply[FT, AT](implicit zip: ZipApply[FT, AT]): zip.type = zip

    implicit def zipApply[FT, FL <: HList, AT, AL <: HList, RL <: HList](
      implicit
      genf: Generic.Aux[FT, FL],
      gena: Generic.Aux[AT, AL],
      zip: hl.ZipApply[FL, AL] :=> RL,
      tp: hl.Tupler[RL]
    ): ZipApply[FT, AT] :=> tp.Out = new ZipApply[FT, AT] {
      type Out = tp.Out
      def apply(ft: FT, at: AT) = (genf.to(ft) zipApply gena.to(at)).tupled
    }
  }

  /**
   * Type class supporting zipping this tuple with a tuple of tuples returning a tuple of tuples with each
   * element of this tuple prepended to the corresponding tuple element of the argument tuple.
   *
   * @author Miles Sabin
   */
  trait ZipOne[H, T] extends DepFn2[H, T]
  object ZipOne {
    type Aux[H, T, Out] = ZipOne[H, T] :=> Out
    def apply[H, T](implicit zip: ZipOne[H, T]): zip.type = zip

    implicit def zipOne[HT, HL <: HList, TT, TL <: HList, TLL <: HList, RLL <: HList, RL <: HList](
      implicit
      genh: Generic.Aux[HT, HL],
      gent: Generic.Aux[TT, TL],
      mpet: hl.Mapper[productElements.type, TL] :=> TLL,
      zone: hl.ZipOne[HL, TLL] :=> RLL,
      mtp: hl.Mapper[tupled.type, RLL] :=> RL,
      tp: hl.Tupler[RL]
    ): ZipOne[HT, TT] :=> tp.Out = new ZipOne[HT, TT] {
      type Out = tp.Out
      def apply(h: HT, t: TT) = ((genh.to(h) zipOne (gent.to(t) map productElements)) map tupled).tupled
    }
  }

  /**
   * Type class supporting zipping a tuple with a constant, resulting in a tuple of tuples of the form
   * ({element from input tuple}, {supplied constant})
   *
   * @author Miles Sabin
   */
  trait ZipConst[T, C] extends DepFn2[T, C]
  object ZipConst {
    type Aux[T, C, Out] = ZipConst[T, C] :=> Out
    def apply[T, C](implicit zip: ZipConst[T, C]): zip.type = zip

    implicit def zipConst[T, C, L1 <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      zipper: hl.ZipConst[C, L1] :=> L2,
      tp: hl.Tupler[L2]
    ): ZipConst[T, C] :=> tp.Out = new ZipConst[T, C] {
      type Out = tp.Out
      def apply(t: T, c: C) = tp(zipper(c, gen.to(t)))
    }
  }

  /**
   * Type class supporting zipping a tuple with its element indices, resulting in a tuple of tuples of the form
   * ({element from input tuple}, {element index})
   *
   * @author Andreas Koestler
   */
  trait ZipWithIndex[T] extends DepFn1[T]
  object ZipWithIndex {
    type Aux[T, Out] = ZipWithIndex[T] :=> Out
    def apply[T](implicit zip: ZipWithIndex[T]): zip.type = zip

    implicit def zipConst[T, L1 <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      zipper: hl.ZipWithIndex[L1] :=> L2,
      tp: hl.Tupler[L2]
    ): ZipWithIndex[T] :=> tp.Out = new ZipWithIndex[T] {
      type Out = tp.Out
      def apply(t: T) = tp(zipper(gen.to(t)))
    }
  }


  /**
   * Type class supporting unification of this tuple.
   *
   * @author Miles Sabin
   */
  trait Unifier[T] extends DepFn1[T]
  object Unifier {
    type Aux[T, Out] = Unifier[T] :=> Out
    def apply[T](implicit unifier: Unifier[T]): unifier.type = unifier

    implicit def unifier[T, L1 <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      unifier: hl.Unifier[L1] :=> L2,
      tp: hl.Tupler[L2]
    ): Unifier[T] :=> tp.Out = new Unifier[T] {
      type Out = tp.Out
      def apply(t: T) = unifier(gen.to(t)).tupled
    }
  }

  /**
   * Type class supporting unification of all elements that are subtypes of `B` in this tuple to `B`, with all other
   * elements left unchanged.
   *
   * @author Miles Sabin
   */
  trait SubtypeUnifier[T, B] extends DepFn1[T]
  object SubtypeUnifier {
    type Aux[T, B, Out] = SubtypeUnifier[T, B] :=> Out
    def apply[T, B](implicit unifier: SubtypeUnifier[T, B]): unifier.type = unifier

    implicit def subtypeUnifier[T, B, L1 <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L1],
      unifier: hl.SubtypeUnifier[L1, B] :=> L2,
      tp: hl.Tupler[L2]
    ): SubtypeUnifier[T, B] :=> tp.Out = new SubtypeUnifier[T, B] {
      type Out = tp.Out
      def apply(t: T) = unifier(gen.to(t)).tupled
    }
  }

  /**
   * Type class supporting computing the type-level Nat corresponding to the length of this tuple.
   *
   * @author Miles Sabin
   */
  trait Length[T] extends DepFn1[T]
  object Length {
    type Aux[T, Out] = Length[T] :=> Out
    def apply[T](implicit length: Length[T]): length.type = length

    implicit def length[T, L <: HList](
      implicit
      gen: Generic.Aux[T, L],
      length: hl.Length[L]
    ): Length[T] :=> length.Out = new Length[T] {
      type Out = length.Out
      def apply(t: T) = length()
    }
  }

  /**
   * Type class supporting conversion of this tuple to a `M` with elements typed as the least upper bound
   * of the types of the elements of this tuple.
   *
   * @author Alexandre Archambault
   */
  trait ToTraversable[T, M[_]] extends DepFn1[T] {
    type Lub
    type Out = M[Lub]
  }

  object ToTraversable {
    type Aux[T, M[_], L] = ToTraversable[T, M] { type Lub = L }
    def apply[T, M[_]](implicit toTraversable: ToTraversable[T, M]): toTraversable.type = toTraversable

    implicit def toTraversableNothing[M[_]](
      implicit tt: hl.ToTraversable.Aux[HNil, M, Nothing]
    ): Aux[Unit, M, Nothing] = new ToTraversable[Unit, M] {
      type Lub = Nothing
      def apply(t: Unit) = tt(HNil)
    }

    implicit def toTraversable[T, L <: HList, M[_], Lub](
      implicit
      gen: Generic.Aux[T, L],
      toTraversable: hl.ToTraversable.Aux[L, M, Lub]
    ): Aux[T, M, Lub] = new ToTraversable[T, M] {
      type Lub = toTraversable.Lub
      def apply(t: T) = gen.to(t).to[M]
    }
  }

  /**
   * Type class supporting conversion of this tuple to a `List` with elements typed as the least upper bound
   * of the types of the elements of this tuple.
   *
   * Provided for backward compatibility.
   *
   * @author Miles Sabin
   */
  trait ToList[T, Lub] extends DepFn1[T]
  object ToList {
    type Aux[T, Lub, Out] = ToList[T, Lub] :=> Out
    def apply[T, Lub](implicit toList: ToList[T, Lub]): toList.type = toList

    implicit def toList[T, Lub](
      implicit toTraversable: ToTraversable.Aux[T, List, Lub]
    ): ToList[T, Lub] :=> List[Lub] = new ToList[T, Lub] {
      type Out = List[Lub]
      def apply(t: T) = toTraversable(t)
    }

    implicit def toListNothing[T](
      implicit toTraversable: ToTraversable.Aux[T, List, Nothing]
    ): ToList[T, Nothing] :=> List[Nothing] =
      toList[T, Nothing]
  }

  /**
   * Type class supporting conversion of this tuple to an `Array` with elements typed as the least upper bound
   * of the types of the elements of this tuple.
   *
   * Provided for backward compatibility.
   *
   * @author Miles Sabin
   */
  trait ToArray[T, Lub] extends DepFn1[T]
  object ToArray {
    type Aux[T, Lub, Out] = ToArray[T, Lub] :=> Out
    def apply[T, Lub](implicit toArray: ToArray[T, Lub]): toArray.type = toArray

    implicit def toArray[T, Lub](
      implicit toTraversable: ToTraversable.Aux[T, Array, Lub]
    ): ToArray[T, Lub] :=> Array[Lub] = new ToArray[T, Lub] {
      type Out = Array[Lub]
      def apply(t: T) = toTraversable(t)
    }

    implicit def toArrayNothing[T](
      implicit toTraversable: ToTraversable.Aux[T, Array, Nothing]
    ): ToArray[T, Nothing] :=> Array[Nothing] =
        toArray[T, Nothing]
  }

  /**
   * Type class supporting conversion of this tuple to a `Sized[M[Lub], N]` with elements typed as
   * the least upper bound Lub of the types of the elements of this tuple.
   *
   * @author Alexandre Archambault
   */
  trait ToSized[T, M[_]] extends DepFn1[T]
  object ToSized {
    type Aux[T, M[_], Out] = ToSized[T, M] :=> Out
    def apply[T, M[_]](implicit toSized: ToSized[T, M]): toSized.type = toSized

    implicit def toSized[T, L <: HList, M[_]](
      implicit
      gen: Generic.Aux[T, L],
      toSized: hl.ToSized[L, M]
    ): ToSized[T, M] :=> toSized.Out = new ToSized[T, M] {
      type Out = toSized.Out
      def apply(t: T) = gen.to(t).toSized[M]
    }
  }

  /**
   * Type class computing the coproduct type corresponding to this tuple.
   *
   * @author Andreas Koestler
   */
  trait ToCoproduct[T] extends DepFn {
    type Out <: Coproduct
  }

  object ToCoproduct {
    type Aux[T, Out <: Coproduct] = ToCoproduct[T] :=> Out
    def apply[T](implicit tcp: ToCoproduct[T]): tcp.type = tcp

    implicit val hnilToCoproduct: ToCoproduct[HNil] :=> CNil =
      new ToCoproduct[HNil] { type Out = CNil }

    implicit def hlistToCoproduct[T, L <: HList](
      implicit
      gen: Generic.Aux[T, L],
      ut: hl.ToCoproduct[L]
    ): ToCoproduct[T] :=> ut.Out =
      new ToCoproduct[T] { type Out = ut.Out }
  }

  /**
   * Type class computing the sum type corresponding to this tuple.
   *
   * @author Andreas Koestler
   */
  trait ToSum[T] extends DepFn {
    type Out <: Coproduct
  }

  object ToSum {
    type Aux[T, Out <: Coproduct] = ToSum[T] :=> Out
    def apply[T](implicit tcp: ToSum[T]): tcp.type = tcp

    implicit val hnilToSum: ToSum[HNil] :=> CNil =
      new ToSum[HNil] { type Out = CNil }

    implicit def hlistToSum[T, L <: HList](
      implicit
      gen: Generic.Aux[T, L],
      ut: hl.ToSum[L]
    ): ToSum[T] :=> ut.Out =
      new ToSum[T] { type Out = ut.Out }
  }


  /**
   * Type Class witnessing that this tuple can be collected with a 'Poly' to produce a new tuple
   *
   * @author Stacy Curl
   */
  trait Collect[T, P <: Poly] extends DepFn1[T]
  object Collect {
    type Aux[T, P <: Poly, Out] = Collect[T, P] :=> Out
    def apply[T, P <: Poly](implicit collect: Collect[T, P]): collect.type = collect

    implicit def collect[T, L <: HList, L2 <: HList, P <: Poly](
      implicit
      gen: Generic.Aux[T, L],
      collect: hl.Collect[L, P] :=> L2,
      tp: hl.Tupler[L2]
    ): Collect[T, P] :=> tp.Out = new Collect[T, P] {
      type Out = tp.Out
      def apply(t: T) = tp(collect(gen.to(t)))
    }
  }

  /**
   * Typer class supporting the calculation of every permutation of this tuple
   *
   * @author Stacy Curl
   */
  trait Permutations[T] extends DepFn1[T]
  object Permutations {
    type Aux[T, Out] = Permutations[T] :=> Out
    def apply[T](implicit permutations: Permutations[T]): permutations.type = permutations

    implicit def permutations[T, L <: HList, L2 <: HList, L3 <: HList](
      implicit
      gen: Generic.Aux[T, L],
      collect: hl.Permutations[L] :=> L2,
      mapper: hl.Mapper[tupled.type, L2] :=> L3,
      tp: hl.Tupler[L3]
    ): Permutations[T] :=> tp.Out = new Permutations[T] {
      type Out = tp.Out
      def apply(t: T) = tp(collect(gen.to(t)).map(tupled))
    }
  }

  /**
   * Type class supporting rotating a tuple left
   *
   * @author Stacy Curl
   */
  trait RotateLeft[T, N <: Nat] extends DepFn1[T]
  object RotateLeft {
    type Aux[T, N <: Nat, Out] = RotateLeft[T, N] :=> Out
    def apply[T, N <: Nat](implicit rotate: RotateLeft[T, N]): rotate.type = rotate

    implicit def tupleRotateLeft[T, N <: Nat, L <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L],
      rotateLeft: hl.RotateLeft[L, N] :=> L2,
      tp: hl.Tupler[L2]
    ): RotateLeft[T, N] :=> tp.Out = new RotateLeft[T, N] {
      type Out = tp.Out
      def apply(t: T) = tp(rotateLeft(gen.to(t)))
    }
  }

  /**
   * Type class supporting rotating a tuple right
   *
   * @author Stacy Curl
   */
  trait RotateRight[T, N <: Nat] extends DepFn1[T]
  object RotateRight {
    type Aux[T, N <: Nat, Out] = RotateRight[T, N] :=> Out
    def apply[T, N <: Nat](implicit rotate: RotateRight[T, N]): rotate.type = rotate

    implicit def tupleRotateRight[T, N <: Nat, L <: HList, L2 <: HList](
      implicit
      gen: Generic.Aux[T, L],
      rotateRight: hl.RotateRight[L, N] :=> L2,
      tp: hl.Tupler[L2]
    ): RotateRight[T, N] :=> tp.Out = new RotateRight[T, N] {
      type Out = tp.Out
      def apply(t: T) = tp(rotateRight(gen.to(t)))
    }
  }

  /**
   * Type class supporting left-scanning a binary polymorphic function over this tuple.
   *
   * @author Owein Reese
   */
  trait LeftScanner[T, In, P <: Poly] extends DepFn2[T, In]
  object LeftScanner {
    type Aux[T, In, P <: Poly, Out] = LeftScanner[T, In, P] :=> Out
    def apply[T, In, P <: Poly](implicit scan: LeftScanner[T, In, P]): scan.type = scan

    implicit def scanner[T, L <: HList, In, P <: Poly, R <: HList](
      implicit gen: Generic.Aux[T, L],
      scanL: hl.LeftScanner[L, In, P] :=> R,
      tp: hl.Tupler[R]
    ): LeftScanner[T, In, P] :=> tp.Out = new LeftScanner[T, In, P] {
      type Out = tp.Out
      def apply(t: T, in: In) = tp(scanL(gen.to(t), in))
    }
  }

  /**
   * Type class supporting right-scanning a binary polymorphic function over this tuple.
   *
   * @author Owein Reese
   */
  trait RightScanner[T, In, P <: Poly] extends DepFn2[T, In]
  object RightScanner {
    type Aux[T, In, P <: Poly, Out] = RightScanner[T, In, P] :=> Out
    def apply[T, In, P <: Poly](implicit scan: RightScanner[T, In, P]): scan.type = scan

    implicit def scanner[T, L <: HList, In, P <: Poly, R <: HList](
      implicit gen: Generic.Aux[T, L],
      scanR: hl.RightScanner[L, In, P] :=> R,
      tp: hl.Tupler[R]
    ): RightScanner[T, In, P] :=> tp.Out = new RightScanner[T, In, P] {
      type Out = tp.Out
      def apply(t: T, in: In) = tp(scanR(gen.to(t), in))
    }
  }

  /**
   * Type class supporting producing a tuple of shape `N` filled with elements of type `A`.
   *
   * @author Alexandre Archambault
   */
  trait Fill[N, A] extends DepFn1[A]
  object Fill {
    type Aux[N, A, Out] = Fill[N, A] :=> Out
    def apply[N, A](implicit fill: Fill[N, A]): fill.type = fill

    implicit def fill1[N <: Nat, A, L <: HList, P](
      implicit
      fill: hlist.Fill[N, A] :=> L,
      tupler: hlist.Tupler[L]
    ): Fill[N, A] :=> tupler.Out = new Fill[N, A] {
      type Out = tupler.Out
      def apply(elem: A) = tupler(fill(elem))
    }

    implicit def fill2[A, N1 <: Nat, N2 <: Nat, SubOut](
      implicit
      subFill: Fill[N2, A] :=> SubOut,
      fill: Fill[N1, SubOut]
    ): Fill[(N1, N2), A] :=> fill.Out = new Fill[(N1, N2), A] {
      type Out = fill.Out
      def apply(elem: A) = fill(subFill(elem))
    }
  }

  /**
   * Type class supporting the patching of a tuple.
   *
   * @author Owein Reese
   */
  trait Patcher[N <: Nat, M <: Nat, T, InT] extends DepFn2[T, InT]
  object Patcher{
    def apply[N <: Nat, M <: Nat, T, InT](implicit patch: Patcher[N, M, T, InT]): patch.type = patch

    implicit def tuplePatch[N <: Nat, M <: Nat, T, L <: HList, InT, InL <: HList, OutL <: HList](
      implicit
      gen: Generic.Aux[T, L],
      genIn: Generic.Aux[InT, InL],
      patch: hl.Patcher[N, M, L, InL] :=> OutL,
      tp: hl.Tupler[OutL]
    ): Patcher[N, M, T, InT] :=> tp.Out = new Patcher[N, M, T, InT] {
      type Out = tp.Out
      def apply(t: T, in: InT) = tp(patch(gen.to(t), genIn.to(in)))
    }
  }

  /**
   * Typeclass supporting grouping this `Tuple` into tuples of `N` items each, at `Step`
   * apart. If `Step` equals `N` then the groups do not overlap.
   *
   * @author Andreas Koestler
   */
  trait Grouper[T, N <: Nat, Step <: Nat] extends DepFn1[T]
  object Grouper {
    type Aux[T, N <: Nat, Step <: Nat, Out] = Grouper[T, N, Step] :=> Out
    def apply[T, N <: Nat, Step <: Nat](implicit grouper: Grouper[T, N, Step]): grouper.type = grouper

    implicit def tupleGrouper[T, N <: Nat, Step <: Nat, L <: HList, OutL <: HList](
      implicit
      gen: Generic.Aux[T, L],
      grouper: hl.Grouper[L, N, Step] :=> OutL,
      tupler: hl.Tupler[OutL]
    ): Grouper[T, N, Step] :=> tupler.Out = new Grouper[T, N, Step] {
      type Out = tupler.Out
      def apply(t: T) = tupler(grouper(gen.to(t)))
    }
  }

  /**
   * Typeclass supporting grouping this `Tuple` into tuples of `N` items each, at `Step`
   * apart. If `Step` equals `N` then the groups do not overlap.
   *
   * Use the elements in `Pad` as necessary to complete last partition
   * up to `n` items. In case there are not enough padding elements, return a partition
   * with less than `n` items.
   *
   * @author Andreas Koestler
   */
  trait PaddedGrouper[T, N <: Nat, Step <: Nat, Pad] extends DepFn2[T, Pad]
  object PaddedGrouper {
    type Aux[T, N <: Nat, Step <: Nat, Pad, Out] = PaddedGrouper[T, N, Step, Pad] :=> Out
    def apply[T, N <: Nat, Step <: Nat, Pad](
      implicit grouper: PaddedGrouper[T, N, Step, Pad]
    ): grouper.type = grouper

    implicit def tuplePaddedGrouper[Pad, PadL <: HList, T, N <: Nat, Step <: Nat, L <: HList, OutL <: HList](
      implicit
      genL: Generic.Aux[T, L],
      genPad: Generic.Aux[Pad, PadL],
      grouper: hl.PaddedGrouper[L, N, Step, PadL] :=> OutL,
      tupler: hl.Tupler[OutL]
    ): PaddedGrouper[T, N, Step, Pad] :=> tupler.Out = new PaddedGrouper[T, N, Step, Pad] {
      type Out = tupler.Out
      def apply(t: T, pad: Pad) = tupler(grouper(genL.to(t), genPad.to(pad)))
    }
  }

  /**
   * Type class supporting permuting this `Tuple` into the same order as another `Tuple` with
   * the same element types.
   *
   * @author Peter Neyens
   */
  @implicitNotFound("Implicit not found: shapeless.ops.tuple.Align[${T}, ${U}]. The types ${T} and ${U} cannot be aligned.")
  trait Align[T, U] extends (T => U) with Serializable {
    def apply(t: T): U
  }

  object Align {
    def apply[T, U](implicit align: Align[T, U]): align.type = align

    implicit def tupleAlign[T, U, L <: HList, M <: HList](
      implicit
      gent: Generic.Aux[T, L],
      genu: Generic.Aux[U, M],
      align: hl.Align[L, M],
      tp: hl.Tupler[M] :=> U
    ): Align[T, U] = t =>
      align(gent.to(t)).tupled
  }
}