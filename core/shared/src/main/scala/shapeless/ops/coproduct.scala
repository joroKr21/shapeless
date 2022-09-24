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

import poly._

import annotation.implicitNotFound

object coproduct {

  /** Type class for converting a value of type I into the coproduct C. (Type I need to occur in the coproduct C) */
  trait Inject[C <: Coproduct, I] extends Serializable {
    def apply(i: I): C
  }

  object Inject {
    def apply[C <: Coproduct, I](implicit inject: Inject[C, I]): inject.type = inject

    implicit def tlInject[H, T <: Coproduct, I](implicit tlInj: Inject[T, I]): Inject[H :+: T, I] =
      i => Inr(tlInj(i))
    implicit def hdInject[H, HH <: H, T <: Coproduct]: Inject[H :+: T, HH] =
      Inl(_)
  }

  /**
    * Type class for attempting to get a value of type T out of an instance of corpdocut C.
    * If the coproduct instance is not of the specified type, None is returned
    */
  trait Selector[C <: Coproduct, T] extends Serializable {
    def apply(c: C): Option[T]
  }

  object Selector {
    def apply[C <: Coproduct, T](implicit select: Selector[C, T]): select.type = select

    implicit def hdSelector[H, T <: Coproduct]: Selector[H :+: T, H] = {
      case Inl(h) => Some(h)
      case Inr(t) => None
    }

    implicit def tlSelector[H, T <: Coproduct, S](implicit st: Selector[T, S]): Selector[H :+: T, S] = {
      case Inl(h) => None
      case Inr(t) => st(t)
    }
  }

  /** Type class supporting getting the Nth type from a coproduct C. */
  trait At[C <: Coproduct, N <: Nat] extends DepFn1[C] {
    type A
    type Out = Option[A]
  }

  object At {
    type Aux[C <: Coproduct, N <: Nat, A0] = At[C, N] { type A = A0 }
    def apply[C <: Coproduct, N <: Nat](implicit at: At[C, N]): at.type = at

    implicit def coproductAt0[H, T <: Coproduct]: Aux[H :+: T, Nat._0, H] =
      new At[H :+: T, Nat._0] {
        type A = H
        def apply(c: H :+: T) = c match {
          case Inl(h) => Some(h)
          case _      => None
        }
      }

    implicit def coproductAtN[H, T <: Coproduct, N <: Nat](
      implicit att: At[T, N]
    ): Aux[H :+: T, Succ[N], att.A] = new At[H :+: T, Succ[N]] {
      type A = att.A
      def apply(c: H :+: T) = c match {
        case Inl(_)    => None
        case Inr(tail) => att(tail)
      }
    }
  }

  /** find index of A in C */
  trait IndexOf[C <: Coproduct, A] extends DepFn0 {
    type Out <: Nat
    def value(implicit n: ops.nat.ToInt[Out]): Int = n.apply()
  }

  object IndexOf {
    type Aux[C <: Coproduct, A, R <: Nat] = IndexOf[C, A] :=> R
    def apply[C <: Coproduct, A](implicit index: IndexOf[C, A]): index.type = index

    implicit def matched[C <: Coproduct, A]: IndexOf[A :+: C, A] :=> Nat._0 =
      new IndexOf[A :+: C, A] {
        type Out = Nat._0
        def apply() = Nat._0
      }

    implicit def notMatched[C <: Coproduct, A, H, Next <: Nat](
      implicit ev: A =:!= H,
      next: IndexOf[C, A] :=> Next,
      n: Witness.Aux[Succ[Next]]
    ): IndexOf[H :+: C, A] :=> Succ[Next] = new IndexOf[H :+: C, A] {
      type Out = Succ[Next]
      def apply() = n.value
    }
  }

  /**
    * Type class for filtering coproduct by type U, splitting into a coproduct containing only type U and
    * a coproduct of all other types.
    */
  trait Partition[C <: Coproduct, U] extends DepFn1[C] {
    type Prefix <: Coproduct
    type Suffix <: Coproduct
    type Out = Either[Prefix, Suffix]

    def filter(c: C): Option[Prefix] = apply(c).swap.toOption
    def filterNot(c: C): Option[Suffix] = apply(c).toOption
    def apply(c: C): Out = toEither(coproduct(c))
    def coproduct(c: C): Prefix :+: Suffix :+: CNil
  }

  object Partition {
    def apply[C <: Coproduct, U](implicit partition: Partition[C, U]): partition.type = partition

    type Aux[C <: Coproduct, U, Pre <: Coproduct, Suf <: Coproduct] = Partition[C, U] {
      type Prefix = Pre
      type Suffix = Suf
    }

    implicit def cnilPartition[U]: Aux[CNil, U, CNil, CNil] = new Partition[CNil, U] {
      type Prefix = CNil
      type Suffix = CNil
      def coproduct(c: CNil) = Inr(Inr(c))
    }

    implicit def coproductPartition_Match[H, T <: Coproduct, TPrefix <: Coproduct, TSuffix <: Coproduct](
      implicit partition: Aux[T, H, TPrefix, TSuffix]
    ): Aux[H :+: T, H, H :+: TPrefix, TSuffix] = new Partition[H :+: T, H] {
      type Prefix = H :+: TPrefix
      type Suffix = TSuffix
      def coproduct(c: H :+: T) = c match {
        case Inl(h) => Inl(Inl(h))
        case Inr(t) => partition.coproduct(t) match {
          case Inl(h) => Inl(Inr(h))
          case Inr(t) => Inr(t)
        }
      }
    }

    implicit def coproductPartition_NonMatch[H, T <: Coproduct, TPrefix <: Coproduct, TSuffix <: Coproduct, U](
      implicit partition: Aux[T, U, TPrefix, TSuffix], e: U =:!= H
    ): Aux[H :+: T, U, TPrefix, H :+: TSuffix] = new Partition[H :+: T, U] {
      type Prefix = TPrefix
      type Suffix = H :+: TSuffix
      def coproduct(c: H :+: T) = c match {
        case Inl(h) => Inr(Inl(Inl(h)))
        case Inr(t) => partition.coproduct(t) match {
          case Inl(h)      => Inl(h)
          case Inr(Inl(t)) => Inr(Inl(Inr(t)))
          case Inr(Inr(c)) => Inr(Inr(c))
        }
      }
    }
  }

  /**
    * Type class which filters a coproduct by a type U, producing a coproduct containing only U.
    * (The output is a coproduct because type U may occur multiple times in the original coproduct)
    */
  trait Filter[C <: Coproduct, U] extends DepFn1[C] {
    type A <: Coproduct
    type Out = Option[A]
  }

  object Filter {
    type Aux[C <: Coproduct, U, A0 <: Coproduct] = Filter[C, U] { type A = A0 }
    def apply[C <: Coproduct, U](implicit filter: Filter[C, U]): filter.type = filter

    implicit def coproductFilter[C <: Coproduct, U, CPrefix <: Coproduct, CSuffix <: Coproduct](
      implicit partition: Partition.Aux[C, U, CPrefix, CSuffix]
    ): Aux[C, U, CPrefix] = new Filter[C, U] {
      type A = CPrefix
      def apply(c: C) = partition.filter(c)
    }
  }

  /**
    * Type class which filters a coproduct by a type U, producing a coproduct that does not contain U
    * If U does not exist in the coproduct, the original coproduct is returned
    */
  trait FilterNot[C <: Coproduct, U] extends DepFn1[C] {
    type A <: Coproduct
    type Out = Option[A]
  }

  object FilterNot {
    type Aux[C <: Coproduct, U, A0 <: Coproduct] = FilterNot[C, U] { type A = A0 }
    def apply[C <: Coproduct, U](implicit filterNot: FilterNot[C, U]): filterNot.type = filterNot

    implicit def coproductFilterNot[C <: Coproduct, U, CPrefix <: Coproduct, CSuffix <: Coproduct](
      implicit partition: Partition.Aux[C, U, CPrefix, CSuffix]
    ): Aux[C, U, CSuffix] = new FilterNot[C, U] {
      type A = CSuffix
      def apply(c: C) = partition.filterNot(c)
    }
  }

  /**
    * Type class that can removes the first occurrence of a particular type from a coproduct, splitting it into the
    * specified type U and a coproduct representing the rest of the coproduct (with first occurrence of U removed).
    * Also provides the `inverse` method which allows for reconstructing the original coproduct from its subparts.
    */
  trait Remove[C <: Coproduct, U] extends DepFn1[C] {
    type Rest <: Coproduct
    type Out = Either[U, Rest]

    def inverse(r: Either[U, Rest]): C
    def coproduct(c: C): U :+: Rest = apply(c) match {
      case Left(u) => Inl(u)
      case Right(r) => Inr(r)
    }
  }

  trait LowPriorityRemove {
    type Aux[C <: Coproduct, U, R <: Coproduct] = Remove[C, U] { type Rest = R }

    // Must be given a lower priority than removeHead, so that:
    // - the two don't collide for coproducts with repeated types
    // - the first element of type I in C is removed
    implicit def removeTail[H, T <: Coproduct, U, R <: Coproduct](implicit
      tailRemove: Remove.Aux[T, U, R]
    ): Aux[H :+: T, U, H :+: R] = new Remove[H :+: T, U] {
      type Rest = H :+: R

      def apply(c: H :+: T) = c match {
        case Inl(h) => Right(Inl(h))
        case Inr(t) => tailRemove(t) match {
          case Left(i)  => Left(i)
          case Right(r) => Right(Inr(r))
        }
      }

      def inverse(r: Either[U, H :+: R]) = r match {
        case Left(i)       => Inr(tailRemove.inverse(Left(i)))
        case Right(Inl(h)) => Inl(h)
        case Right(Inr(t)) => Inr(tailRemove.inverse(Right(t)))
      }
    }
  }

  object Remove extends LowPriorityRemove {
    def apply[C <: Coproduct, U](implicit remove: Remove[C, U]): remove.type = remove

    implicit def removeHead[H, T <: Coproduct]: Aux[H :+: T, H, T] = new Remove[H :+: T, H] {
      type Rest = T

      def apply(c: H :+: T) = c match {
        case Inl(h) => Left(h)
        case Inr(t) => Right(t)
      }

      def inverse(r: Either[H, T]) = r match {
        case Left(h)  => Inl(h)
        case Right(t) => Inr(t)
      }
    }
  }

  /** Type class similar to [[Remove]], but removes the last occurance of the specified type (I) instead */
  trait RemoveLast[C <: Coproduct, I] extends DepFn1[C] {
    type Rest <: Coproduct
    type Out = Either[I, Rest]
    def inverse(r: Either[I, Rest]): C
  }

  trait LowPriorityRemoveLast {
    type Aux[C <: Coproduct, I, R <: Coproduct] = RemoveLast[C, I] { type Rest = R }

    protected def fromRemove[C <: Coproduct, I](remove: Remove[C, I]): Aux[C, I, remove.Rest] =
      new RemoveLast[C, I] {
        type Rest = remove.Rest
        def apply(c: C) = remove(c)
        def inverse(r: Either[I, Rest]) = remove.inverse(r)
      }

    protected def toRemove[C <: Coproduct, I](removeLast: RemoveLast[C, I]): Remove.Aux[C, I, removeLast.Rest] =
      new Remove[C, I] {
        type Rest = removeLast.Rest
        def apply(c: C) = removeLast(c)
        def inverse(r: Either[I, Rest]) = removeLast.inverse(r)
      }

    // Must be given a lower priority than removeLastTail, so that:
    // - the two don't collide for coproducts with repeated types
    // - the last element of type I in C is removed
    implicit def removeLastHead[H, T <: Coproduct]: Aux[H :+: T, H, T] =
      fromRemove(Remove.removeHead[H, T])
  }

  object RemoveLast extends LowPriorityRemoveLast {
    def apply[C <: Coproduct, I](implicit remove: RemoveLast[C, I]): remove.type = remove

    implicit def removeLastTail[H, T <: Coproduct, I, R <: Coproduct](
      implicit tailRemoveLast: RemoveLast.Aux[T, I, R]
    ): Aux[H :+: T, I, H :+: R] =
      fromRemove(Remove.removeTail(toRemove(tailRemoveLast)))
  }

  /**
    * For each type in the coproduct run a function (provide in Poly) which produces some coproduct, then flatten all
    * the resulting coproducts. This is conceptually similar to List#flatMap with the list items being types
    */
  trait FlatMap[C <: Coproduct, F <: Poly] extends DepFn1[C] {
    type Out <: Coproduct
  }

  object FlatMap {
    type Aux[C <: Coproduct, F <: Poly, Out <: Coproduct] = FlatMap[C, F] :=> Out
    def apply[C <: Coproduct, F <: Poly](implicit flatMap: FlatMap[C, F]): flatMap.type = flatMap

    implicit def cnilFlatMap[F <: Poly]: FlatMap[CNil, F] :=> CNil =
      new FlatMap[CNil, F] {
        type Out = CNil
        def apply(c: CNil) = c
      }

    implicit def cpFlatMap[H, T <: Coproduct, F <: Poly, OutH <: Coproduct, OutT <: Coproduct](
      implicit
      fh: Case1[F, H] @=> OutH,
      ft: FlatMap[T, F] :=> OutT,
      extendBy: ExtendBy[OutH, OutT]
    ): FlatMap[H :+: T, F] :=> extendBy.Out =
      new FlatMap[H :+: T, F] {
        type Out = extendBy.Out
        def apply(c: H :+: T) = c match {
          case Inl(h) => extendBy.right(fh(h))
          case Inr(t) => extendBy.left(ft(t))
        }
    }
  }

  /** For each type in a coproduct, map it to another type. Conceptually similar to List#map */
  trait Mapper[F <: Poly, C <: Coproduct] extends DepFn1[C] {
    type Out <: Coproduct
  }

  object Mapper {
    type Aux[F <: Poly, C <: Coproduct, Out <: Coproduct] = Mapper[F, C] :=> Out
    def apply[F <: Poly, C <: Coproduct](implicit mapper: Mapper[F, C]): mapper.type = mapper
    def apply[C <: Coproduct](f: Poly)(implicit mapper: Mapper[f.type, C]): mapper.type = mapper

    implicit def cnilMapper[F <: Poly]: Mapper[F, CNil] :=> CNil =
      new Mapper[F, CNil] {
        type Out = CNil
        def apply(t: CNil) = t
      }

    implicit def cpMapper[F <: Poly, H, OutH, T <: Coproduct, OutT <: Coproduct](
      implicit
      fh: Case1[F, H] @=> OutH,
      mt: Mapper[F, T] :=> OutT
    ): Mapper[F, H :+: T] :=> (OutH :+: OutT) =
      new Mapper[F, H :+: T] {
        type Out = OutH :+: OutT
        def apply(c: H :+: T) = c match {
          case Inl(h) => Inl(fh(h))
          case Inr(t) => Inr(mt(t))
        }
      }
  }

  /**
    * Type class that unifies all the types in a coproduct into one single type which is their closest common parent type
    * (i.e. least upper bound of all the types in the coproduct)
    */
  trait Unifier[C <: Coproduct] extends DepFn1[C]
  object Unifier {
    type Aux[C <: Coproduct, Out] = Unifier[C] :=> Out
    def apply[C <: Coproduct](implicit unifier: Unifier[C]): unifier.type = unifier

    implicit def lstUnifier[H]: Unifier[H :+: CNil] :=> H =
      new Unifier[H :+: CNil] {
        type Out = H
        def apply(c: H :+: CNil) = c match {
          case Inl(h) => h
          case Inr(_) => unexpected
        }
      }

    implicit def cpUnifier[H1, H2, T <: Coproduct, L, O](
      implicit
      lt: Unifier[H2 :+: T] :=> L,
      u: Lub[H1, L, O]
    ): Unifier[H1 :+: H2 :+: T] :=> O =
      new Unifier[H1 :+: H2 :+: T] {
        type Out = O
        def apply(c: H1 :+: H2 :+: T) = c match {
          case Inl(h1) => u.left(h1)
          case Inr(t) => u.right(lt(t))
        }
      }
  }

  /** Type class folding all possible types of a coproduct down to a single type */
  trait Folder[F <: Poly, C <: Coproduct] extends DepFn1[C]
  object Folder {
    type Aux[F <: Poly, C <: Coproduct, Out] = Folder[F, C] :=> Out
    def apply[F <: Poly, C <: Coproduct](implicit folder: Folder[F, C]): folder.type = folder
    def apply[C <: Coproduct](f: Poly)(implicit folder: Folder[f.type, C]): folder.type = folder

    implicit def mkFolder[F <: Poly, C <: Coproduct, M <: Coproduct, O](
      implicit
      mapper: Mapper[F, C] :=> M,
      unifier: Unifier[M] :=> O
    ): Folder[F, C] :=> O =
      new Folder[F, C] {
        type Out = O
        def apply(c: C) = unifier(mapper(c))
      }
  }

  /** Type class which performs left fold on a coproduct. Provided with a dependent function that can convert
    * all types in a coproduct into the same type as the initial value of type In, combines the actual value
    * of the coproduct with the initial value */
  trait LeftFolder[C <: Coproduct, In, F] extends DepFn2[C,In]
  object LeftFolder {
    type Aux[C <: Coproduct, In, HF, Out] = LeftFolder[C, In, HF] :=> Out
    def apply[C <: Coproduct, In, F](implicit folder: LeftFolder[C, In, F]): folder.type = folder

    implicit def hdLeftFolder[H, In, F](
      implicit f: Case2[F, In, H] @=> In
    ): LeftFolder[H :+: CNil, In, F] :=> In =
      new LeftFolder[H :+: CNil, In, F] {
        type Out = In
        def apply(c: H :+: CNil, in: In) = f(in,c.head.get)
      }

    implicit def tlLeftFolder[H, T <: Coproduct, In, HF, OutH](
      implicit
      f: Case2[HF, In, H] @=> OutH,
      ft: LeftFolder[T, In, HF] :=> OutH
    ): LeftFolder[H :+: T, In, HF] :=> OutH =
      new LeftFolder[H :+: T, In, HF] {
        type Out = OutH
        def apply(c: H :+: T, in: In) = c match {
          case Inl(h) => f(in, h)
          case Inr(t) => ft(t, in)
        }
      }
  }

  /**
   * Type class supporting zipping this `Coproduct` with a constant of type `Z` returning a `Coproduct` of tuples of the form
   * ({element from input `Coproduct`}, {supplied constant})
   *
   * @author William Harvey
   */
  trait ZipConst[Z, V <: Coproduct] extends DepFn2[Z, V] {
    type Out <: Coproduct
  }

  object ZipConst {
    type Aux[Z, V <: Coproduct, Out <: Coproduct] = ZipConst[Z, V] :=> Out
    def apply[Z, V <: Coproduct](implicit zipConst: ZipConst[Z, V]): zipConst.type = zipConst

    implicit def cnilZipConst[Z]: ZipConst[Z, CNil] :=> CNil =
      new ZipConst[Z, CNil] {
        type Out = CNil
        def apply(z: Z, v: CNil) = v
      }

    implicit def cpZipConst[Z, VH, VT <: Coproduct, OutT <: Coproduct](
      implicit zipConst: ZipConst[Z, VT] :=> OutT
    ): ZipConst[Z, VH :+: VT] :=> ((VH, Z) :+: OutT) =
      new ZipConst[Z, VH :+: VT] {
        type Out = (VH, Z) :+: OutT
        def apply(z: Z, v: VH :+: VT) = v match {
          case Inl(vh) => Inl((vh, z))
          case Inr(vt) => Inr(zipConst(z, vt))
        }
      }
  }

  /** Type class that zips an HList with a Coproduct, producing a Coproduct of tuples where each element from
    * the original coproduct is combined with the matching HList element
    */
  sealed abstract class ZipWithKeys[K <: HList, V <: Coproduct] extends DepFn1[V] {
    type Out <: Coproduct
  }

  object ZipWithKeys {
    import shapeless.labelled._

    private val instance = new ZipWithKeys[HList, Coproduct] {
      type Out = Coproduct
      def apply(v: Coproduct) = v
    }

    type Aux[K <: HList, V <: Coproduct, Out <: Coproduct] = ZipWithKeys[K, V] :=> Out
    def apply[K <: HList, V <: Coproduct](implicit zip: ZipWithKeys[K, V]): zip.type = zip

    implicit def cnilZipWithKeys: ZipWithKeys[HNil, CNil] :=> CNil =
      instance.asInstanceOf[ZipWithKeys[HNil, CNil] :=> CNil]

    implicit def cconsZipWithKeys[KH, VH, KT <: HList, VT <: Coproduct, OutT <: Coproduct](
      implicit
      wkh: Witness.Aux[KH],
      zipWithKeys: ZipWithKeys[KT, VT] :=> OutT
    ): ZipWithKeys[KH :: KT, VH :+: VT] :=> (FieldType[KH, VH] :+: OutT) =
      instance.asInstanceOf[ZipWithKeys[KH :: KT, VH :+: VT] :=> (FieldType[KH, VH] :+: OutT)]
  }

  /**
   * Type class supporting zipping a `Coproduct` with its element indices, resulting in a `Coproduct` of tuples of the form
   * ({element from input tuple}, {element index})
   *
   * @author Andreas Koestler
   */
  trait ZipWithIndex[C <: Coproduct] extends DepFn1[C] {
    type Out <: Coproduct
  }

  object ZipWithIndex {
    import shapeless.Nat._

    type Aux[C <: Coproduct, Out <: Coproduct] = ZipWithIndex[C] :=> Out
    def apply[C <: Coproduct](implicit zip: ZipWithIndex[C]): zip.type = zip

    implicit def cpZipWithIndex[C <: Coproduct](
      implicit impl: Impl[C, _0]
    ): ZipWithIndex[C] :=> impl.Out =
      new ZipWithIndex[C] {
        type Out = impl.Out
        def apply(c: C) = impl(c)
      }

    trait Impl[C <: Coproduct, N <: Nat] extends DepFn1[C] {
      type Out <: Coproduct
    }

    object Impl {
      type Aux[C <: Coproduct, N <: Nat, Out <: Coproduct] = Impl[C, N] :=> Out
      def apply[C <: Coproduct, N <: Nat](implicit impl: Impl[C, N]): impl.type = impl

      implicit def singleZipWithIndexImpl[CH, N <: Nat](
        implicit w: Witness.Aux[N]
      ): Impl[CH :+: CNil, N] :=> ((CH, N) :+: CNil) =
        new Impl[CH :+: CNil, N] {
          type Out = (CH, N) :+: CNil
          def apply(c: CH :+: CNil) = Coproduct[Out]((c.head.get, w.value))
        }

      implicit def cpZipWithIndexImpl[CH, CT <: Coproduct, N <: Nat, OutC <: Coproduct](
        implicit
        impl: Impl[CT, Succ[N]] :=> OutC,
        w: Witness.Aux[N]
      ): Impl[CH :+: CT, N] :=> ((CH, N) :+: OutC) =
        new Impl[CH :+: CT, N] {
          type Out = (CH, N) :+: OutC
          def apply(c: CH :+: CT) = c match {
            case Inl(h) => Inl((h, w.value))
            case Inr(t) => Inr(impl(t))
          }
        }
    }

  }

  /**
   * Type class supporting zipping a `Coproduct` with an `HList`, resulting in a `Coproduct` of tuples of the form
   * ({element from input `Coproduct`}, {element from input `HList`})
   *
   * @author William Harvey
   */
  trait ZipWith[H <: HList, V <: Coproduct] extends DepFn2[H, V] {
    type Out <: Coproduct
  }

  object ZipWith {
    type Aux[H <: HList, V <: Coproduct, Out <: Coproduct] = ZipWith[H, V] :=> Out
    def apply[H <: HList, V <: Coproduct](implicit zip: ZipWith[H, V]): zip.type = zip

    implicit def cnilZipWith: ZipWith[HNil, CNil] :=> CNil =
      new ZipWith[HNil, CNil] {
        type Out = CNil
        def apply(h: HNil, v: CNil) = v
      }

    implicit def cpZipWith[HH, HT <: HList, VH, VT <: Coproduct, OutT <: Coproduct](
      implicit zipWith: ZipWith[HT, VT] :=> OutT
    ): ZipWith[HH :: HT, VH :+: VT] :=> ((VH, HH) :+: OutT) =
      new ZipWith[HH :: HT, VH :+: VT] {
        type Out = (VH, HH) :+: OutT
        def apply(h: HH :: HT, v: VH :+: VT) = v match {
          case Inl(vh) => Inl((vh, h.head))
          case Inr(vt) => Inr(zipWith(h.tail, vt))
        }
      }
  }

  /**
   * Type class supporting computing the type-level Nat corresponding to the length of this `Coproduct`.
   *
   * @author Stacy Curl
   */
  trait Length[C <: Coproduct] extends DepFn0 {
    type Out <: Nat
  }

  object Length {
    type Aux[C <: Coproduct, Out <: Nat] = Length[C] :=> Out
    def apply[C <: Coproduct](implicit length: Length[C]): length.type = length

    implicit def cnilLength: Length[CNil] :=> Nat._0 =
      new Length[CNil] {
        type Out = Nat._0
        def apply() = Nat._0
      }

    implicit def coproductLength[H, T <: Coproduct, N <: Nat](
      implicit
      lt: Length[T] :=> N,
      sn: Witness.Aux[Succ[N]]
    ): Length[H :+: T] :=> Succ[N] =
      new Length[H :+: T] {
        type Out = Succ[N]
        def apply() = sn.value
      }
  }

  /**
   * Type class supporting extending a coproduct on the right
   *
   * @author Stacy Curl
   */
  trait ExtendRight[C <: Coproduct, T] extends DepFn1[C] {
    type Out <: Coproduct
  }

  object ExtendRight {
    type Aux[C <: Coproduct, T, Out <: Coproduct] = ExtendRight[C, T] :=> Out
    def apply[C <: Coproduct, T](implicit extend: ExtendRight[C, T]): extend.type = extend

    implicit def extendRightSingleton[H, A]: ExtendRight[H :+: CNil, A] :=> (H :+: A :+: CNil) =
      new ExtendRight[H :+: CNil, A] {
        type Out = H :+: A :+: CNil
        def apply(c: H :+: CNil) = c match {
          case Inl(h) => Inl(h)
          case Inr(t) => Inr(Inr(t))
        }
      }

    implicit def extendRightCoproduct[H, T <: Coproduct, A, AT <: Coproduct](
      implicit extendRight: ExtendRight[T, A] :=> AT
    ): ExtendRight[H :+: T, A] :=> (H :+: AT) =
      new ExtendRight[H :+: T, A] {
        type Out = H :+: AT
        def apply(c: H :+: T) = c match {
          case Inl(h) => Inl(h)
          case Inr(t) => Inr(extendRight(t))
        }
      }
  }

  /**
    * Type class which combines the functionality of [[ExtendRightBy]] and [[ExtendLeftBy]]. The combined coproduct
    * and be produced by either providing the left part or the right part.
    * */
  trait ExtendBy[L <: Coproduct, R <: Coproduct] extends DepFn {
    type Out <: Coproduct
    def right(l: L): Out
    def left(r: R): Out
  }

  object ExtendBy {
    type Aux[L <: Coproduct, R <: Coproduct, Out <: Coproduct] = ExtendBy[L, R] :=> Out
    def apply[L <: Coproduct, R <: Coproduct](implicit extend: ExtendBy[L, R]): extend.type = extend

    implicit def extendBy[L <: Coproduct, R <: Coproduct, O <: Coproduct](
      implicit
      extendLeftBy: ExtendLeftBy[L, R] :=> O,
      extendRightBy: ExtendRightBy[L, R] :=> O
    ): ExtendBy[L, R] :=> O = new ExtendBy[L, R] {
      type Out = O
      def right(l: L): Out = extendRightBy(l)
      def left(r: R): Out = extendLeftBy(r)
    }
  }

  /** Extend a coproduct to the left by another coproduct. Conceptually similar to prepending a List to the original List */
  trait ExtendLeftBy[L <: Coproduct, R <: Coproduct] extends DepFn1[R] {
    type Out <: Coproduct
  }

  object ExtendLeftBy {
    type Aux[L <: Coproduct, R <: Coproduct, Out <: Coproduct] = ExtendLeftBy[L, R] :=> Out
    def apply[L <: Coproduct, R <: Coproduct](implicit extend: ExtendLeftBy[L, R]): extend.type = extend

    implicit def extendLeftByCoproduct[L <: Coproduct, R <: Coproduct, RevL <: Coproduct](
      implicit
      reverseL: Reverse[L] :=> RevL,
      impl: Impl[RevL, R]
    ): ExtendLeftBy[L, R] :=> impl.Out = new ExtendLeftBy[L, R] {
      type Out = impl.Out
      def apply(r: R) = impl(r)
    }

    trait Impl[RevL <: Coproduct, R <: Coproduct] extends DepFn1[R] {
      type Out <: Coproduct
    }

    object Impl {
      type Aux[RevL <: Coproduct, R <: Coproduct, Out <: Coproduct] = Impl[RevL, R] :=> Out

      implicit def extendLeftByCNilImpl[R <: Coproduct]: Impl[CNil, R] :=> R = new Impl[CNil, R] {
        type Out = R
        def apply(r: R) = r
      }

      implicit def extendLeftByCoproductImpl[H, T <: Coproduct, R <: Coproduct](
        implicit extendLeftBy: Impl[T, H :+: R]
      ): Impl[H :+: T, R] :=> extendLeftBy.Out = new Impl[H :+: T, R] {
        type Out = extendLeftBy.Out
        def apply(r: R) = extendLeftBy(Inr[H, R](r))
      }
    }
  }

  /** Similar to [[ExtendLeftBy]]. Conceptually similar to appending a List to the original List */
  trait ExtendRightBy[L <: Coproduct, R <: Coproduct] extends DepFn1[L] {
    type Out <: Coproduct
  }

  object ExtendRightBy {
    type Aux[L <: Coproduct, R <: Coproduct, Out <: Coproduct] = ExtendRightBy[L, R] :=> Out
    def apply[L <: Coproduct, R <: Coproduct](implicit extend: ExtendRightBy[L, R]): extend.type = extend

    implicit def extendRightByCNil[L <: Coproduct]: ExtendRightBy[L, CNil] :=> L =
      new ExtendRightBy[L, CNil] {
        type Out = L
        def apply(l: L) = l
      }

    implicit def extendRightByCoproduct[L <: Coproduct, H, LH <: Coproduct, T <: Coproduct](
      implicit
      extendRight: ExtendRight[L, H] :=> LH,
      extendRightBy: ExtendRightBy[LH, T]
    ): ExtendRightBy[L, H :+: T] :=> extendRightBy.Out = new ExtendRightBy[L, H :+: T] {
      type Out = extendRightBy.Out
      def apply(l: L) = extendRightBy(extendRight(l))
    }
  }

  /**
   * Type class supporting rotating a Coproduct left
   *
   * @author Stacy Curl
   * @author Alexandre Archambault
   */
  trait RotateLeft[C <: Coproduct, N <: Nat] extends DepFn1[C] {
    type Out <: Coproduct
  }

  object RotateLeft extends LowPriorityRotateLeft {
    type Aux[C <: Coproduct, N <: Nat, Out] = RotateLeft[C, N] :=> Out
    def apply[C <: Coproduct, N <: Nat](implicit rotate: RotateLeft[C, N]): rotate.type = rotate

    implicit def cnilRotateLeft[N <: Nat]: RotateLeft[CNil, N] :=> CNil =
      new RotateLeft[CNil, N] {
        type Out = CNil
        def apply(c: CNil) = c
      }
  }

  trait LowPriorityRotateLeft {
    implicit def coproductRotateLeft[
      C <: Coproduct,
      N <: Nat,
      Size <: Nat,
      NModSize <: Nat,
      Before <: Coproduct,
      After <: Coproduct
    ](implicit
      length: Length[C] :=> Size,
      mod: nat.Mod[N, Size] :=> NModSize,
      split: Split.Aux[C, NModSize, Before, After],
      prepend: Prepend[After, Before]
    ): RotateLeft[C, N] :=> prepend.Out =
      new RotateLeft[C, N] {
        type Out = prepend.Out
        def apply(c: C) = prepend(split(c).swap)
      }
  }

  /**
   * Type class supporting rotating a Coproduct right
   *
   * @author Stacy Curl
   * @author Alexandre Archambault
   */
  trait RotateRight[C <: Coproduct, N <: Nat] extends DepFn1[C] {
    type Out <: Coproduct
  }

  object RotateRight extends LowPriorityRotateRight {
    def apply[C <: Coproduct, N <: Nat](implicit rotate: RotateRight[C, N]): rotate.type = rotate

    implicit def cnilRotateRight[N <: Nat]: RotateRight[CNil, N] :=> CNil =
      new RotateRight[CNil, N] {
        type Out = CNil
        def apply(c: CNil) = c
      }
  }

  trait LowPriorityRotateRight {
    type Aux[C <: Coproduct, N <: Nat, Out <: Coproduct] = RotateRight[C, N] :=> Out

    implicit def coproductRotateRight[
      C <: Coproduct,
      N <: Nat,
      Size <: Nat,
      NModSize <: Nat,
      Size_Diff_NModSize <: Nat
    ](implicit
      length: Length[C] :=> Size,
      mod: nat.Mod[N, Size] :=> NModSize,
      diff: nat.Diff[Size, NModSize] :=> Size_Diff_NModSize,
      rotateLeft: RotateLeft[C, Size_Diff_NModSize]
    ): RotateRight[C, N] :=> rotateLeft.Out =
      new RotateRight[C, N] {
        type Out = rotateLeft.Out
        def apply(c: C) = rotateLeft(c)
      }
  }

  /**
   * Type class providing access to head and tail of a Coproduct
   *
   * @author Stacy Curl
   */
  trait IsCCons[C <: Coproduct] extends Serializable {
    type H
    type T <: Coproduct

    def head(c: C): Option[H]
    def tail(c: C): Option[T]
    def cons(e: Either[H, T]): C
  }

  object IsCCons {
    type Aux[C <: Coproduct, H0, T0 <: Coproduct] = IsCCons[C] { type H = H0; type T = T0 }
    def apply[C <: Coproduct](implicit isCCons: IsCCons[C]): isCCons.type = isCCons

    implicit def coproductCCons[H0, T0 <: Coproduct]: Aux[H0 :+: T0, H0, T0] = new IsCCons[H0 :+: T0] {
      type H = H0
      type T = T0

      def head(c: H0 :+: T0) = c match {
        case Inl(h) => Some(h)
        case _      => None
      }

      def tail(c: H0 :+: T0) = c match {
        case Inr(t) => Some(t)
        case _      => None
      }

      def cons(e: Either[H0, T0]) = e match {
        case Left(h) => Inl(h)
        case Right(t) => Inr(t)
      }
    }
  }
  /**
   * Type class supporting splitting this `Coproduct` at the ''nth'' element returning prefix and suffix as a coproduct
   *
   * @author Stacy Curl, Alexandre Archambault
   */
  trait Split[C <: Coproduct, N <: Nat] extends DepFn1[C] {
    type Left <: Coproduct
    type Right <: Coproduct
    type Out = Either[Left, Right]

    def coproduct(c: C): Left :+: Right :+: CNil = apply(c) match {
      case Left(l) => Inl(l)
      case Right(r) => Inr(Inl(r))
    }
  }

  object Split {
    def apply[C <: Coproduct, N <: Nat](implicit split: Split[C, N]): split.type = split
    type Aux[C <: Coproduct, N <: Nat, L <: Coproduct, R <: Coproduct] =
      Split[C, N] { type Left = L; type Right = R }

    implicit def splitZero[C <: Coproduct]: Aux[C, Nat._0, CNil, C] =
      new Split[C, Nat._0] {
        type Left = CNil
        type Right = C
        def apply(c: C) = Right(c)
      }

    implicit def splitSucc[H, T <: Coproduct, N <: Nat](
      implicit tail: Split[T, N]
    ): Aux[H :+: T, Succ[N], H :+: tail.Left, tail.Right] =
      new Split[H :+: T, Succ[N]] {
        type Left  = H :+: tail.Left
        type Right = tail.Right
        def apply(c: H :+: T) = c match {
          case Inl(h) => Left(Inl(h))
          case Inr(t) => tail(t) match {
            case Left(l)  => Left(Inr(l))
            case Right(r) => Right(r)
          }
        }
      }
  }

  /**
   * Type class supporting taking the first `n`-elements of this `Coproduct`
   *
   * @author Alexandre Archambault
   */
  trait Take[C <: Coproduct, N <: Nat] extends DepFn1[C] {
    type Taken <: Coproduct
    type Out = Option[Taken]
  }

  object Take {
    type Aux[C <: Coproduct, N <: Nat, L <: Coproduct] = Take[C, N] { type Taken = L }
    def apply[C <: Coproduct, N <: Nat](implicit take: Take[C, N]): take.type = take

    implicit def takeZero[C <: Coproduct]: Aux[C, Nat._0, CNil] =
      new Take[C, Nat._0] {
        type Taken = CNil
        def apply(c: C) = None
      }

    implicit def takeSucc[H, T <: Coproduct, N <: Nat](
      implicit tail: Take[T, N]
    ): Aux[H :+: T, Succ[N], H :+: tail.Taken] =
      new Take[H :+: T, Succ[N]] {
        type Taken = H :+: tail.Taken
        def apply(c: H :+: T) = c match {
          case Inl(h) => Some(Coproduct[H :+: tail.Taken](h))
          case Inr(t) => tail(t).map(Inr[H, tail.Taken](_))
        }
      }
  }

  /**
   * Type class supporting dropping the first `n`-elements of this `Coproduct`
   *
   * @author Alexandre Archambault
   */
  trait Drop[C <: Coproduct, N <: Nat] extends DepFn1[C] {
    type Remaining <: Coproduct
    type Out = Option[Remaining]
  }

  object Drop {
    type Aux[C <: Coproduct, N <: Nat, L <: Coproduct] = Drop[C, N] { type Remaining = L }
    def apply[C <: Coproduct, N <: Nat](implicit drop: Drop[C, N]): drop.type = drop

    implicit def dropZero[C <: Coproduct]: Aux[C, Nat._0, C] =
      new Drop[C, Nat._0] {
        type Remaining = C
        def apply(c: C) = Some(c)
      }

    implicit def dropSucc[H, T <: Coproduct, N <: Nat](
      implicit tail: Drop[T, N]
    ): Aux[H :+: T, Succ[N], tail.Remaining] =
      new Drop[H :+: T, Succ[N]] {
        type Remaining = tail.Remaining
        def apply(c: H :+: T) = c match {
          case Inl(h) => None
          case Inr(t) => tail(t)
        }
      }
  }

  /**
   * Type class supporting reversing a Coproduct
   *
   * @author Stacy Curl
   * @author Alexandre Archambault
   */
  trait Reverse[C <: Coproduct] extends DepFn1[C] {
    type Out <: Coproduct
  }

  object Reverse {
    type Aux[C <: Coproduct, Out <: Coproduct] = Reverse[C] :=> Out
    def apply[C <: Coproduct](implicit reverse: Reverse[C]): reverse.type = reverse

    implicit def reverse[C <: Coproduct, O <: Coproduct](
      implicit reverse: Reverse0[CNil, C, O]
    ): Reverse[C] :=> O = new Reverse[C] {
      type Out = O
      def apply(c: C) = reverse(Right(c))
    }

    trait Reverse0[Acc <: Coproduct, L <: Coproduct, Out <: Coproduct] extends Serializable {
      def apply(e: Either[Acc, L]): Out
    }

    object Reverse0 {
      implicit def cnilReverse[Out <: Coproduct]: Reverse0[Out, CNil, Out] = {
        case Left(l) => l
        case Right(_) => unexpected
      }

      implicit def cconsReverse[Acc <: Coproduct, InH, InT <: Coproduct, Out <: Coproduct](
        implicit rt: Reverse0[InH :+: Acc, InT, Out]
      ): Reverse0[Acc, InH :+: InT, Out] = e =>
        rt(e match {
          case Left(acc) => Left(Inr(acc))
          case Right(Inl(h)) => Left(Inl(h))
          case Right(Inr(t)) => Right(t)
        })
    }
  }

  /**
   * Type class supporting permuting this `Coproduct` into the same order as another `Coproduct` with
   * the same element types.
   *
   * @author Michael Pilquist
   */
  trait Align[A <: Coproduct, B <: Coproduct] extends (A => B) with Serializable {
    def apply(a: A): B
  }

  object Align {
    def apply[A <: Coproduct, B <: Coproduct](implicit a: Align[A, B]): Align[A, B] = a

    implicit val cnilAlign: Align[CNil, CNil] =
      identity(_)

    implicit def coproductAlign[A <: Coproduct, BH, BT <: Coproduct, R <: Coproduct](
      implicit
      remove: Remove.Aux[A, BH, R],
      alignTail: Align[R, BT]
    ): Align[A, BH :+: BT] = remove(_) match {
      case Left(bh) => Inl(bh)
      case Right(rest) => Inr(alignTail(rest))
    }
  }

  /**
   * Type class supporting prepending to this `Coproduct`.
   *
   * @author Alexandre Archambault
   */
  trait Prepend[P <: Coproduct, S <: Coproduct] extends DepFn1[Either[P, S]] {
    type Out <: Coproduct
  }

  trait LowestPriorityPrepend {
    type Aux[P <: Coproduct, S <: Coproduct, Out <: Coproduct] = Prepend[P, S] :=> Out

    implicit def cconsPrepend[PH, PT <: Coproduct, S <: Coproduct, OutT <: Coproduct](
      implicit pt: Prepend[PT, S] :=> OutT
    ): Prepend[PH :+: PT, S] :=> (PH :+: OutT) =
      new Prepend[PH :+: PT, S] {
        type Out = PH :+: OutT
        def apply(e: Either[PH :+: PT, S]) = e match {
          case Left(Inl(h)) => Inl(h)
          case Left(Inr(t)) => Inr(pt(Left(t)))
          case Right(s) => Inr(pt(Right(s)))
        }
      }
  }

  trait LowPriorityPrepend extends LowestPriorityPrepend {
    implicit def cnilPrepend0[P <: Coproduct]: Prepend[P, CNil] :=> P =
      new Prepend[P, CNil] {
        type Out = P
        def apply(e: Either[P, CNil]) = e match {
          case Left(l) => l
          case Right(_) => unexpected
        }
      }
  }

  object Prepend extends LowPriorityPrepend {
    def apply[P <: Coproduct, S <: Coproduct](implicit prepend: Prepend[P, S]): prepend.type = prepend

    implicit def cnilPrepend1[S <: Coproduct]: Prepend[CNil, S] :=> S =
      new Prepend[CNil, S] {
        type Out = S
        def apply(e: Either[CNil, S]) = e match {
          case Right(r) => r
          case Left(_) => unexpected
        }
      }
  }

  /**
   * Type class providing access to init and last of a Coproduct
   *
   * @author Stacy Curl
   */
  trait InitLast[C <: Coproduct] extends Serializable {
    type I <: Coproduct
    type L
    def init(c: C): Option[I]
    def last(c: C): Option[L]
  }

  object InitLast {
    type Aux[C <: Coproduct, I0 <: Coproduct, L0] = InitLast[C] { type I = I0; type L = L0 }
    def apply[C <: Coproduct](implicit initLast: InitLast[C]): initLast.type = initLast

    implicit def initLastCoproduct[C <: Coproduct, ReverseC <: Coproduct, H, T <: Coproduct](
      implicit
      reverse: Reverse[C] :=> ReverseC,
      isCCons: IsCCons.Aux[ReverseC, H, T]
    ): Aux[C, T, H] = new InitLast[C] {
      type I = T
      type L = H
      def init(c: C): Option[I] = isCCons.tail(reverse(c))
      def last(c: C): Option[L] = isCCons.head(reverse(c))
    }
  }

  implicit object cnilOrdering extends Ordering[CNil] {
    def compare(x: CNil, y: CNil) = 0
  }

  implicit def coproductPartialOrdering[H, T <: Coproduct](
    implicit
    ordering: Ordering[H],
    partialOrdering: PartialOrdering[T]
  ): PartialOrdering[H :+: T] = new PartialOrdering[H :+: T] {
    def lteq(x: H :+: T, y: H :+: T): Boolean = (x, y) match {
      case (Inl(xh), Inl(yh)) => ordering.compare(xh, yh) <= 0
      case (Inr(xt), Inr(yt)) => partialOrdering.tryCompare(xt, yt).fold(false)(_ <= 0)
      case _                  => false
    }

    def tryCompare(x: H :+: T, y: H :+: T): Option[Int] = (x, y) match {
      case (Inl(xh), Inl(yh)) => Some(ordering.compare(xh, yh))
      case (Inr(xt), Inr(yt)) => partialOrdering.tryCompare(xt, yt)
      case _                  => None
    }
  }

  /**
   * Type class computing the `HList`  type corresponding to this `Coproduct`.
   *
   * @author Miles Sabin
   */
  trait ToHList[L <: Coproduct] extends DepFn {
    type Out <: HList
  }

  object ToHList {
    type Aux[L <: Coproduct, Out <: HList] = ToHList[L] :=> Out
    def apply[L <: Coproduct](implicit thl: ToHList[L]): thl.type = thl

    implicit val cnilToHList: ToHList[CNil] :=> HNil =
      new ToHList[CNil] {
        type Out = HNil
      }

    implicit def cconsToHList[H, T <: Coproduct, OutT <: HList](
      implicit ut: ToHList[T] :=> OutT
    ): ToHList[H :+: T] :=> (H :: OutT) =
      new ToHList[H :+: T] {
        type Out = H :: OutT
      }
  }


  /**
    * Type class checking that :
    * - coproduct is a sub-union of a bigger coproduct
    * - embeds a sub-coproduct into a bigger coproduct
    */
  trait Basis[Super <: Coproduct, Sub <: Coproduct] extends DepFn1[Super] {
    type Rest <: Coproduct
    type Out = Either[Rest, Sub]
    def inverse(e: Either[Rest, Sub]): Super
  }

  object Basis {
    type Aux[Super <: Coproduct, Sub <: Coproduct, R <: Coproduct] = Basis[Super, Sub] { type Rest = R }
    def apply[Super <: Coproduct, Sub <: Coproduct](implicit basis: Basis[Super, Sub]): basis.type = basis

    implicit def cnilBasis[Super <: Coproduct]: Aux[Super, CNil, Super] = new Basis[Super, CNil] {
      type Rest = Super
      def apply(s: Super) = Left(s)
      def inverse(e: Either[Rest, CNil]) = e match {
        case Left(l) => l
        case Right(_) => unexpected
      }
    }

    implicit def cconsBasis[Super <: Coproduct, H, T <: Coproduct, TRest <: Coproduct](
      implicit
      tailBasis: Basis.Aux[Super, T, TRest],
      remove: RemoveLast[TRest, H]
    ): Aux[Super, H :+: T, remove.Rest] = new Basis[Super, H :+: T] {
      type Rest = remove.Rest
      def apply(s: Super) = tailBasis(s) match {
        case Left(r) => remove(r) match {
          case Left(h) => Right(Inl(h))
          case Right(r) => Left(r)
        }
        case Right(t) => Right(Inr(t))
      }

      def inverse(e: Either[Rest, H :+: T]) = e match {
        case Left(r) => tailBasis.inverse(Left(remove.inverse(Right(r))))
        case Right(c) => c match {
          case Inl(h) => tailBasis.inverse(Left(remove.inverse(Left(h))))
          case Inr(t) => tailBasis.inverse(Right(t))
        }
      }
    }
  }

  private def toEither[Prefix, Suffix](c: Prefix :+: Suffix :+: CNil): Either[Prefix, Suffix] = c match {
    case Inl(prefix) => Left(prefix)
    case Inr(Inl(suffix)) => Right(suffix)
    case _ => sys.error("Impossible")
  }

  /**
    * Type class supporting reifying a `Coproduct` of singleton types.
    *
    * @author Jisoo Park
    */
  trait Reify[L <: Coproduct] extends DepFn0 {
    type Out <: HList
  }

  object Reify {
    type Aux[L <: Coproduct, Out <: HList] = Reify[L] :=> Out
    def apply[L <: Coproduct](implicit reify: Reify[L]): reify.type = reify

    implicit def cnilReify[L <: CNil]: Reify[L] :=> HNil =
      new Reify[L] {
        type Out = HNil
        def apply() = HNil
      }

    implicit def coproductReify[H, T <: Coproduct, OutT <: HList](
      implicit
      wh: Witness.Aux[H],
      rt: Reify[T] :=> OutT
    ): Reify[H :+: T] :=> (H :: OutT) =
      new Reify[H :+: T] {
        type Out = H :: OutT
        def apply() = wh.value :: rt()
      }
  }

  /** Type class supporting finding a typeclass instance for each type in a coproduct, resulting in
    * a coproduct of typeclass instances.
    */
  sealed trait LiftAll[F[_], In <: Coproduct] extends DepFn {
    type Out <: HList
    def instances: Out
  }

  object LiftAll {
    type Aux[F[_], In0 <: Coproduct, Out <: HList] = LiftAll[F, In0] :=> Out
    def apply[F[_]]: Curried[F] = new Curried[F]
    def apply[F[_], In <: Coproduct](implicit lift: LiftAll[F, In]): lift.type = lift

    class Curried[F[_]] {
      def apply[In <: Coproduct](in: In)(implicit lift: LiftAll[F, In]): lift.type = lift
    }

    implicit def liftAllCnil[F[_]]: LiftAll[F, CNil] :=> HNil = new LiftAll[F, CNil] {
      type Out = HNil
      def instances = HNil
    }

    implicit def liftAllCcons[F[_], H, T <: Coproduct, TI <: HList](
      implicit
      headInstance: F[H],
      tailInstances: LiftAll[F, T] :=> TI
    ): LiftAll[F, H :+: T] :=> (F[H] :: TI) =
      new LiftAll[F, H :+: T] {
        type Out = F[H] :: TI
        def instances = headInstance :: tailInstances.instances
      }
  }

  /**
    * Type class converting a `Coproduct` to an `Either`
    *
    * @author Michael Zuber
    */
  sealed trait CoproductToEither[C <: Coproduct] extends DepFn1[C]
  object CoproductToEither {
    type Aux[In <: Coproduct, Out] = CoproductToEither[In] :=> Out

    implicit def baseToEither[L, R]: CoproductToEither[L :+: R :+: CNil] :=> Either[L, R] =
      new CoproductToEither[L :+: R :+: CNil] {
        type Out = Either[L, R]
        def apply(t: L :+: R :+: CNil): Either[L, R] = t match {
          case Inl(l) => Left(l)
          case Inr(Inl(r)) => Right(r)
          case _ => unexpected
        }
      }

    implicit def cconsToEither[L, R <: Coproduct, OutR](
      implicit evR: CoproductToEither[R] :=> OutR
    ): CoproductToEither[L :+: R] :=> Either[L, OutR] = new CoproductToEither[L :+: R] {
      type Out = Either[L, OutR]
      def apply(t: L :+: R) = t match {
        case Inl(l) => Left(l)
        case Inr(r) => Right(evR(r))
      }
    }
  }

  /**
    * Type class converting an `Either` to a `Coproduct`
    *
    * @author Michael Zuber
    */
  sealed trait EitherToCoproduct[L, R] extends DepFn1[Either[L, R]] {
    type Out <: Coproduct
  }

  object EitherToCoproduct extends EitherToCoproductLowPrio {
    type Aux[L, R, Out <: Coproduct] = EitherToCoproduct[L, R] :=> Out

    implicit def econsEitherToCoproduct[L, RL, RR, OutR <: Coproduct](
      implicit evR: EitherToCoproduct[RL, RR] :=> OutR
    ): EitherToCoproduct[L, Either[RL, RR]] :=> (L :+: OutR) =
      new EitherToCoproduct[L, Either[RL, RR]] {
        type Out = L :+: OutR
        def apply(t: Either[L, Either[RL, RR]]) = t match {
          case Left(l) => Inl(l)
          case Right(r) => Inr(evR(r))
        }
      }
  }

  trait EitherToCoproductLowPrio {
    implicit def baseEitherToCoproduct[L, R]: EitherToCoproduct[L, R] :=> (L :+: R :+: CNil) =
      new EitherToCoproduct[L, R] {
        type Out = L :+: R :+: CNil
        def apply(t: Either[L, R]) = t match {
          case Left(l) => Inl(l)
          case Right(r) => Coproduct[L :+: R :+: CNil](r)
        }
      }
  }

  /**
    * Type class supporting the injection of runtime values of type `Any` in `Coproduct`.
    *
    * @author Juan José Vázquez Delgado
    * @author Fabio Labella
    */
  @implicitNotFound("Implicit not found. CNil has no values, so it's impossible to convert anything to it")
  trait RuntimeInject[C <: Coproduct] extends Serializable {
    def apply(x: Any): Option[C]
  }

  object RuntimeInject extends RuntimeInjectLowPrio {
    implicit def baseCaseRuntimeInject[H](implicit castH: Typeable[H]): RuntimeInject[H :+: CNil] =
      castH.cast(_).map(Inl(_))
  }

  trait RuntimeInjectLowPrio {
    implicit def inductiveCaseRuntimeInject[H, T <: Coproduct](
      implicit
      next: RuntimeInject[T],
      castH: Typeable[H]
    ): RuntimeInject[H :+: T] =
      x => castH.cast(x) match {
        case Some(value) => Option(Inl(value))
        case None => next(x).map(v => Inr(v))
      }
  }
}
