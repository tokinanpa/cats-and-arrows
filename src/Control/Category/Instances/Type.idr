||| This module defines record-style wrappers for the canonical
||| category of Idris types and pure unrestricted functions, referred
||| to simply as `Typ`.
module Control.Category.Instances.Type

import Control.Category
import Control.Category.Records

%default total

namespace SemigroupoidR
  public export
  Typ : SemigroupoidR
  Typ = MkSemigroupoidR (~~>) {impl = Function}

namespace CategoryR
  public export
  Typ : CategoryR
  Typ = MkCategoryR (~~>) {impl = Function}

namespace MonoidalR
  public export
  TypPair : MonoidalR
  TypPair = MkMonoidalR (~~>) Pair () {impl = FuncPair}

  public export
  TypEither : MonoidalR
  TypEither = MkMonoidalR (~~>) Either Void {impl = FuncEither}

namespace BraidedR
  public export
  TypPair : BraidedR
  TypPair = MkBraidedR (~~>) Pair () {impl = FuncPair}

  public export
  TypEither : BraidedR
  TypEither = MkBraidedR (~~>) Either Void {impl = FuncEither}

namespace CartesianR
  public export
  Typ : CartesianR
  Typ = MkCartesianR (~~>) Pair () {impl = Function}

namespace CocartesianR
  public export
  Typ : CocartesianR
  Typ = MkCocartesianR (~~>) Either Void {impl = Function}

namespace ClosedR
  public export
  Typ : ClosedR
  Typ = MkClosedR (~~>) Pair (~~>) () {impl = Function}

namespace BimonoidalR
  public export
  Typ : BimonoidalR
  Typ = MkBimonoidalR (~~>) Either Pair Void () {impl = Function}

namespace RigCategoryR
  public export
  Typ : RigCategoryR
  Typ = MkRigCategoryR (~~>) Either Pair Void () {impl = Function}

namespace SymRigCategoryR
  public export
  Typ : SymRigCategoryR
  Typ = MkSymRigCategoryR (~~>) Either Pair Void () {impl = Function}

namespace DistributiveR
  public export
  Typ : DistributiveR
  Typ = MkDistributiveR (~~>) Either Pair Void () {impl = Function}
