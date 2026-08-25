||| This module defines record-style wrappers for the canonical
||| category of Idris types and pure unrestricted functions, referred
||| to simply as `Typ`.
module Control.Category.Instances.Type

import Control.Category
import Control.Category.Semigroupoid
import Control.Category.Bimonoidal
import Control.Category.Records

%default total

namespace SemigroupoidR
  public export
  Typ : SemigroupoidR
  Typ = MkSemigroupoidR (~~>) {con = Function}

namespace CategoryR
  public export
  Typ : CategoryR
  Typ = MkCategoryR (~~>) {con = Function}

namespace MonoidalR
  public export
  TypPair : MonoidalR
  TypPair = MkMonoidalR (~~>) Pair () {con = FuncPair}

  public export
  TypEither : MonoidalR
  TypEither = MkMonoidalR (~~>) Either Void {con = FuncEither}

namespace BraidedR
  public export
  TypPair : BraidedR
  TypPair = MkBraidedR (~~>) Pair () {con = FuncPair}

  public export
  TypEither : BraidedR
  TypEither = MkBraidedR (~~>) Either Void {con = FuncEither}

namespace CartesianR
  public export
  Typ : CartesianR
  Typ = MkCartesianR (~~>) Pair () {con = Function}

namespace CocartesianR
  public export
  Typ : CocartesianR
  Typ = MkCocartesianR (~~>) Either Void {con = Function}

namespace ClosedR
  public export
  Typ : ClosedR
  Typ = MkClosedR (~~>) Pair (~~>) () {con = Function}

namespace BimonoidalR
  public export
  Typ : BimonoidalR
  Typ = MkBimonoidalR (~~>) Either Pair Void () {con = Function}

namespace RigCategoryR
  public export
  Typ : RigCategoryR
  Typ = MkRigCategoryR (~~>) Either Pair Void () {con = Function}

namespace SymRigCategoryR
  public export
  Typ : SymRigCategoryR
  Typ = MkSymRigCategoryR (~~>) Either Pair Void () {con = Function}

namespace DistributiveR
  public export
  Typ : DistributiveR
  Typ = MkDistributiveR (~~>) Either Pair Void () {con = Function}
