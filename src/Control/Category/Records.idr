||| This module exports "record-style" wrappers around various
||| interfaces in this library. These may be easier to use if the
||| categories you're constructing are particularly complex, as
||| Idris's interface resolution can often break.
|||
||| To convert a structure into its record-style variant, simply use
||| the record constructor. The interace implementation will be
||| automatically searched for, or it can be explicitly specified
||| using the `con` argument (short for constraint). Likewise, the
||| `(.con)` field can be used to extract the interface implementation
||| from the record.
module Control.Category.Records

import public Control.Category.Records.Semigroupoid as Control.Category.Records
import public Control.Category.Records.Category as Control.Category.Records
import public Control.Category.Records.Functor as Control.Category.Records
import public Control.Category.Records.NatTrans as Control.Category.Records
import public Control.Category.Records.Monad as Control.Category.Records
import public Control.Category.Records.Monoidal as Control.Category.Records
import public Control.Category.Records.Braided as Control.Category.Records
import public Control.Category.Records.Cartesian as Control.Category.Records
import public Control.Category.Records.Cocartesian as Control.Category.Records
import public Control.Category.Records.Bimonoidal as Control.Category.Records
import public Control.Category.Records.Closed as Control.Category.Records
import public Control.Category.Records.Traced as Control.Category.Records
