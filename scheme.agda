module _ where

open import Agda.Builtin.Equality
open import Level as L
open import Data.Bool
open import Data.Char
open import Data.Nat.Properties
open import Data.Char.Base
open import Data.String as String
open import Data.List as List hiding ([_])
open import Data.List.Sized as Sized hiding (map)
open import Data.Maybe as Maybe
open import Function
open import Category.Monad

open import Relation.Unary.Indexed public
open import Induction.Nat.Strong hiding (<-lower ; ≤-lower)
open import Text.Parser.Success
open import Text.Parser.Combinators
open import Text.Parser.Char

-- CLI Imports
open import IO
open import Data.Product
open import agdARGS.System.Console.CLI
open import agdARGS.System.Console.CLI.Usage
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.System.Console.Modifiers
open import agdARGS.System.Console.Options.Usual hiding (Parser)

instance eqChar = Data.Char._≟_

instance
  plusMaybe : RawMonadPlus {L.zero} Maybe
  plusMaybe = Maybe.monadPlus

  plusList : RawMonadPlus {L.zero} List.List
  plusList = List.monadPlus


parser : [ Parser Char (∣List Char ∣≡_) Maybe Bool ]
parser =
  fix (Parser Char (∣List Char ∣≡_) Maybe Bool) $
    λ rec → (true <$ anyOf (String.toList "!#$%&|*+-/:<=>?@^_~"))

module _ {A : Set} {M : Set → Set} where

  parseit! : [ Parser Char (∣List Char ∣≡_) M A ] → (str : String) → M (Success Char (∣List Char ∣≡_) A (List.length (String.toList str)))
  parseit! parser str =
   runParser parser (n≤1+n _) (Sized.fromList (String.toList str))

test₁ : maybe′ (λ x → Success.value x) false (parseit! parser "$$@") ≡ true
test₁ = refl

cli : CLI _
cli = record
  { name = "agda-scheme"
  ; exec = record
  { description  = "Scheme, in Agda!"
  ; subcommands  = noSubCommands
  ; modifiers   = , "-O"        ∷= flag "deprecated"
                  ⟨ "--help"    ∷= flag "Display this help"
                  ⟨ "--version" ∷= flag "Output version information and exit"
                  ⟨ ⟨⟩
  ; arguments    = string -- lotsOf filePath
  }
  }

main = withCLI cli handler where
  handler : ParsedInterface cli → IO _
  handler (theCommand _  a) = putStrLn (maybe id "" a)
  handler (subCommand () _)
