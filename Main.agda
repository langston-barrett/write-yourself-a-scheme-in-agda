module Main where

open import Agda.Builtin.Char                    using (primIsSpace)
open import Agda.Builtin.Equality                using (_≡_ ; refl)
open import Data.Char                as Char     using (show)
open import Data.Maybe               as Maybe    using (maybe′)
open import Data.String              as String   using (String)
open import Function                             using (_$_ ; _∘_ ; id ; const)
open import Text.Parser.Success      as Success

-- CLI Imports
open import IO
open import Data.Product
open import agdARGS.System.Console.CLI hiding ([_)
open import agdARGS.System.Console.CLI.Usage
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.System.Console.Modifiers
open import agdARGS.System.Console.Options.Usual as Usual hiding (Parser; string)

open import Parsers

module Main where
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
    ; arguments    = Usual.string -- lotsOf filePath
    }
    }

  -- TODO: improve both of these
  -- "real main", moved out of IO for better unit testing
  io : ParsedInterface cli → String
  io (subCommand () _)
  io (theCommand _  a) =
    maybe′ (Char.show ∘ Success.value) "No parse"
          (Parsers.parseit! Parsers.symbol
                            (maybe′ id "" a)) -- TODO: error on lack of parse

  main = withCLI cli (putStrLn ∘ io)
