module Main where

open import Agda.Builtin.Char                    using (primIsSpace)
open import Agda.Builtin.Equality                using (_≡_ ; refl)
open import Data.Char                as Char     using (show)
open import Data.Maybe               as Maybe    using (maybe′)
open import Data.String              as String   using (String ; _++_)
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

open import Eval
open import Parsers
open import Util

module Main where
  cli : CLI _
  cli = record
    { name = "agda-scheme"
    ; exec = record
    { description  = "Scheme, in Agda!"
    ; subcommands  = noSubCommands
    ; modifiers   = , "-O"           ∷= flag "deprecated"
                    ⟨ "--help"       ∷= flag "Display this help"
                    ⟨ "--parse-only" ∷= flag "Parse but don't execute"
                    ⟨ "--version"    ∷= flag "Output version information and exit"
                    ⟨ ⟨⟩
    ; arguments    = Usual.string -- lotsOf filePath
    }
    }

  -- TODO: use Sum, Parsers.parse
  -- "real main", moved out of IO for better unit testing
  realMain : String → String
  realMain args =
    maybe′ (Util.show ∘ Success.value) ("[ERR] No parse: " ++ args)
           (Parsers.parseit! Parsers.expr args)

  main : _
  main = withCLI cli (putStrLn ∘ maybe′ realMain "[ERR] Bad arguments!" ∘ helper)
    where
      helper : ParsedInterface cli → Maybe.Maybe String
      helper (subCommand () _)
      helper (theCommand _ parsedArgs) = parsedArgs
