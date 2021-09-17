module Janus.Style
  ( Style(..)
  , ascii
  , unicode
  ) where

data Style = Style
  { stUniverse    :: String
  , stLambda      :: String
  , stArrow       :: String
  , stForall      :: String
  , stMPairTypeOp :: String
  , stMUnitType   :: String
  , stAPairOpen   :: String
  , stAPairClose  :: String
  , stAUnit       :: String
  , stAUnitType   :: String
  , stSumTypeOp   :: String
  , stMany        :: String
  }

unicode :: Style
unicode = Style { stUniverse    = "𝘜"
                , stLambda      = "λ"
                , stArrow       = "→"
                , stForall      = "∀"
                , stMPairTypeOp = "⊗"
                , stMUnitType   = "𝟭ₘ"
                , stAPairOpen   = "⟨"
                , stAPairClose  = "⟩"
                , stAUnit       = "⟨⟩"
                , stAUnitType   = "⊤"
                , stSumTypeOp   = "⊕"
                , stMany        = "ω"
                }

ascii :: Style
ascii = Style { stUniverse    = "U"
              , stLambda      = "\\"
              , stArrow       = "->"
              , stForall      = "forall"
              , stMPairTypeOp = "*"
              , stMUnitType   = "I"
              , stAPairOpen   = "<"
              , stAPairClose  = ">"
              , stAUnit       = "<>"
              , stAUnitType   = "T"
              , stSumTypeOp   = "+"
              , stMany        = "w"
              }

