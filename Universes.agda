{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

-- Adapted from https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

module Universes where

open import Agda.Primitive public
 renaming (
            Level to Universe -- We speak of universes rather than of levels.
          ; lzero to ð¤â       -- Our first universe is called ð¤â
          ; lsuc to _âº        -- The universe after ð¤ is ð¤ âº
          ; SetÏ to ð¤Ï        -- There is a universe ð¤Ï strictly above ð¤â, ð¤â, â¯ , ð¤â, â¯
          )
 using    (_â_)               -- Least upper bound of two universes, e.g. ð¤â â ð¤â is ð¤â

Type = Î» â â Set â

_Ì   : (ð¤ : Universe) â Type (ð¤ âº)

ð¤âÌ  = Type ð¤

ð¤â = ð¤â âº
ð¤â = ð¤â âº
ð¤â = ð¤â âº

_âºâº : Universe â Universe
ð¤ âºâº = ð¤ âº âº

universe-of : {ð¤ : Universe} (X : ð¤âÌ ) â Universe
universe-of {ð¤} X = ð¤

infix  1 _Ì
