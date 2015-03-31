{-# LANGUAGE TypeFamilies #-}

module Types where

import Nodes

data IntT
data BoolT

instance Show IntT where
    show _ = undefined

instance Show BoolT where
    show _ = undefined

type instance Den IntT = Int
type instance Den BoolT = Bool

