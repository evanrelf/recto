{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Recto.Internal.Plugin where

import Control.Monad.IO.Class (liftIO)
import Generics.SYB (everywhereM, mkM)
import GHC (mkModuleName)
import GHC.Data.FastString (FastString)
import GHC.Driver.Main (getHscEnv)
import GHC.Driver.Env (HscEnv (hsc_NC))
import GHC.Hs
  ( HsExpr (HsVar, HsOverLabel, RecordCon)
  , HsModule (..)
  , HsParsedModule (..)
  , HsRecFields (HsRecFields)
  , LHsRecField
  , LHsExpr
  , GhcPs
  , noExtField
  , mkHsApps
  )
import GHC.Parser.Annotation (noAnn, reLoc, reLocA)
import GHC.Plugins
  ( CommandLineOption
  , Plugin (..)
  , ModSummary
  , Hsc
  , defaultPlugin
  , purePlugin
  )
import GHC.Stack (HasCallStack)
import GHC.Types.Name (Name)
import GHC.Types.Name.Occurrence (mkVarOcc, occNameString)
import GHC.Types.Name.Reader (RdrName (Exact, Unqual))
import GHC.Types.SrcLoc (GenLocated (L), SrcSpan)
import GHC.Unit.Finder (FindResult (Found), findImportedModule)
import GHC.Unit.Module.Name (ModuleName)

plugin :: Plugin
plugin =
  defaultPlugin
    { parsedResultAction = sourcePlugin
    , pluginRecompile = purePlugin
    }

sourcePlugin
  :: [CommandLineOption]
  -> ModSummary
  -> HsParsedModule
  -> Hsc HsParsedModule
sourcePlugin _ _ hsParsedModule = do
  let HsParsedModule{ hpm_module = L l hsModule } = hsParsedModule
  let HsModule{ hsmodDecls = decls } = hsModule
  decls' <- everywhereM (mkM transformExpr) decls
  let hsModule' = hsModule{ hsmodDecls = decls' }
  let hsParsedModule' = hsParsedModule{ hpm_module = L l hsModule' }
  pure hsParsedModule'

transformExpr :: LHsExpr GhcPs -> Hsc (LHsExpr GhcPs)
transformExpr e@(reLoc -> L l expr)
  | RecordCon _ (L _ name) (HsRecFields fields dotdot) <- expr
  , Unqual (occNameString -> "ANON") <- name
  , Just fields <- traverse getField fields
  , Nothing <- dotdot
  = do
      names <- getRectoNames
      pure $ anonExpr names l fields

  | otherwise
  = pure e

  where
  getField
    :: LHsRecField GhcPs (LHsExpr GhcPs)
    -> Maybe (FastString, LHsExpr GhcPs)
  getField = undefined

anonExpr
  :: RectoNames
  -> SrcSpan
  -> [(FastString, LHsExpr GhcPs)]
  -> LHsExpr GhcPs
anonExpr RectoNames{ recto_empty, recto_insert } l = go
  where
  go :: [(FastString, LHsExpr GhcPs)] -> LHsExpr GhcPs
  go [] = mkVar l recto_empty
  go ((n, e) : fs) = mkVar l recto_insert `mkHsApps` [mkLabel l n, e, go fs]

  mkVar :: SrcSpan -> RdrName -> LHsExpr GhcPs
  mkVar l name = reLocA $ L l $ HsVar noExtField (reLocA $ L l name)

  mkLabel :: SrcSpan -> FastString -> LHsExpr GhcPs
  mkLabel l n = reLocA $ L l $ HsOverLabel noAnn n

data RectoNames = RectoNames
  { recto_empty :: RdrName
  , recto_insert :: RdrName
  }

getRectoNames :: Hsc RectoNames
getRectoNames = do
  let moduleName = mkModuleName "Recto"
  recto_empty <- Exact <$> undefined moduleName "empty"
  recto_insert <- Exact <$> undefined moduleName "insert"
  pure RectoNames{ recto_empty, recto_insert }
  where
  lookupName :: HasCallStack => ModuleName -> String -> Hsc Name
  lookupName moduleName stringName = do
    env <- getHscEnv
    mModule <- liftIO $ findImportedModule env moduleName Nothing
    case mModule of
      Found _ module_ -> do
        name <- liftIO $ lookupNameCache (hsc_NC env) module_ stringName
        pure $ mkVarOcc name
      _ -> error "lookupName: name not found"
