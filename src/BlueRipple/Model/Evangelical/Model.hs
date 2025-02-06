{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module BlueRipple.Model.Evangelical.Model
  (
    module BlueRipple.Model.Evangelical.Model
  , module BlueRipple.Model.Election2.ModelCommon
  )
where

import qualified BlueRipple.Model.Election2.DataPrep as DP
import qualified BlueRipple.Model.Election2.ModelCommon as MC
import BlueRipple.Model.Election2.ModelCommon (ModelConfig(..))
import qualified BlueRipple.Model.Election2.ModelCommon2 as MC2
import qualified BlueRipple.Model.Election2.ModelRunner as MR
import qualified BlueRipple.Model.Demographic.DataPrep as DDP
import qualified BlueRipple.Model.StanTools as MST

--import qualified BlueRipple.Configuration as BR
import qualified BlueRipple.Data.CachingCore as BRCC
import qualified BlueRipple.Data.Types.Demographic as DT
import qualified BlueRipple.Data.Types.Geographic as GT
import qualified BlueRipple.Data.Types.Modeling as MT
import qualified BlueRipple.Data.CES as CCES
import qualified BlueRipple.Data.ACS_PUMS as ACS
import qualified BlueRipple.Data.Small.Loaders as BR
import qualified BlueRipple.Data.Small.DataFrames as BR
import qualified BlueRipple.Data.FramesUtils as BRF
--import qualified BlueRipple.Utilities.KnitUtils as BR

import qualified Knit.Report as K

import qualified Stan as S
import qualified Stan.Libraries.BuildingBlocks as SBB (rowLength)
import Stan (TypedList(..))
import Stan.Operators
{-
import qualified Stan.ModelBuilder as SMB
import qualified Stan.ModelRunner as SMR
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TEO
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as SF
import qualified Stan.Parameters as SP
import qualified Stan.ModelConfig as SC
import qualified Stan.RScriptBuilder as SR
import qualified Stan.ModelBuilder.BuildingBlocks as SBB
import qualified Stan.ModelBuilder.BuildingBlocks.GroupAlpha as SG
import qualified Stan.ModelBuilder.DesignMatrix as DM
-}
import qualified CmdStan as CS

import qualified Frames as F
import qualified Frames.Melt as F
import qualified Frames.MapReduce as FMR
import qualified Frames.SimpleJoins as FJ
import qualified Frames.Constraints as FC
import qualified Frames.Streamly.TH as FS
import qualified Frames.Streamly.InCore as FI
import qualified Frames.Serialize as FS

import qualified Control.Foldl as FL
import qualified Control.Foldl.Statistics as FLS
import Control.Lens (view)

import qualified Flat
import qualified Data.IntMap.Strict as IM
import qualified Data.List as List
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vinyl as V
import qualified Data.Vinyl.TypeLevel as V

FS.declareColumn "NEvangelical" ''Int
FS.declareColumn "NEvangelicalW" ''Double

type CountDataR = [DP.SurveyWeight, DP.Surveyed, NEvangelical, DP.SurveyedW, NEvangelicalW]

type CESByR k = k V.++ DP.PredictorsR V.++ CountDataR

type CESByCDR = CESByR DP.CDKeyR

type CESByCD = F.Record CESByCDR

runEvangelicalModel :: forall l r ks b .
                   (K.KnitEffects r
                   , BRCC.CacheEffects r
                   , V.RMap l
                   , Ord (F.Record l)
                   , FS.RecFlat l
                   , Typeable l
                   , Typeable (DP.PSDataR ks)
                   , F.ElemOf (DP.PSDataR ks) GT.StateAbbreviation
                   , DP.LPredictorsR F.⊆ DP.PSDataR ks
                   , F.ElemOf (DP.PSDataR ks) DT.PopCount
                   , DP.DCatsR F.⊆ DP.PSDataR ks
                   , l F.⊆ DP.PSDataR ks --'[GT.StateAbbreviation]
                   , Show (F.Record l)
                   )
                => CCES.SurveyYear
                -> MR.CacheStructure () ()
                -> PSType (F.Record DP.DCatsR -> Bool)
                -> ModelConfig b
                -> K.ActionWithCacheTime r (DP.PSData ks)
                -> K.Sem r (K.ActionWithCacheTime r (MC.PSMap l MT.ConfidenceInterval, MC2.ModelParameters))
runEvangelicalModel cesYear cacheStructure psType mc psData_C = do
  let --config = MC2.TurnoutOnly tc
      runConfig = RunConfig False False (Just (MC.psGroupTag @l, psType))
  modelData_C <- cachedPreppedCES cacheStructure cesYear
  runModel (MR.csModelDirE cacheStructure)  ("E_" <> show (CCES.cesYear cesYear))
    (MR.csPSName cacheStructure) runConfig mc modelData_C psData_C

type ModelRTT = S.RowTypeTag CESByCD
type ModelData b = MC.ModelData CESByCD b

evangelicalModelData ::  forall b gq . ModelConfig b -> S.StanModelBuilderEff CESData gq (MC.ModelData CESByCD b)
evangelicalModelData mc = do
  let modelIDT :: S.InputDataType S.ModelDataT CESData = S.ModelData
      cesSurveyDataTag :: S.StanModelBuilderEff CESData gq ModelRTT
      cesSurveyDataTag = S.getRTT modelIDT "CES"
  let uwSurveyed :: FC.ElemsOf rs [DP.Surveyed, DP.SurveyWeight] => ModelRTT -> S.StanModelBuilderEff CESData gq S.IntArrayE
      uwSurveyed rtt = S.addCountData modelIDT rtt "Surveyed" (view DP.surveyed)
      weightedCount ws = DP.weightedCountF ws (view DP.surveyed) (view DP.surveyWeight) (view DP.surveyedESS)
      weightedQty ws = DP.weightedQtyF ws (view DP.surveyed) (view DP.surveyWeight) (view DP.surveyedESS)
      uwEvangelical :: FC.ElemsOf rs [NEvangelical, DP.SurveyWeight] => ModelRTT -> S.StanModelBuilderEff CESData gq S.IntArrayE
      uwEvangelical rtt = S.addCountData modelIDT rtt "Evangelical" (view nEvangelical)
      wSurveyed :: FC.ElemsOf rs '[DP.Surveyed, DP.SurveyWeight, DP.SurveyedESS]
                => DP.WeightingStyle -> ModelRTT -> S.StanModelBuilderEff CESData gq S.VectorE
      wSurveyed ws rtt = S.addRealData modelIDT rtt "Surveyed" (Just 0) Nothing (weightedCount ws)
      wEvangelical :: FC.ElemsOf rs [NEvangelicalW, DP.SurveyWeight] => DP.WeightingStyle -> ModelRTT -> S.StanModelBuilderEff CESData gq S.VectorE
      wEvangelical ws rtt = S.addRealData modelIDT rtt "Evangelical" (Just 0) Nothing (weightedQty ws (view nEvangelicalW))
      rwSurveyed :: FC.ElemsOf rs [DP.Surveyed, DP.SurveyWeight, DP.SurveyedESS]
                 => DP.WeightingStyle -> ModelRTT -> S.StanModelBuilderEff CESData gq S.IntArrayE
      rwSurveyed ws rtt = S.addCountData modelIDT rtt "Surveyed" (round . weightedCount ws)
      rwEvangelical ::  FC.ElemsOf rs [NEvangelical, DP.SurveyWeight] => DP.WeightingStyle -> ModelRTT -> S.StanModelBuilderEff CESData gq S.IntArrayE
      rwEvangelical ws rtt = S.addCountData modelIDT rtt "Evangelical" (round . weightedQty ws (view nEvangelicalW))
  case mc.mcSurveyAggregation of
        MC.UnweightedAggregation -> fmap MC.ModelData $ cesSurveyDataTag >>= \rtt -> MC.covariatesAndCountsFromData rtt mc uwSurveyed uwEvangelical
        MC.RoundedWeightedAggregation ws -> fmap MC.ModelData $ cesSurveyDataTag >>= \rtt -> MC.covariatesAndCountsFromData rtt mc (rwSurveyed ws) (rwEvangelical ws)
        MC.WeightedAggregation _ ws -> fmap MC.ModelData $ cesSurveyDataTag >>= \rtt -> MC.covariatesAndCountsFromData rtt mc (wSurveyed ws) (wEvangelical ws)


data PSType a = PSAll Text | PSGiven Text Text a | PSAmong Text Text a

psPrefix :: PSType a -> Text
psPrefix (PSAll p) = p
psPrefix (PSGiven p _ _) = p
psPrefix (PSAmong p _ _) = p

psTypeDataGQ :: forall k md gq . DP.DCatsR F.⊆ DP.PSDataR k
             => S.RowTypeTag (F.Record (DP.PSDataR k)) -> PSType (F.Record DP.DCatsR -> Bool) -> S.StanModelBuilderEff md gq (PSType S.IntArrayE)
psTypeDataGQ psRowTag pst = do
--  cesGQRowTag <- S.dataSetTag @CESByCD S.ModelData "CES"
  let boolToInt :: Bool -> Int
      boolToInt False = 0
      boolToInt True = 1
      psIDT :: S.InputDataType S.GQDataT (DP.PSData k) = S.GQData
  case pst of
    PSAll p -> pure $ PSAll p
    PSGiven p vName cF -> S.addIntData psIDT psRowTag vName (Just 0) (Just 1) (boolToInt . cF . F.rcast) >>= pure . PSGiven p vName
    PSAmong p vName cF -> S.addIntData psIDT psRowTag vName (Just 0) (Just 1) (boolToInt . cF . F.rcast) >>= pure . PSAmong p vName

psTypeToArgs :: PSType S.IntArrayE
             -> (Text, Maybe (S.CodeWriter (S.VectorE -> S.VectorE)), Maybe (S.CodeWriter (S.IntArrayE -> S.IntArrayE)))
psTypeToArgs (PSAll p) = (p, Nothing, Nothing)
psTypeToArgs (PSGiven p _ ia) = (p, Just $ pure $ \v -> v |.*| S.to_vector ia, Nothing)
psTypeToArgs (PSAmong p _ ia) = (p, Nothing, Just $ pure $ \v -> v |.*| ia)


data RunConfig l = RunConfig { rcIncludePPCheck :: Bool, rcIncludeLL :: Bool, rcPS :: Maybe (S.GroupTypeTag (F.Record l), PSType (F.Record DP.DCatsR -> Bool)) }
-- not returning anything for now
model :: forall k l b .
         (Typeable (DP.PSDataR k)
         , F.ElemOf (DP.PSDataR k) DT.PopCount
         , DP.LPredictorsR F.⊆ DP.PSDataR k
         , DP.DCatsR F.⊆ DP.PSDataR k
         )
      => RunConfig l
      -> ModelConfig b
      -> [Text]
      -> S.StanModelBuilderEff CESData (DP.PSData k) ()
model rc mc states = do
  mData <- evangelicalModelData mc
  paramSetup <- MC2.setupParameters Nothing states mc
  (MC2.Components modelM llM ppM centerF) <- MC2.components Nothing (MC.covariatesAndCounts mData) paramSetup mc.mcSurveyAggregation
  modelM
  when rc.rcIncludePPCheck $ void ppM
  when rc.rcIncludeLL llM
  let gqIDT :: S.InputDataType S.GQDataT (DP.PSData k) = S.GQData
  case rc.rcPS of
    Nothing -> pure ()
    Just (gtt, pst) -> do
      psRowTag <- S.getRTT @(F.Record (DP.PSDataR k)) gqIDT "PSData" --S.dataSetTag @(F.Record (DP.PSDataR k)) S.GQData "PSData"
      (prefix, modP, modN) <- fmap psTypeToArgs $ psTypeDataGQ @k psRowTag pst
      MC2.postStratifyOne gqIDT psRowTag (view DT.popCount) F.rcast prefix paramSetup modP modN mc.mcDesignMatrixRow (Just $ centerF S.GQDataT) Nothing gtt >> pure ()

runModel :: forall l k r b .
            (K.KnitEffects r
            , BRCC.CacheEffects r
            , l F.⊆ DP.PSDataR k
            , F.ElemOf (DP.PSDataR k) DT.PopCount
            , DP.LPredictorsR F.⊆ DP.PSDataR k
            , V.RMap l
            , Ord (F.Record l)
            , FS.RecFlat l
            , Typeable (DP.PSDataR k)
            , F.ElemOf (DP.PSDataR k) GT.StateAbbreviation
            , DP.DCatsR F.⊆ DP.PSDataR k
            , DP.DCatsR F.⊆ CESByCDR
            , DP.LPredictorsR F.⊆ CESByCDR
            , Show (F.Record l)
            , Typeable l
            )
         => Either Text Text
         -> Text
         -> Text
         -> RunConfig l
         -> ModelConfig b
         -> K.ActionWithCacheTime r CESData
         -> K.ActionWithCacheTime r (DP.PSData k)
         -> K.Sem r (K.ActionWithCacheTime r (MC.PSMap l MT.ConfidenceInterval, MC2.ModelParameters))
runModel modelDirE modelName gqName runConfig config modelData_C psData_C = do
  let dataName = MC.modelConfigText config
  stanDir <- K.liftKnit MST.stanDir >>= K.knitMaybe "runModel: empty stanDir!" . BRCC.insureFinalSlash
  let runnerInputNames = S.RunnerInputNames
                         (stanDir <> modelName <> "/")
                         (MC.modelConfigText config)
                         (Just $ S.GQNames "GQ" (dataName <> "_" <> gqName))
                         dataName
--  modelData <- K.ignoreCacheTime modelData_C
  states <- S.toList . FL.fold (FL.premap (view GT.stateAbbreviation) FL.set) . unCESData <$> K.ignoreCacheTime modelData_C
  psKeys <- S.toList . FL.fold (FL.premap (F.rcast @l) FL.set) . DP.unPSData <$> K.ignoreCacheTime psData_C
  (dw, code) <- S.dataWranglerAndCode modelData_C psData_C
                (groupBuilder config states)
                (const $ psGroupBuilder states psKeys)
                (\_ _ -> model runConfig config states)

  let datSuffix = S.rinData runnerInputNames
      jsonData t = "jsonData_" <> datSuffix <> "$" <> t
      evangelical = jsonData "Evangelical"
      surveyed = jsonData "Surveyed"
      rSuffix = S.rinModel runnerInputNames <> "_" <> datSuffix
      unwraps = case config.mcSurveyAggregation of
        MC.WeightedAggregation MC.BetaProportion _ -> [S.UnwrapExpr (evangelical <> " / " <> surveyed) ("yEvangelicalRate_" <> rSuffix)]
        _ -> [S.UnwrapNamed "Evangelical" ("yEvangelical_" <> rSuffix)]
  res_C <- S.runModel' @BRCC.SerializerC @BRCC.CacheData
           modelDirE
           (Right runnerInputNames)
           Nothing
           dw
           code
           (modelResultAction config runConfig) --S.DoNothing -- (stateModelResultAction mcWithId dmr)
           (S.Both unwraps) --(S.Both [S.UnwrapNamed "successes" "yObserved"])
           modelData_C
           psData_C
  K.logLE K.Info $ modelName <> " run complete."
  pure res_C

groupBuilder :: forall g k l b .
                 (Foldable g
--                 , Typeable (DP.PSDataR k)
--                 , Show (F.Record l)
--                 , Ord (F.Record l)
--                 , l F.⊆ DP.PSDataR k
--                 , Typeable l
--                 , F.ElemOf (DP.PSDataR k) GT.StateAbbreviation
--                 , DP.DCatsR F.⊆ DP.PSDataR k
                 )
               => ModelConfig b
               -> g Text
--               -> g (F.Record l)
               -> S.StanDataBuilderEff S.ModelDataT CESData ()
groupBuilder _config states = do
  let groups' = MC.groups states
      modelIDT :: S.InputDataType S.ModelDataT CESData = S.ModelData
  S.addData "CES" modelIDT (S.ToFoldable unCESData) >>= MC.addGroupIndexesAndIntMaps groups' >> pure ()
--  psGroupBuilder states psKeys

-- NB: often l ~ k, e.g., for predicting district turnout/preference
-- But say you want to predict turnout by race, nationally.
-- Now l ~ '[Race5C]
-- How about turnout by Education in each state? Then l ~ [StateAbbreviation, Education4C]
psGroupBuilder :: forall g k l md .
                 (Foldable g
                 , Typeable (DP.PSDataR k)
                 , Show (F.Record l)
                 , Ord (F.Record l)
                 , l F.⊆ DP.PSDataR k
                 , Typeable l
                 , F.ElemOf (DP.PSDataR k) GT.StateAbbreviation
                 , DP.DCatsR F.⊆ DP.PSDataR k
                 )
               => g Text
               -> g (F.Record l)
               -> S.StanDataBuilderEff S.GQDataT (DP.PSData k) ()
psGroupBuilder states psKeys = do
  let groups' = MC.groups states
      gqIDT :: S.InputDataType S.GQDataT (DP.PSData k) = S.GQData
      psGtt = MC.psGroupTag @l
  psRowTag <- S.addData "PSData" gqIDT (S.ToFoldable DP.unPSData)
  S.addGroupIndexForData gqIDT psGtt psRowTag $ S.makeIndexFromFoldable show F.rcast psKeys
  S.addGroupIntMapForData gqIDT psGtt psRowTag $ S.dataToIntMapFromFoldable F.rcast psKeys
  S.addGroupIndexes gqIDT psRowTag F.rcast groups'

--NB: parsed summary data has stan indexing, i.e., Arrays start at 1.
--NB: Will return no prediction (Nothing) for "both" model for now. Might eventually return both predictions?
modelResultAction :: forall k l r b .
                     (Ord (F.Record l)
                     , K.KnitEffects r
                     , Typeable (DP.PSDataR k)
                     , Typeable l
--                     , DP.LPredictorsR F.⊆ DP.CESByR lk
                     )
                  => ModelConfig b
                  -> RunConfig l
                  -> S.ResultAction CESData (DP.PSData k) S.DataSetGroupIntMaps S.DataSetGroupIntMaps r () (MC.PSMap l MT.ConfidenceInterval, MC2.ModelParameters)
modelResultAction config runConfig = S.UseSummary f where
  f summary _ modelDataAndIndexes_C gqDataAndIndexes_CM = do
    (modelData, _resultIndexesE) <- K.ignoreCacheTime modelDataAndIndexes_C
     -- compute means of predictors because model was zero-centered in them
    let mdMeansFld :: DP.LPredictorsR F.⊆ rs
                   => S.DesignMatrixRow (F.Record DP.LPredictorsR) -> FL.Fold (F.Record rs) [Double]
        mdMeansFld dmr =
          let covariates = S.designMatrixRowF $ contramap F.rcast dmr
              nPredictors = SBB.rowLength dmr
          in FL.premap (VU.toList . covariates)
             $ traverse (\n -> FL.premap (List.!! n) FL.mean) [0..(nPredictors - 1)]
        mdMeansLM :: S.DesignMatrixRow (F.Record DP.LPredictorsR) -> [Double]
        mdMeansLM dmr = FL.fold (FL.premap (F.rcast @DP.LPredictorsR) $ mdMeansFld dmr) $ unCESData modelData
        getVector n = K.knitEither $ S.getVector . fmap CS.mean <$> S.parse1D n (CS.paramStats summary)
        betaSIF :: S.DesignMatrixRow (F.Record DP.LPredictorsR) -> [Double] -> K.Sem r (VU.Vector (Double, Double))
        betaSIF dmr mdMeansL = do
          case SBB.rowLength dmr of
            0 -> pure VU.empty
            _p -> do
              betaV <- getVector "beta"
              pure $ VU.fromList $ zip (V.toList betaV) mdMeansL
    betaSIM <- betaSIF config.mcDesignMatrixRow $ mdMeansLM config.mcDesignMatrixRow
    psMap <- case runConfig.rcPS of
      Nothing -> mempty
      Just (_gtt, pst) -> case gqDataAndIndexes_CM of
        Nothing -> K.knitError "modelResultAction: Expected gq data and indexes but got Nothing."
        Just gqDaI_C -> do
          let getVectorPcts n = K.knitEither $ S.getVector . fmap CS.percents <$> S.parse1D n (CS.paramStats summary)
--              rtt ::  S.RowTypeTag (F.Record (DP.PSDataR k)) = S.RowTypeTag "PSData"
          (_gqData, gqIndexesE) <- K.ignoreCacheTime gqDaI_C
          grpIM <- K.knitEither
             $ gqIndexesE >>= S.getGroupIndex (S.RowTypeTag @(F.Record (DP.PSDataR k)) "PSData") (MC.psGroupTag @l)

          psTByGrpV <- getVectorPcts $ psPrefix pst <> "_byGrp"
          K.knitEither $ M.fromList . zip (IM.elems grpIM) <$> (traverse MT.listToCI $ V.toList psTByGrpV)
    pure $ (MC.PSMap psMap, MC2.ModelParameters betaSIM)

newtype CESData = CESData { unCESData :: F.FrameRec CESByCDR } deriving stock Generic

instance Flat.Flat CESData where
  size (CESData c) n = Flat.size (FS.SFrame c) n
  encode (CESData c) = Flat.encode (FS.SFrame c)
  decode = (\c → CESData (FS.unSFrame c)) <$> Flat.decode

cachedPreppedCES :: (K.KnitEffects r, BRCC.CacheEffects r)
                 => MR.CacheStructure () ()
                 -> CCES.SurveyYear
                 -> K.Sem r (K.ActionWithCacheTime r CESData)
cachedPreppedCES cacheStructure cy = do
  cacheDirE' <- K.knitMaybe "cachedPreppedCES: Empty cacheDir given!" $ BRCC.insureFinalSlashE $ MR.csProjectCacheDirE cacheStructure
  rawCESByCD_C <- cesCountedEvangelicalsByCD False cy
  let cyInt = CCES.cesYear cy
      (srcWindow, cachedSrc) = ACS.acs1Yr2012_22
  acs_C <- fmap (F.filterFrame ((== DT.Citizen) . view DT.citizenC)) <$> (DDP.cachedACSa5ByCD srcWindow cachedSrc (min 2022 cyInt) (Just cyInt)) -- so we get density from closest year as survey
--  K.ignoreCacheTime acs_C >>= BRLC.logFrame . F.filterFrame ((== "MT") . view GT.stateAbbreviation)
  let appendCacheFile :: Text -> Text -> Text
      appendCacheFile t d = d <> t
      cesByCDModelCacheE = bimap (appendCacheFile "CESModelData.bin") (appendCacheFile "CESByCDModelData.bin") cacheDirE'
  cacheKey <- case cesByCDModelCacheE of
    Left ck -> BRCC.clearIfPresentD ck >> pure ck
    Right ck -> pure ck
  let deps = (,) <$> rawCESByCD_C <*> acs_C -- <*> houseElections_C
  BRCC.retrieveOrMakeD cacheKey deps $ \(ces, acs) -> (fmap CESData $ cesAddDensity cy acs ces)

cesAddDensity :: (K.KnitEffects r)
              => CCES.SurveyYear
              -> F.FrameRec DDP.ACSa5ByCDR
              -> F.FrameRec (DP.CDKeyR V.++ DP.DCatsR V.++ CountDataR)
              -> K.Sem r (F.FrameRec CESByCDR)
cesAddDensity cesYr acs ces = K.wrapPrefix "TSP_Religion.Model.cesAddDensity" $ do
  K.logLE K.Info "Adding people-weighted pop density to CES"
  let fixSingleDistricts :: (F.ElemOf rs GT.StateAbbreviation, F.ElemOf rs GT.CongressionalDistrict, Functor f)
                         => f (F.Record rs) -> f (F.Record rs)
      fixSingleDistricts = BR.fixSingleDistricts ("DC" : (BR.atLargeDistrictStates (CCES.cesYear cesYr))) 1
      (joined, missing) = FJ.leftJoinWithMissing @(DP.CDKeyR V.++ DP.DCatsR) ces -- @([GT.StateAbbreviation, GT.CongressionalDistrict] V.++ DP.DCatsR) ces --
                          $ DP.withZeros @DP.CDKeyR @DP.DCatsR
                          $ fmap F.rcast $ fixSingleDistricts acs
  when (not $ null missing) $ do
--    BR.logFrame $ F.filterFrame ((== "DC") . view GT.stateAbbreviation) acs
    K.knitError $ "cesAddDensity: Missing keys in CES/ACS join: " <> show missing
  pure $ fmap F.rcast joined

cesCountedEvangelicalsByCD ∷ (K.KnitEffects r, BRCC.CacheEffects r)
                           => Bool
                           -> CCES.SurveyYear
                           -> K.Sem r (K.ActionWithCacheTime r (F.FrameRec (DP.CDKeyR V.++ DP.DCatsR V.++ CountDataR)))
cesCountedEvangelicalsByCD clearCaches cy = do
  ces_C ← CCES.cesLoader cy
  let cacheKey = "model/TSP_Religion/ces" <> show (CCES.cesYear cy) <> "ByCD.bin"
  when clearCaches $ BRCC.clearIfPresentD cacheKey
  BRCC.retrieveOrMakeFrame cacheKey ces_C $ (fmap (fmap F.rcast) . cesMR @DP.CDKeyR (CCES.cesYear cy))

cesMR ∷ forall lk rs f m .
        (Foldable f, Functor f, Monad m
        , FC.ElemsOf rs [BR.Year, DT.EvangelicalC, DT.EducationC, DT.HispC, DT.Race5C, CCES.CESPostWeight]
        , rs F.⊆ (DT.Education4C ': rs)
        , (lk V.++ DP.DCatsR) V.++ CountDataR ~ ((lk V.++ DP.DCatsR) V.++ CountDataR)
        , Ord (F.Record (lk V.++ DP.DCatsR))
        , (lk V.++ DP.DCatsR) F.⊆ (DT.Education4C ': rs)
        , FI.RecVec ((lk V.++ DP.DCatsR) V.++ CountDataR)
        )
      ⇒ Int -> f (F.Record rs) → m (F.FrameRec (lk V.++ DP.DCatsR V.++ CountDataR))
cesMR earliestYear =
  BRF.frameCompactMR
  (FMR.unpackFilterOnField @BR.Year (>= earliestYear))
  (FMR.assignKeysAndData @(lk V.++ DP.DCatsR) @rs)
  countCESF
  . fmap (DP.cesAddEducation4 . DP.cesRecodeHispanic)

countCESF :: (FC.ElemsOf rs [DT.EvangelicalC, CCES.CESPostWeight])
          => FL.Fold
             (F.Record rs)
             (F.Record CountDataR)
countCESF =
  let wgt = view CCES.cESPostWeight
      evangelical = (== DT.Evangelical) . view DT.evangelicalC
      surveyedF = FL.length
      surveyWgtF = FL.premap wgt FL.sum
      lmvskSurveyedF = FL.premap wgt FLS.fastLMVSK
      essSurveyedF = DP.effSampleSizeFld lmvskSurveyedF
      evangelicalF = FL.prefilter evangelical FL.length
      waEvangelicalF = DP.wgtdAverageBoolFld wgt evangelical
   in (\sw s ev eS wEv →
          sw F.&: s F.&: ev F.&: eS F.&: min eS (eS * wEv) F.&: V.RNil)
      <$> surveyWgtF
      <*> surveyedF
      <*> evangelicalF
      <*> essSurveyedF
      <*> waEvangelicalF
