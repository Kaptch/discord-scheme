{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedLabels     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import           Calamity
import           Calamity.Cache.InMemory   (runCacheInMemory)
import           Calamity.Commands
import qualified Calamity.Commands.Context as CommandContext
import           Calamity.Commands.Command (Command)
import           Calamity.Commands.CommandUtils (TypedCommandC, CommandForParsers)
import           Calamity.Gateway.Types    as G (StatusUpdateData (..))
import           Calamity.HTTP.Internal.Types (RestError (..))
import           Calamity.Metrics.Noop     (runMetricsNoop)
import qualified Calamity.Types.Model.Guild.Member as TM
import           Control.Lens              hiding (Context, List, cons, noneOf)
import           Control.Monad
import           Control.Monad.Except
import qualified Data.Char                 as DC
import           Data.Flags
import           Data.Hashable
import qualified Data.HashMap              as HM
import qualified Data.List                 as DL
import           Data.Maybe
import qualified Data.Text.Lazy            as L
import qualified Data.Text                 as S
import           Data.Typeable
import qualified Data.Vector               as V
import           Debug.Trace
import qualified Di
import qualified DiPolysemy                as DiP
import           GHC.Conc
import           Numeric                   (readHex)
import qualified Polysemy                  as P
import qualified Polysemy.AtomicState      as P
import qualified Polysemy.Embed            as P
import qualified Polysemy.Error            as P
import qualified Polysemy.Reader           as P
import qualified Polysemy.State            as P
import qualified Polysemy.Async            as P
import           System.Environment        (getEnv)
import qualified System.Random             as R
import           Scheme
import           TextShow
import           Text.Parsec               as PA
import           Text.ParserCombinators.Parsec as PA hiding (try)
import           Text.Parsec.Language      as PA
import qualified Text.Parsec.Token         as PA
import           Calamity.Types.LogEff
import           Calamity.Metrics.Eff
import           Calamity.Cache.Eff

instance {-# OVERLAPS #-} HasID' a => Hashable a where
  hashWithSalt salt x = hashWithSalt salt ((getID :: a -> Snowflake a) x)

instance {-# OVERLAPS #-} (Eq a, HasID' a) => Ord a where
  compare x y = compare ((getID :: a -> Snowflake a) x) ((getID :: a -> Snowflake a) y)
  (<=) x y = ((getID :: a -> Snowflake a) x) <= ((getID :: a -> Snowflake a) y)

instance TextShow a => TextShow (V.Vector a) where
  showb = showbVecWith showb
    where
      showbVecWith :: (a -> Builder) -> V.Vector a -> Builder
      showbVecWith showbx v
        | V.null v = "{}"
        | otherwise = TextShow.singleton '{' <> showbx (V.head v) <> go (V.tail v)
        where
          go v'
            | V.null v' = TextShow.singleton '}'
            | otherwise = TextShow.singleton ',' <> showbx (V.head v') <> go (V.tail v')
  showbPrec _ = showb

instance TextShow RestError where
  showb (HTTPError status response) = "HTTPError " <> showb status <> " " <> (fromString $ show response)
  showb (InternalClientError t) = "InternalClientError " <> fromLazyText t
  showbPrec _ = showb

data GlobalState = GlobalState
  {
    _roleNamesPool :: HM.Map Guild (V.Vector S.Text)
  , _schemeRT :: HM.Map Guild (Continuation (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)])
                              , Environment (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)]))
  }

makeLenses ''GlobalState

removeElem :: V.Vector a -> Int -> V.Vector a
removeElem v i = V.backpermute v (V.fromList ([0..i-1] ++
                                               [(V.length v - 1)] ++
                                               [i+1..(V.length v - 2)]))

info :: BotC r => L.Text -> P.Sem r ()
info = DiP.info
  
tellt :: (BotC r, Tellable t) => t -> L.Text -> P.Sem r (Either RestError Message)
tellt t m = tell t $ L.toStrict m

rollIndex :: P.Member (P.Embed IO) r => Int -> P.Sem r Int
rollIndex x = P.embed $ R.getStdRandom (R.randomR (0, x))

checkPermissionsAct :: BotC r => Permissions -> Context -> P.Sem r () -> P.Sem r ()
checkPermissionsAct perms ctx act = do
  case (view #guild ctx) of
    Nothing -> pure ()
    Just g -> do
      p <- permissionsIn' g (view #user ctx)
      case (containsSome p perms) of
        False -> void . tellt ctx $ "Not permitted"
        True -> act

inGuildAct :: BotC r => Context -> (Guild -> P.Sem r ()) -> P.Sem r ()
inGuildAct ctx act = case (view #guild ctx) of
                       Nothing -> pure ()
                       Just g -> act g

getUsers' :: SchemeC' (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)]) r =>
  [SchemeValue (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)])] ->
  P.Sem r (SchemeValue (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)]))
getUsers' [] = do
  g <- fst <$> (P.embed P.ask)
  res <- P.embed (invoke $ ListGuildMembers g (ListMembersOptions (Just (toInteger $ memberCount g)) Nothing))
  case res of
    Left err -> P.throw $ Default "Internal error"
    Right res' -> pure $ List (map (String . show . TM.username) res')
getUsers' args = P.throw $ NumArgs (Just 0) args

printInChannel :: SchemeC' (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)]) r =>
  [SchemeValue (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)])] ->
  P.Sem r (SchemeValue (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)]))
printInChannel ([String s]) = do
  c <- snd <$> (P.embed P.ask)
  P.embed (tell @String c s)
  pure $ List []
printInChannel args = P.throw $ NumArgs (Just 1) args

discordStd :: SchemeC' (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)]) r =>
  [(String, SchemeValue (P.Sem '[LogEff, MetricEff, CacheEff, P.Reader Client, P.AtomicState EventHandlers, P.Embed IO, P.Final IO, P.Async, P.Reader (Guild, Channel)]))]
discordStd = [("users", PrimitiveFunc getUsers'), ("print", PrimitiveFunc printInChannel)]

main :: IO ()
main = do
  token <- L.pack <$> getEnv "BOT_TOKEN"
  glSt <- newTVarIO (GlobalState HM.empty HM.empty)
  Di.new $
    \di -> void
    . P.runFinal
    . P.embedToFinal
    . P.runAtomicStateTVar glSt
    . runCacheInMemory
    . runMetricsNoop
    . useConstantPrefix "!"
    . DiP.runDiToIO di
    . runBotIO (BotToken token) (andFlags defaultIntents intentGuildMembers)
    $ do
        addCommands $ do
          helpCommand

          group "misc" $ do
            command @'[User] "mute-user" $
              \ctx u -> inGuildAct ctx $
                      \g -> checkPermissionsAct muteMembers ctx $ do
                        void
                          $ invoke
                          $ ModifyGuildMember g u
                          $ modifyGuildMemberMute (Just True)

          group "scm" $ do
            command @'[] "new-env" $
              \ctx -> inGuildAct ctx $
              \g -> P.runReader (g, view #channel ctx) $ P.atomicModify (\s -> over schemeRT (HM.alter (maybe (Just (nullC, (extendEnv stdEnv discordStd))) (const $ Just (nullC, (extendEnv stdEnv discordStd)))) g) s)
            command @'[[L.Text]] "parse" $
              \ctx t -> inGuildAct ctx $
              \g -> void . tellt ctx $ L.pack $ show (readExpr (L.unpack (L.unwords t)))
            command @'[[L.Text]] "eval" $
              \ctx t -> inGuildAct ctx $
              \g -> do
                st <- P.atomicGets (view schemeRT)
                r <- P.runReader (g, view #channel ctx) $ P.subsume_ $ case (readExpr (L.unpack (L.unwords t))) of
                           Left err -> do
                             void . tellt ctx $ L.pack $ show err
                             pure Nothing
                           Right val -> case (HM.lookup g st) of
                             Nothing -> pure Nothing
                             Just st -> do
                               (cont, (env, res)) <- evalScheme' (fst st) (snd st) val
                               case res of
                                 Left err -> do
                                   void . tellt ctx $ L.pack $ show err
                                   pure Nothing
                                 Right res' -> do
                                   void . tellt ctx $ L.pack $ show res'
                                   pure $ Just (cont, env, res)
                case r of
                  Nothing -> pure ()
                  Just (cont, env, res) -> do
                    P.atomicModify (\s -> over schemeRT (HM.alter (maybe Nothing (const $ Just (cont, env))) g) s)
            command @'[] "print-env" $
              \ctx -> inGuildAct ctx $
              \g -> do
                env <- P.atomicGets (view schemeRT)
                void . tellt ctx $ L.pack $ show (HM.lookup g env)

          group "role-management" $ do
            command @'[Role] "rename-role" $
              \ctx r -> inGuildAct ctx $
              \g -> checkPermissionsAct manageRoles ctx $ do
                hm <- P.atomicGets (view roleNamesPool)
                case (HM.lookup g hm) of
                  Nothing -> pure ()
                  Just vec -> do
                    rand <- rollIndex ((V.length vec) - 1)
                    let role = vec V.! rand
                    resp <- invoke
                            $ ModifyGuildRole g r
                            $ modifyGuildRoleName (Just $ role)
                    either (const $ pure ())
                      (const $
                        P.atomicModify (\s -> over roleNamesPool
                                              (HM.insert g $
                                                removeElem vec rand) s))
                      resp
            command @'[] "rename-roles" $
              \ctx -> inGuildAct ctx $
              \g -> checkPermissionsAct manageRoles ctx $ do
                hm <- P.atomicGets (view roleNamesPool)
                case (HM.lookup g hm) of
                  Nothing -> pure ()
                  Just vec -> do
                    roles <- invoke $ GetGuildRoles g
                    case roles of
                      Left err -> void . tellt ctx $ showtl err
                      Right roles' -> mapM_ act roles'
                        where
                          act role' = do
                            rand <- rollIndex ((V.length vec) - 1)
                            let role = vec V.! rand
                            resp <- invoke
                                    $ ModifyGuildRole g role'
                                    $ modifyGuildRoleName (Just $ role)
                            either (const $ pure ())
                              (const $
                                P.atomicModify (\s -> over roleNamesPool
                                                 (HM.insert g $
                                                  removeElem vec rand) s))
                              resp          
            command @'[[L.Text]] "append-roles" $
              \ctx t -> inGuildAct ctx $
              \g -> checkPermissionsAct manageRoles ctx $ do
                let t' = map L.toStrict t
                P.atomicModify (\s -> over roleNamesPool
                                      (HM.alter (maybe (Just $ V.fromList t') (\x -> Just $ x V.++ (V.fromList t'))) g)
                                      s)
            command @'[] "show-role-pool" $
              \ctx -> inGuildAct ctx $
              \g -> do
                glSt <- P.atomicGet
                void . tellt ctx $ showtl $ HM.lookup g $ view roleNamesPool glSt
            command @'[] "flush-role-pool" $
              \ctx -> inGuildAct ctx $
              \g -> P.atomicModify (\s -> over roleNamesPool (HM.alter (maybe Nothing (const Nothing)) g) s)

          group "test" $ do
            command @'[] "test" $
              \ctx -> do
                void . tellt ctx $ "test"
            command @'[[L.Text]] "echo" $
              \ctx t -> do
                void . tell @String ctx $ (L.unpack (L.unwords t))
            command @'[] "users" $
              \ctx -> inGuildAct ctx $
              \g -> do
                res <- invoke $ ListGuildMembers g (ListMembersOptions (Just (toInteger $ memberCount g)) Nothing)
                case res of
                  Left err -> pure ()
                  Right res' -> void . tell @String ctx $ show (map TM.username res')

        react @'MessageCreateEvt $ \msg ->
          info $ "Got message: " <> showtl msg

        react @'ReadyEvt $ \_ -> do
          sendPresence
            G.StatusUpdateData
              {
                G.since = Nothing,
                G.game = Just $ activity "Prefix: !" Game,
                G.status = "online",
                G.afk = False
              }

        react @('CustomEvt "command-error" (CommandContext.Context, CommandError)) $
          \(ctx, e) -> do
            info $ "Command failed with reason: " <> showtl e
            case e of
              ParseError n r ->
                void . tellt ctx $ "Failed to parse parameter: `"
                  <> L.fromStrict n
                  <> "`, with reason: ```\n"
                  <> r
                  <> "```"
