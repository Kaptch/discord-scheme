{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Main where

import           Calamity
import           Calamity.Cache.InMemory   (runCacheInMemory)
import           Calamity.Commands
import qualified Calamity.Commands.Context as CommandContext
import           Calamity.Gateway.Types    as G (StatusUpdateData (..))
import           Calamity.Metrics.Noop     (runMetricsNoop)
import           Control.Lens
import           Control.Monad
import           Data.Text.Lazy            as L
import qualified DiPolysemy                as DiP
import qualified Polysemy                  as P
import qualified Polysemy.Async            as P
import qualified Polysemy.AtomicState      as P
import qualified Polysemy.Embed            as P
import qualified Polysemy.Fail             as P
import           System.Environment        (getEnv)
import           TextShow

info :: BotC r => Text -> P.Sem r ()
info = DiP.info

tellt :: (BotC r, Tellable t) => t -> Text -> P.Sem r (Either RestError Message)
tellt t m = tell t $ L.toStrict m

main :: IO ()
main = do
  token <- L.pack <$> getEnv "BOT_TOKEN"
  void . P.runFinal
    . P.embedToFinal
    . runCacheInMemory
    . runMetricsNoop
    . useConstantPrefix "!"
    . runBotIO (BotToken token)
    $ do
        addCommands $ do
          helpCommand

          command @'[User] "duginize" $ \ctx u -> do
            case (view #guild ctx) of
              Nothing -> pure ()
              Just g -> void
                $ invoke
                $ ModifyGuildMember g u
                $ ModifyGuildMemberData (Just "AAA") Nothing Nothing Nothing Nothing

          command @'[] "test" $ \ctx -> do
            void . tellt ctx $ "test"

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
