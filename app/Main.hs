module Main (main) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.State
import Data.Dependent.Sum
import Data.Functor
import Data.Functor.Const
import Data.Functor.Identity (Identity (Identity))
import Data.IntMap qualified as IM
import Data.Map
import Data.Map qualified as Map
import Data.Some
import Data.These
import Reflex
import Reflex.Host.Headless
import Reflex.Requester.Base.Internal
import Text.Read (Lexeme (Ident))
import Unsafe.Coerce

main :: IO ()
main = do
  runHeadlessApp app
  pure ()

app :: forall t m. (MonadHeadlessApp t m) => m (Event t ())
app = mdo
  ePostBuild <- getPostBuild

  rec (_, eRequest) <-
        runRequesterT
          ( do
              eX <-
                switchHold never
                  =<< requestingIdentity
                    ( ePostBuild
                        $> Const (PatchIntMap $ IM.singleton 1 (Just "1"))
                    )
              performEvent $ ffor eX (const $ pure ())
              pure ()
          )
          eResponse'
      (eRequest', eResponse') <-
        matchResponseMapWithRequests'
          (\x -> (mkSome x, \case Some x' -> unsafeCoerce x'))
          eRequest
          eResponse
      eResponse <- pure $ ffor eRequest' $ fmap (\x -> Some (Identity ()))
  pure never

matchResponseMapWithRequests' ::
  forall t rawRequest rawResponse request response m.
  ( MonadFix m,
    MonadHold t m,
    Reflex t
  ) =>
  -- | Given a request (from 'Requester'), produces the wire format of the
  -- request and a function used to process the associated response
  (forall a. request a -> (rawRequest, rawResponse -> response a)) ->
  -- | The outgoing requests
  Event t (RequesterData request) ->
  -- | A map of incoming responses, tagged by an identifying key
  Event t (Map Int rawResponse) ->
  -- | A map of outgoing wire-format requests and an event of responses keyed
  -- by the 'RequesterData' key of the associated outgoing request
  m
    ( Event t (Map Int rawRequest),
      Event t (RequesterData response)
    )
matchResponseMapWithRequests' f send recv = do
  rec nextId <- hold 1 $ fmap (\(next, _, _) -> next) outgoing
      waitingFor :: Incremental t (PatchMap Int (Decoder rawResponse response)) <-
        holdIncremental mempty $
          alignEventWithMaybe
            ( \case
                These x y -> pure $ x <> y
                This x -> pure x
                That x -> pure x
            )
            outstanding
            (snd <$> incoming)
      let outgoing = processOutgoing nextId send
          incoming = processIncoming waitingFor outstanding recv
          outstanding = fmap (\(_, outstanding, _) -> outstanding) outgoing
  return (fmap (\(_, _, rawReqs) -> rawReqs) outgoing, fst <$> incoming)
  where
    processOutgoing ::
      Behavior t Int ->
      -- The next available key
      Event t (RequesterData request) ->
      -- The outgoing request
      Event
        t
        ( Int,
          PatchMap Int (Decoder rawResponse response),
          Map Int rawRequest
        )
    -- The new next-available-key, a map of requests expecting responses, and the tagged raw requests
    processOutgoing nextId out = flip pushAlways out $ \dm -> do
      oldNextId <- sample nextId
      let (result, newNextId) = flip runState oldNextId $
            forM (requesterDataToList dm) $ \(k :=> v) -> do
              n <- get
              put $ succ n
              let (rawReq, rspF) = f v
              return (n, rawReq, Decoder k rspF)
          patchWaitingFor =
            PatchMap $
              Map.fromList $
                (\(n, _, dec) -> (n, Just dec)) <$> result
          toSend = Map.fromList $ (\(n, rawReq, _) -> (n, rawReq)) <$> result
      return (newNextId, patchWaitingFor, toSend)
    -- Looks up the each incoming raw response in a map of response
    -- decoders and returns the decoded response and a patch that can
    -- be used to clear the ID of the consumed response out of the queue
    -- of expected responses.
    processIncoming ::
      Incremental t (PatchMap Int (Decoder rawResponse response)) ->
      -- A map of outstanding expected responses
      Event t (PatchMap Int (Decoder rawResponse response)) ->
      -- A map of response decoders for prompt responses
      Event t (Map Int rawResponse) ->
      -- A incoming response paired with its identifying key
      Event t (RequesterData response, PatchMap Int v)
    -- The decoded response and a patch that clears the outstanding responses queue
    processIncoming waitingFor outstanding inc = flip push (alignEventWithMaybe thatMaybe inc outstanding) $ \(rspMap, promptRspMap) -> do
      wf' <- sample $ currentIncremental waitingFor
      -- This is where the error comes from
      let wf = maybe id applyAlways promptRspMap wf'
      -- Commenting out the above line and uncommenting the below line makes the error go away
      -- let wf = wf'
      let match rawRsp (Decoder k rspF) =
            let rsp = rspF rawRsp
             in singletonRequesterData k rsp
          matches = Map.intersectionWith match rspMap wf
      pure $
        if Map.null matches
          then Nothing
          else
            Just
              (Map.foldl' mergeRequesterData emptyRequesterData matches, PatchMap $ Nothing <$ matches)
    thatMaybe :: These a b -> Maybe (a, Maybe b)
    thatMaybe = \case
      This x -> Just (x, Nothing)
      That x -> Nothing
      These x y -> Just (x, Just y)
