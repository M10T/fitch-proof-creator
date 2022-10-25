{-# LANGUAGE OverloadedStrings #-}
module Main (Main.main) where

import Lib
import Happstack.Server
    ( Response, ServerPart, Method(POST)
    , BodyPolicy(..), decodeBody, defaultBodyPolicy
    , dir, look, nullConf, ok, simpleHTTP
    , toResponse, methodM, body
    )
import Control.Monad (msum)
import qualified Text.Blaze.Html5 as H
import Text.Blaze.Html5 ((!))
import qualified Text.Blaze.Html5.Attributes as A
import Happstack.Server ( Browsing(EnableBrowsing), nullConf
                        , serveDirectory, simpleHTTP
                        )
import Happstack.Server.RqData (RqData, look, getDataFn, lookTexts)
import Data.Char (isSpace)




appTemplate :: String -> H.Html -> H.Html
appTemplate title body =
    H.html $ do
      H.head $ do
        H.title (H.toHtml title)
        H.meta ! A.httpEquiv "Content-Type"
               ! A.content "text/html;charset=utf-8"
        H.script ! A.src "https://ajax.googleapis.com/ajax/libs/jquery/2.1.3/jquery.min.js" $ ""
        H.script ! A.src "/static/premise_script.js" $ ""
      H.body $ do
        body

serverResp :: ServerPart Response
serverResp = ok $ toResponse $ appTemplate "Fitch Proof Creator"
                (do
                    H.h2 $ "Proof Parameters:"
                    H.form ! A.id "premise_form" 
                           ! A.target "proof_loc" 
                           ! A.method "POST"
                           ! A.action "/proof" $ do 
                        H.label "Premise: " >> H.input ! A.type_ "text"
                                                       ! A.name "premise"
                        H.br
                        H.label ! A.id "lResult" $ "Result: " >> H.input ! A.id "result" 
                                                                         ! A.type_ "text" 
                                                                         ! A.name "result"
                        H.br ! A.class_ "submit"
                        H.button  $ "Submit"
                    H.button ! A.onclick "add_premise()" $ "Add Premise"
                    H.button ! A.onclick "remove_premise()" $ "Remove Premise"
                    H.br ! A.class_ "submit "
                    H.br ! A.class_ "submit"
                    H.h2 "Proof:"
                    H.iframe ! A.name "proof_loc" ! A.width "500" ! A.height "400" $ ""
                )

formResp :: ServerPart Response
formResp = 
    do methodM POST
       decodeBody (defaultBodyPolicy "/tmp/" 0 1000 1000)
       premises0 <- body $ lookTexts "premise" 
       let premises = filter (not . null . (dropWhile isSpace)) $ map (tail . init . show) premises0
       result <- body $ look "result"
       let exprPremises = map (f . tail . init . show) premises
       let exprResult = (f . tail . init . show) result 
       let proof = safeTransformProof (proofGiven exprPremises) exprResult
       let res = disp proof
       ok $ toResponse $ H.div (foldl (>>) (head res) (tail res))
    where f = (read::(String->Expression))
          line "" = H.br
          line s = H.p $ H.toHtml s
          disp :: Maybe FitchProof -> [H.Html]
          disp (Just x) = map line ((proofToLines . optimize) x)
          disp (Nothing) = []

main :: IO ()
main = simpleHTTP nullConf $ msum 
    [
        dir "index" $ serverResp,
        dir "static" $ serveDirectory EnableBrowsing [] "./scripts",
        dir "proof" $ formResp
    ]