{-# LANGUAGE OverloadedStrings #-}
module Main (Main.main) where

import Lib
import Happstack.Server (ok, toResponse, simpleHTTP, nullConf, ServerPart, Response, dir)
import Control.Monad (msum)
import qualified Text.Blaze.Html5 as H
import Text.Blaze.Html5 ((!))
import qualified Text.Blaze.Html5.Attributes as A

appTemplate :: String -> H.Html -> H.Html
appTemplate title body =
    H.html $ do
      H.head $ do
        H.title (H.toHtml title)
        H.meta ! A.httpEquiv "Content-Type"
               ! A.content "text/html;charset=utf-8"
        H.script ! A.src "https://ajax.googleapis.com/ajax/libs/jquery/2.1.3/jquery.min.js" $ ""
      H.body $ do
        body

serverResp :: ServerPart Response
serverResp = ok $ toResponse $ appTemplate "Fitch Proof Creator"
                (do
                    H.h2 $ "Proof Parameters:"
                    H.form ! A.id "premise_form" 
                           ! A.target "" $ do 
                        H.label "Premise: " >> H.input ! A.type_ "text"
                                                       ! A.name "premise"
                        H.br ! A.id "submit"
                        H.button  $ "Submit"
                    H.button ! A.onclick "add_premise()" $ "Add Premise"
                    H.button ! A.onclick "remove_premise()" $ "Remove Premise"
                    H.br
                    H.br
                    H.h2 "Proof:"
                    H.iframe ! A.name "proof_loc" $ ""
                    H.script $ H.toHtml scriptJs
                )

scriptJs:: String
scriptJs = "\n\
    \function add_premise() {\n\
    \   const form = document.getElementById(\"premise_form\")\n\
    \   const button = document.getElementById(\"submit\")\n\
    \   const newInput = document.createElement(\"input\")\n\
    \   newInput.type = \"text\"\n\
    \   newInput.name = \"premise\"\n\
    \   const newLabel = document.createElement(\"label\")\n\
    \   newLabel.innerHTML = \"Premise: \"\n\
    \   form.insertBefore(document.createElement(\"br\"),button)\n\
    \   form.insertBefore(newLabel,button)\n\
    \   form.insertBefore(newInput,button)\n\
    \}\n\
    \function remove_premise() {\n\
    \   if ($('input').size() <= 1) return;\n\
    \   $(\"input\").last().remove()\n\
    \   $(\"label\").last().remove()\n\
    \   $(\"br:not(#submit)\").last().remove()\n\
    \}"

main :: IO ()
main = simpleHTTP nullConf $ msum 
    [dir "index" $ serverResp]