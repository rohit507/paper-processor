module Main where

import Intro
import Development.Shake
import Data.Csv
import Text.HTML.Scalpel
import Network.HTTP.Conduit

main :: IO ()
main = putStrLn "Hello World!"

{-

Goals:

  open-pdfs and scrape for
    title, authors, venue, citations
  use google scholar to
    generate bibtex citations
    get reference count
  generate taglist
    attempt to assign tags if possible
  build
    map of 2nd order references, w/ most cited getting stuff out
  use sql-lite DB for content?

use grobid and cervine for parsing

do we use a stack based model?

What I want is a model where it grabs things from one pool and generates a
potential match csv for the entire metadata pool

well all the potential output csvs.



-}
