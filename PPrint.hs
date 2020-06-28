module PPrint where

writeln :: String -> IO ()
writeln = putStrLn

showsPair :: Show a => (String, a) -> ShowS
showsPair (k,v) = (k ++) . (": " ++) . shows v

pprH, pprV :: [ShowS] -> ShowS
pprV = intercalateS ('\n':)
pprH = intercalateS (' ':)

intercalateS :: ShowS -> [ShowS] -> ShowS
intercalateS sep (x:xs) = x . foldr ((.) . (sep .)) id xs

pprListWith :: (a -> ShowS) -> [a] -> ShowS
pprListWith f = pprV . map f

runShows :: ShowS -> IO ()
runShows = putStrLn . ($"")
