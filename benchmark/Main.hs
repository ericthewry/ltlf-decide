-- You can benchmark your code quickly and effectively with Criterion. See its
-- website for help: <http://www.serpentine.com/criterion/>.
import Criterion.Main
import Tableau

bchmks :: IO String 
bchmks = do
  
  

main :: IO ()
main = defaultMain [
  bgroup "Tableau Decision Procedure (sat)" [
                                              ],
  bgroup "Tableau Decision Procedure (valid)" [
                                                ]
  ]
