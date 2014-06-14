import System.Directory
import System.Environment
import System.FilePath
import System.Posix.Directory
import System.Posix.Files
import System.IO.Error
import Foreign.C.Error

enoent::Bool->String -> IO ()
enoent fix path = do
        putStrLn $ "find: `"++(fixPath fix path)++"': No such file or directory"
     
enotdir::Bool->String -> IO ()
enotdir fix path = do
    putStrLn $ "find: `"++(fixPath fix path)++"': Not a directory"

fixPath::Bool->String->String
fixPath fix path = if fix && (take 2 path == "./") then drop 2 path else path
    
printPath::Bool->String -> IO ()
printPath fix path = do
        putStrLn $ fixPath fix path
        
checkPath::String->String
checkPath dir = if null dir then dir else if last dir == '/' then dir else dir++"/"

impl::Bool->String->String->IO()
impl fix prefix name = do
    let fullName = prefix++name
    let cwdName = if null name then "." else name
    e <- tryIOError $ getSymbolicLinkStatus cwdName
    case e of
         Left ex -> enoent fix fullName
         Right fs -> do
             printPath fix fullName
             if not (isSymbolicLink fs) && (isDirectory fs) then do
                 content <- getDirectoryContents cwdName
                 mapM_ (impl fix prefix) (map (\a -> checkPath name ++ a)  (filter (\a -> (a/="." && a/="..")) content))
                                                            else return ()

main:: IO()
main = do
        [path] <- getArgs
        let (dir,name) = splitFileName path
        let fix = (take 2 path /= "./") && (take 1 path /= "/")
        e <- tryIOError $ changeWorkingDirectory dir
        case e of
             Left ex -> do
--                  putStrLn $ show e
                 errno <- getErrno
                 if errno == eNOTDIR then enotdir fix path else return ()
                 if errno == eNOENT then enoent fix path else return ()
             Right _ -> impl fix dir name
