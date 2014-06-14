import System.Environment
import System.Posix.Files

enofileordir path = do
	putStrLn "find: `"++path++"': No such file or directory"

printPath path = do
	putStrLn path

checkSlash path = if last path == '/' then path else path++"/"

handleFileOfDirectory path = do
	fs <- getSymbolicLinkStatus path
	if isSymbolicLink fs then printPath path else
		if isDirectory fs then handleDirectory (checkSlash path)


handleDirectory path;

main:: IO()
main = do
	[path] <- getArgs
	if null path then enofileordir path else
		case last path of
			'/' -> handleDirectory path
			otherwise -> handleFileOfDirectory path
