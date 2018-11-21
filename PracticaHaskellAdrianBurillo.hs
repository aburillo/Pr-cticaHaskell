type Var = String -- nombres de variables
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp deriving Read
--Instance
instance Eq FProp where 
 (V x) == (V y) = x==y
 (No x) == (No y) = x==y
 (Y x y) == (Y n m) = (x==n && y==m) || (x==m && y==n)
 (O x y) == (O n m) = (x==n && y==m) || (x==m && y==n)
 (Si x y) == (Si n m) = x==n && y==m
 (Sii x y) == (Sii n m) = (x==n && y==m) || (x==m && y==n)
 x == y = False

instance Ord FProp where
 x <= y = consecuencia x y
 
instance Show FProp where
 show (V x) = x
 show (No x) = "~" ++ show x
 show (Y x y) = "(" ++ show x ++ " /\\ " ++ show y ++ ")"
 show (O x y) = "(" ++ show x ++ "\\/" ++ show y ++ ")"
 show (Si x y) = "(" ++ show x ++ " -> " ++ show y ++ ")"
 show (Sii x y) = "(" ++ show x ++ " <-> " ++ show y ++ ")"

--Funciones para hacer pruebas
f5 = Sii (Y (V "p") (V "q")) (O (No(V "q"))(V "r"))
f3 = Y (V "p") (Y (V "q") (O (No (V "q")) (V "r")))
f2 = Y (V "p") (Si (No(V "q")) (No(V "p")))
f4 = Y (V "p") (No (V "p"))
f1 = Si (No (V "p")) (Si (V "p") (Y (V "q") (No (V "q"))))
--une dos listas de tipo vars y ademas elimina las repeticiones
unionV :: [Var] -> [Var] -> [Var]
unionV [] l = l
unionV (x:xs) l = eliminaRepetidos (x:(unionV xs l)) 

--dada una lista de var elimina las repeticiones, a esta funcion se la llama en unionV
eliminaRepetidos:: [Var] -> [Var] 
eliminaRepetidos []=[]
eliminaRepetidos (x:xs) = x: eliminaRepetidos([i| i<- xs, i/= x])

--Dada una formula nos devuelve una lista con las variables que se utilizan
vars :: FProp -> [Var]
vars (V f)= [f]
vars (Y x y) = unionV (vars x) (vars y)
vars (No x) = vars x
vars (O x y) = unionV (vars x) (vars y)
vars (Si x y) = unionV (vars x) (vars y)
vars (Sii x y) = unionV (vars x) (vars y)
--Dado un entero ( que es el numero de variables )y una lista que es un auxiliar, devuelvo una lista de listas con todas las posibilidades de combinar true y false 
generaCasos :: Int -> [Bool] -> [[Bool]]
generaCasos 0 l = [l]
generaCasos n l= (generaCasos (n-1) (True:l)) ++ (generaCasos (n-1) (False:l))

--Dado un var y una lista de var me busca en que posciom de la lista esta este var y lo devuelve
busca:: Var -> [Var] -> Int ->Int 
busca z (x:xs) n
            | z==x = n
            | otherwise = busca z xs n+1

--esta funcion dada un fprop asigna valores de la lista bool a las variables(de la lista [var]) y comprueba si para esos valores devuelve true o false
tautologiaAux :: FProp -> [Var] -> [Bool] -> Bool
tautologiaAux (V x) v b = b !! (busca x v 0)
tautologiaAux (No x) l m = not (tautologiaAux x l m)
tautologiaAux (Y x y) l m =  (tautologiaAux x l m) && (tautologiaAux y l m)
tautologiaAux (O x y) l m =  (tautologiaAux x l m) || (tautologiaAux y l m)
tautologiaAux (Si x y) l m =  (not (tautologiaAux x l m)) || (tautologiaAux y l m)
tautologiaAux (Sii x y) l m =   ((tautologiaAux x l m) && (tautologiaAux y l m)) || ((not (tautologiaAux x l m)) && (not (tautologiaAux y l m))) 

-- con el numero de variables saco todas las posibilidades llamando a generacasos y mira si para todas las posibilidades el valor es true
-- si alguno fuese false la lista no seria vacia 
tautologia :: FProp -> Bool
tautologia z = ([True |x<- aux, (tautologiaAux z aux2 x)== False] == []) where aux = generaCasos (length(vars (z))) []  
                                                                               aux2 = vars(z)
--hago el mismo proceso que en tautologia pero mira en vez de si es se cumple para todas, si se cumple para algunas
satisfactible :: FProp -> Bool
satisfactible z = ([True |x<- aux, (tautologiaAux z aux2 x)== True] /= []) where aux = generaCasos (length(vars (z))) []
                                                                                 aux2 = vars(z)
-- Dadas 2 Fprop comprueba si y es consecuencia de x, es decir si la segunda en introducir es consecuencia de la primera(uso tautologia)																				 
consecuencia :: FProp -> FProp -> Bool
consecuencia x y = tautologia (Si x y)

--Comruebo si 2 fprop son equivalentes(uso tautologia)
equivalencia:: FProp -> FProp -> Bool
equivalencia x y =  tautologia (Sii x y)																			 

--llama a un auxiliar consecuenciasAus que es el que procesa la lista de funciones
consecuencias :: [FProp] -> [[FProp]]
consecuencias x = consecuenciasAux x x
--me llegan 2 listas de fprop la primera es la que proceso la segunda es constante en toda la funcion.
--Esta funcion crea una lista delistas de funciones, ya que para cada funcion crea una lista con las que son consecuencia
consecuenciasAux :: [FProp] -> [FProp] -> [[FProp]]
consecuenciasAux [] ys  = []
consecuenciasAux (x:xs) ys = ([y| y <- ys, consecuencia y x]):(consecuenciasAux xs ys)

--crea una lista de listas de funciones sin repeticiones de las funciones que son equivalentes
equivalencias :: [FProp] -> [[FProp]]
equivalencias x = separa (equivalenciasAux x x)

--realiza lo mismo que consecuenciasAux pero comprobando si las funciones de las que creo la lista son equivalentes y no consecuentes
equivalenciasAux :: [FProp] -> [FProp] -> [[FProp]]
equivalenciasAux [] ys  = []
equivalenciasAux (x:xs) ys = ([y| y <- ys, equivalencia y x]):(equivalenciasAux xs ys) 	   

--elimina listas repetidas dentro de la lista de listas de fprop
separa :: [[FProp]] -> [[FProp]]
separa [] = []
separa (x:xs) = x:separa([y|y <- xs, not (elem (head x) y)])

--recoge una funcion y nos muestra sus variables
varsIO:: IO()
varsIO = do
            putStrLn ("Dime la formula de la que quieras saber sus variables")
            var <- getLine
            print (vars (read var))
--recoge una funcion y nos dice si es tautologia
tautologiaIO :: IO()
tautologiaIO = do
            putStrLn ("Dime la formula que quieres comprobar")
            tauto <- getLine
            print (tautologia (read tauto))
--recoge una funcion y nos dice si es satisfactible
satisfactibleIO :: IO()
satisfactibleIO = do
            putStrLn ("Dime la formula que quieres comprobar")
            satis <- getLine
            print (satisfactible (read satis))
			
--recoge dos funciones y nos dice si la segunda es consecuencia de la primera
consecuenciaIO :: IO()
consecuenciaIO = do
            putStrLn ("Dime la formula consecuente")
            cons1 <- getLine
            putStrLn ("Dime la formula consecuencia")
            cons2 <- getLine
            print (consecuencia (read cons1) (read cons2))
			
--recoge 2 funciones y nos dice si son equivalentes
equivalenciaIO :: IO()
equivalenciaIO = do
            putStrLn ("Dime las 2 formulas que quieres comprobar si son equivalentes")
            cons1 <- getLine
            cons2 <- getLine
            print (equivalencia (read cons1) (read cons2))
--llama a metefunciones que le devuelve una lista de string que cada string es una funcion,lo trasformo a Fprop y llamo a consecuencias
consecuenciasIO :: IO()
consecuenciasIO = do
            p<-metefunciones
            print (consecuencias (map read p))

--lama a metefunciones que le devuelve una lista de string que cada string es una funcion,lo trasformo a Fprop y llamo a equivalencias
equivalenciasIO :: IO()
equivalenciasIO = do
            p<-metefunciones
            print (equivalencias (map read p))

--funcion recursiva que guarda string(que son funciones) hasta que el usuario quiera introducir y devuelve una lista de string que luego ser trasformada a fprop
metefunciones :: IO [String]
metefunciones = do
             putStrLn ("Deseas introducir funcion?(si/no)")
             cons1 <- getLine
             if cons1== "si" then do cons2<-getLine
                                     q <- metefunciones
                                     return( (cons2 : q))
                             else return ([])
--Esta es la funcion principal de entrada y salida que llama a todas las funciones definidas anteriormente de entrada salida
main = do
    putStrLn "Buenas ,puedes introducir los siguientes comandos para realizar distintas acciones ->"
    putStrLn "vars , tautologia, satisfactible,consecuencia, equivalencia , consecuencias, equivalencias, o cualquier otra cosa para salir"
    name <- getLine
    if name == "tautologia" then do tautologiaIO
                                    main
                            else if name=="satisfactible" then do satisfactibleIO
                                                                  main
                                                          else if name == "consecuencia" then do consecuenciaIO
                                                                                                 main
                                                                                         else if name=="equivalencia" then do equivalenciaIO
                                                                                                                              main
                                                                                                                      else if name == "consecuencias" then do consecuenciasIO
                                                                                                                                                              main
                                                                                                                                                      else if name == "equivalencias" then do equivalenciasIO
                                                                                                                                                                                              main
                                                                                                                                                                                      else if name == "vars" then do varsIO
                                                                                                                                                                                                                     main
                                                                                                                                                                                                             else putStrLn "adios"