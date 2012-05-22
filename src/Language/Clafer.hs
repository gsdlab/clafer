
module Language.Clafer (
                        myLexer,  -- don't want to export (addFragment)
                        resolveLayout,-- don't want to export (addFragment)
                        resLayout, -- don't want to export (addFragment)
                        desugarModule,-- don't want to export (addFragment)
                        findDupModule,-- don't want to export 
                        allUnique,-- don't want to export 
                        resolveModule,-- don't want to export 
                        transModule,-- don't want to export 
                        optimizeModule,-- don't want to export 
                        genModule,-- don't want to export 
                        genXmlModule,-- don't want to export 
                        sugarModule,-- don't want to export 
                        Print, 
                        printTree, 
                        Token,
                        pModule,
                        astrModule,-- don't want to export 
                        Module,
                        claferIRXSD,
						mapModule,
                        module Front.ErrM,
                        module Generator.Stats,
                        module ClaferArgs,
                        module Common                        
) where

import Common
import Front.ErrM
import ClaferArgs
import Front.Lexclafer
import Front.Parclafer
import Front.Printclafer
import Front.Absclafer hiding (Clafer)
import Front.LayoutResolver
import Front.Mapper
import Intermediate.Desugarer
import Intermediate.Resolver
import Intermediate.StringAnalyzer
import Intermediate.Transformer
import Optimizer.Optimizer
import Generator.Alloy
import Generator.Xml
import Generator.Schema
import Generator.Stats

claferIRXSD :: [Char]
claferIRXSD = Generator.Schema.xsd