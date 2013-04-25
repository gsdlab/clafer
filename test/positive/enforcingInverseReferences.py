from ast import Module
from ast import GCard
from ast import Supers
from ast import Clafer
from ast import Exp
from ast import Declaration
from ast import LocalDeclaration
from ast import Constraint
from ast import FunExp
from ast import ClaferId
from ast import DeclPExp
from ast import Goal

def getModule():
	stack = []
	module = Module.Module("")
	stack.append(module)
##### clafer #####
	pos=((1,1), (3,36))
	isAbstract=True
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="Book"
	uid="c1_Book"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((2,9), (3,36))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="author"
	uid="c2_author"
	my_supers = Supers.Supers(isOverlapping=True, elements=[
		Exp.Exp(expType="Super", , parentId="", pos=((2,19), (2,25)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c17_Author", isTop=True)])])
	card=(1,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="Boolean", parentId="c3_exp", pos=((3,19), (3,36)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="in", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c4_exp", pos=((3,19), (3,23)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="parent", isTop=True)])])]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c5_exp", pos=((3,27), (3,36)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c6_exp", pos=((3,27), (3,31)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c7_exp", pos=((3,32), (3,36)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c18_book", isTop=False)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])])])])])]))
	stack[-1].addElement(constraint)
	stack.pop()
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="Boolean", parentId="c8_exp", pos=((0,0), (0,0)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="All", declaration=
		Declaration.Declaration(isDisjunct=True, localDeclarations=[LocalDeclaration.LocalDeclaration("x"), LocalDeclaration.LocalDeclaration("y")],  body=
		Exp.Exp(expType="Body", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c2_author", isTop=False)])])])),bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="Boolean", parentId="c10_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="!=", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c11_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c12_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="x", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c13_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c14_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c15_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="y", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c16_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])]))]))
	stack[-1].addElement(constraint)
	stack.pop()
##### clafer #####
	pos=((5,1), (7,40))
	isAbstract=True
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="Author"
	uid="c17_Author"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((6,9), (7,40))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="book"
	uid="c18_book"
	my_supers = Supers.Supers(isOverlapping=True, elements=[
		Exp.Exp(expType="Super", , parentId="", pos=((6,17), (6,21)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c1_Book", isTop=True)])])
	card=(1,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="Boolean", parentId="c19_exp", pos=((7,19), (7,40)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="in", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c20_exp", pos=((7,19), (7,25)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="parent", isTop=True)])])]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c21_exp", pos=((7,29), (7,40)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c22_exp", pos=((7,29), (7,33)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c23_exp", pos=((7,34), (7,40)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c2_author", isTop=False)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])])])])])]))
	stack[-1].addElement(constraint)
	stack.pop()
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="Boolean", parentId="c24_exp", pos=((0,0), (0,0)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="All", declaration=
		Declaration.Declaration(isDisjunct=True, localDeclarations=[LocalDeclaration.LocalDeclaration("x"), LocalDeclaration.LocalDeclaration("y")],  body=
		Exp.Exp(expType="Body", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c18_book", isTop=False)])])])),bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="Boolean", parentId="c26_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="!=", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c27_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c28_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="x", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c29_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c30_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="Set", parentId="c31_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="y", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="Set", parentId="c32_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])]))]))
	stack[-1].addElement(constraint)
	stack.pop()
##### clafer #####
	pos=((9,1), (9,11))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="B"
	uid="c33_B"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="Set", parentId="", pos=((9,5), (9,9)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c1_Book", isTop=True)])])
	card=(5,5)
	globalCard=(5,5)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((10,1), (10,13))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="A"
	uid="c34_A"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="Set", parentId="", pos=((10,5), (10,11)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c17_Author", isTop=True)])])
	card=(6,6)
	globalCard=(6,6)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
	return module