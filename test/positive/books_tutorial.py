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
	pos=((4,1), (24,27))
	isAbstract=True
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="Book"
	uid="c1_Book"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((5,5), (6,28))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="title"
	uid="c2_title"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((5,13), (5,19)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="string", isTop=True)])])
	card=(1,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((6,9), (6,28))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="subtitle"
	uid="c3_subtitle"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((6,20), (6,26)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="string", isTop=True)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
	stack.pop()
##### clafer #####
	pos=((7,5), (7,19))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="year"
	uid="c4_year"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((7,12), (7,19)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="integer", isTop=True)])])
	card=(1,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((8,5), (8,14))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="page"
	uid="c5_page"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(2,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((9,5), (12,19))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=True, interval=(1,1))
	id="format"
	uid="c6_format"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(1,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((10,9), (11,24))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="paper"
	uid="c7_paper"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((11,13), (11,24))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="hardcover"
	uid="c8_hardcover"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
	stack.pop()
##### clafer #####
	pos=((12,9), (12,19))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="electronic"
	uid="c9_electronic"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
	stack.pop()
##### clafer #####
	pos=((13,5), (19,23))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=True, interval=(1,1))
	id="kind"
	uid="c10_kind"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(1,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((14,9), (14,17))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="textbook"
	uid="c11_textbook"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((15,9), (15,15))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="manual"
	uid="c12_manual"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((16,9), (16,18))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="reference"
	uid="c13_reference"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((17,9), (17,16))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="fiction"
	uid="c14_fiction"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((18,9), (18,19))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="nonfiction"
	uid="c15_nonfiction"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((19,9), (19,23))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="other"
	uid="c16_other"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((19,17), (19,23)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="string", isTop=True)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
	stack.pop()
##### clafer #####
	pos=((20,5), (20,24))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="authors"
	uid="c17_authors"
	my_supers = Supers.Supers(isOverlapping=True, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((20,16), (20,22)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c44_Author", isTop=True)])])
	card=(1,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="IBoolean", parentId="c18_exp", pos=((0,0), (0,0)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="IAll", declaration=
		Declaration.Declaration(isDisjunct=True, localDeclarations=[LocalDeclaration.LocalDeclaration("x"), LocalDeclaration.LocalDeclaration("y")],  body=
		Exp.Exp(expType="Body", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c17_authors", isTop=False)])])])),bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="IBoolean", parentId="c20_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="!=", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c21_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c22_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="x", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c23_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c24_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c25_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="y", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c26_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])]))]))
	stack[-1].addElement(constraint)
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="IBoolean", parentId="c27_exp", pos=((21,7), (21,24)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=>", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c28_exp", pos=((21,7), (21,16)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=">=", elements=[
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="c29_exp", pos=((21,7), (21,11)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c4_year", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="c30_exp", pos=((21,15), (21,16)), iExpType="IIntExp", iExp=[5])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c31_exp", pos=((21,20), (21,24)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="ISome", declaration=None, bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="ISet", parentId="c32_exp", pos=((21,20), (21,24)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c33_ISBN", isTop=False)])])]))])])]))
	stack[-1].addElement(constraint)
##### clafer #####
	pos=((22,5), (24,27))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="ISBN"
	uid="c33_ISBN"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((22,12), (22,18)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="string", isTop=True)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((23,9), (23,23))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="GS1"
	uid="c34_GS1"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((23,15), (23,21)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="string", isTop=True)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="IBoolean", parentId="c35_exp", pos=((24,11), (24,27)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=>", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c36_exp", pos=((24,11), (24,20)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=">=", elements=[
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="c37_exp", pos=((24,11), (24,15)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="parent", isTop=True)])])]),
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c4_year", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="c38_exp", pos=((24,19), (24,20)), iExpType="IIntExp", iExp=[6])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c39_exp", pos=((24,24), (24,27)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="ISome", declaration=None, bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="ISet", parentId="c40_exp", pos=((24,24), (24,27)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c34_GS1", isTop=False)])])]))])])]))
	stack[-1].addElement(constraint)
	stack.pop()
	stack.pop()
##### clafer #####
	pos=((26,1), (28,19))
	isAbstract=True
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="Person"
	uid="c41_Person"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="clafer", isTop=False)])])
	card=(0,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((27,5), (27,18))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="name"
	uid="c42_name"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((27,12), (27,18)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="string", isTop=True)])])
	card=(1,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### clafer #####
	pos=((28,5), (28,19))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="dob"
	uid="c43_dob"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((28,11), (28,17)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="string", isTop=True)])])
	card=(0,1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
	stack.pop()
##### clafer #####
	pos=((30,1), (31,20))
	isAbstract=True
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="Author"
	uid="c44_Author"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((30,19), (30,25)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c41_Person", isTop=True)])])
	card=(0,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### clafer #####
	pos=((31,5), (31,20))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="books"
	uid="c45_books"
	my_supers = Supers.Supers(isOverlapping=True, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((31,14), (31,18)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c1_Book", isTop=True)])])
	card=(1,-1)
	globalCard=(0,-1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
	stack.pop()
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="IBoolean", parentId="c46_exp", pos=((0,0), (0,0)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="IAll", declaration=
		Declaration.Declaration(isDisjunct=True, localDeclarations=[LocalDeclaration.LocalDeclaration("x"), LocalDeclaration.LocalDeclaration("y")],  body=
		Exp.Exp(expType="Body", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c45_books", isTop=False)])])])),bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="IBoolean", parentId="c48_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="!=", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c49_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c50_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="x", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c51_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c52_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c53_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="y", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c54_exp", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])]))]))
	stack[-1].addElement(constraint)
	stack.pop()
##### clafer #####
	pos=((33,1), (42,14))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="GenerativeProgramming"
	uid="c55_GenerativeProgramming"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((33,25), (33,29)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c1_Book", isTop=True)])])
	card=(1,1)
	globalCard=(1,1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="IBoolean", parentId="c56_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c57_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c58_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c59_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c60_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c61_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c62_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c63_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c64_exp", pos=((34,7), (34,21)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=", elements=[
		Exp.Exp(expType="Argument", my_type="IString", parentId="c65_exp", pos=((34,7), (34,12)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="IString", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c2_title", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="IString", parentId="c66_exp", pos=((34,15), (34,21)), iExpType="IStringExp", iExp=["\"name\""])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c67_exp", pos=((35,8), (35,19)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="INo", declaration=None, bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="ISet", parentId="c68_exp", pos=((35,11), (35,19)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c2_title", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c3_subtitle", isTop=False)])])]))])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c69_exp", pos=((36,8), (36,16)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=", elements=[
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="c70_exp", pos=((36,8), (36,12)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c4_year", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="c71_exp", pos=((36,15), (36,16)), iExpType="IIntExp", iExp=[5])])])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c72_exp", pos=((37,8), (37,19)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=", elements=[
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="c73_exp", pos=((37,8), (37,15)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="#", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c74_exp", pos=((37,11), (37,15)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c5_page", isTop=False)])])])])]),
		Exp.Exp(expType="Argument", my_type="IInteger", parentId="c75_exp", pos=((37,18), (37,19)), iExpType="IIntExp", iExp=[4])])])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c76_exp", pos=((38,8), (38,13)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="ISome", declaration=None, bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="ISet", parentId="c77_exp", pos=((38,8), (38,13)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c6_format", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c7_paper", isTop=False)])])]))])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c78_exp", pos=((39,8), (39,18)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="ISome", declaration=None, bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="ISet", parentId="c79_exp", pos=((39,8), (39,18)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c10_kind", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c15_nonfiction", isTop=False)])])]))])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c80_exp", pos=((40,8), (40,39)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c81_exp", pos=((40,8), (40,15)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c17_authors", isTop=False)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c82_exp", pos=((40,18), (40,39)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="++", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c83_exp", pos=((40,18), (40,27)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c90_Czarnecki", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c84_exp", pos=((40,29), (40,39)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c98_Eisenecker", isTop=True)])])])])])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c85_exp", pos=((41,8), (41,21)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=", elements=[
		Exp.Exp(expType="Argument", my_type="IString", parentId="c86_exp", pos=((41,8), (41,12)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="IString", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c33_ISBN", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="IString", parentId="c87_exp", pos=((41,15), (41,21)), iExpType="IStringExp", iExp=["\"name\""])])])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c88_exp", pos=((42,8), (42,14)), iExpType="IDeclarationParentExp", iExp=[DeclPExp.DeclPExp(quantifier="INo", declaration=None, bodyParentExp=
		Exp.Exp(expType="BodyParentExp", my_type="ISet", parentId="c89_exp", pos=((42,11), (42,14)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c33_ISBN", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c34_GS1", isTop=False)])])]))])])]))
	stack[-1].addElement(constraint)
	stack.pop()
##### clafer #####
	pos=((44,1), (46,38))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="Czarnecki"
	uid="c90_Czarnecki"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((44,13), (44,19)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c44_Author", isTop=True)])])
	card=(1,1)
	globalCard=(1,1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="IBoolean", parentId="c91_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c92_exp", pos=((45,7), (45,20)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=", elements=[
		Exp.Exp(expType="Argument", my_type="IString", parentId="c93_exp", pos=((45,7), (45,11)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="IString", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c42_name", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="IString", parentId="c94_exp", pos=((45,14), (45,20)), iExpType="IStringExp", iExp=["\"name\""])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c95_exp", pos=((46,8), (46,38)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="in", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c96_exp", pos=((46,8), (46,29)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c55_GenerativeProgramming", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c97_exp", pos=((46,33), (46,38)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c45_books", isTop=False)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])])])])])]))
	stack[-1].addElement(constraint)
	stack.pop()
##### clafer #####
	pos=((48,1), (50,38))
	isAbstract=False
	groupCard = GCard.GCard(isKeyword=False, interval=(0,-1))
	id="Eisenecker"
	uid="c98_Eisenecker"
	my_supers = Supers.Supers(isOverlapping=False, elements=[
		Exp.Exp(expType="Super", my_type="ISet", parentId="", pos=((48,14), (48,20)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c44_Author", isTop=True)])])
	card=(1,1)
	globalCard=(1,1)
	currClafer = Clafer.Clafer(pos=pos, isAbstract=isAbstract, gcard=groupCard, ident=id, uid=uid, my_supers=my_supers, card=card, glCard=globalCard)
	stack[-1].addElement(currClafer)
	stack.append(currClafer)
##### constraint #####
	constraint = Constraint.Constraint(isHard=True , exp=
		Exp.Exp(expType="ParentExp", my_type="IBoolean", parentId="c99_exp", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="&&", elements=[
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c100_exp", pos=((49,7), (49,20)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="=", elements=[
		Exp.Exp(expType="Argument", my_type="IString", parentId="c101_exp", pos=((49,7), (49,11)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="IString", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c42_name", isTop=False)])])]),
		Exp.Exp(expType="Argument", my_type="IString", parentId="c102_exp", pos=((49,14), (49,20)), iExpType="IStringExp", iExp=["\"name\""])])]),
		Exp.Exp(expType="Argument", my_type="IBoolean", parentId="c103_exp", pos=((50,8), (50,38)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation="in", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c104_exp", pos=((50,8), (50,29)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c55_GenerativeProgramming", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="c105_exp", pos=((50,33), (50,38)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="this", isTop=True)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IFunctionExp", iExp=[FunExp.FunExp(operation=".", elements=[
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="c45_books", isTop=False)]),
		Exp.Exp(expType="Argument", my_type="ISet", parentId="", pos=((0,0), (0,0)), iExpType="IClaferId", iExp=[ClaferId.ClaferId(moduleName="", my_id="ref", isTop=False)])])])])])])])])]))
	stack[-1].addElement(constraint)
	stack.pop()
	return module