open util/integer
pred show {}

abstract sig c1_IMeasurable
{  }

sig c4_AbstractElement extends c1_IMeasurable
{}

sig c10_AbstractSort extends c1_IMeasurable
{}


inst configureproduct {
	2,
	c10_AbstractSort in IM_AbstractSort,
	c4_AbstractElement in IM_AbstractElement
}


run  show for configureproduct

