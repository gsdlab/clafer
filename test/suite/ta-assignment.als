/* Simplifications:
    - for now we ignore lab instructors
    - for now we assume that a prof teaches only one course
    - profs only have three ranking levels in this model
    - we say TA's are happy if they get their first choice
    - no half TA positions
*/

-- the structure of the model (write by hand)
sig Course { 
    lecturer : one Prof,
    assistants : set TA, -- this is what we are solving for
    allocation : one Int,
}{
    -- cannot have more TAs assigned than spaces allocated
    #assistants <= allocation
}
sig TA { first, second, third : lone Course }
sig Prof { prefer, reject : set TA }

-- constraints
-- each TA can be assigned to at most one course
fact SingleCoursePerTA { all ta : TA | lone assistants.ta }
-- TA will only be assigned to a course that they named
fact RespectTAWishes { ~assistants & (first+second+third) }
-- all assigned TAs are preferred or accepted by the prof
fact RespectProfWishes { no ~lecturer.assistants & reject }

-- this is generated from the CSV input
inst Winter2012 {
    Prof = X + Y, 
    TA = A + B + C + D + E + F + G,
    Course = ECE155 + ECE351,
    lecturer = ECE155->X + ECE351->Y,
    allocation = ECE155->3 + ECE351->2,
    prefer = X->A + X->B + Y->A + Y->B + Y->C,
    reject = X->F + X->G + Y->D + Y->G,
    first = A->ECE155 + B->ECE351 + C->ECE155 + D->ECE351 + E->ECE155 
            + F->ECE351 + G->ECE351
    second = A->ECE351 + B->ECE155 + C->ECE351 + D->ECE155 + E->ECE351
    no third
}


-- the various objectives to optimize
metrics m {
    -- prof happiness: got preferred TAs
    max[ #( ~lecturer.assistants & prefer ) ]
    -- prof unhappiness: spaces that are allocated by not assigned (holes)
    min[ (sum c : Course | c.allocation) - #assistants ]
    -- TA happiness: got first choice
    max[ #(assistants & ~first) ]
    -- TA unhappiness: didn't get a job
    min[ #(TA - Course.assistants) ]
}

pred p[] {}

run p for Winter2012 optimize m

