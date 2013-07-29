open util/integer
pred show {}


abstract sig c1_Book
{ r_c2_author : some c2_author }
{ all disj x, y : this.@r_c2_author | (x.@ref) != (y.@ref) }

sig c2_author
{ ref : one c3_Author }
{ one @r_c2_author.this
  (this.~@r_c2_author) in (this.(@ref.(@r_c4_book.@ref))) }

abstract sig c3_Author
{ r_c4_book : some c4_book }
{ all disj x, y : this.@r_c4_book | (x.@ref) != (y.@ref) }

sig c4_book
{ ref : one c1_Book }
{ one @r_c4_book.this
  (this.~@r_c4_book) in (this.(@ref.(@r_c2_author.@ref))) }

fact { 5 <= #c5_B and #c5_B <= 5 }
sig c5_B extends c1_Book
{}

fact { 6 <= #c6_A and #c6_A <= 6 }
sig c6_A extends c3_Author
{}

