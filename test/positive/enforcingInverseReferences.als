/*
All clafers: 6 | Abstract: 2 | Concrete: 2 | References: 2
Constraints: 4
Goals: 0
Global scope: 6..*
All names unique: False
*/
open util/integer
pred show {}
run  show for 1 but 6 c17_Author, 6 c18_book, 5 c1_Book, 6 c2_author, 5 c33_B, 6 c34_A

abstract sig c1_Book
{ r_c2_author : some c2_author }
{ all disj x, y : this.@r_c2_author | (x.@ref) != (y.@ref) }

sig c2_author
{ ref : one c17_Author }
{ one @r_c2_author.this
  (this.~@r_c2_author) in (this.(@ref.(@r_c18_book.@ref))) }

abstract sig c17_Author
{ r_c18_book : some c18_book }
{ all disj x, y : this.@r_c18_book | (x.@ref) != (y.@ref) }

sig c18_book
{ ref : one c1_Book }
{ one @r_c18_book.this
  (this.~@r_c18_book) in (this.(@ref.(@r_c2_author.@ref))) }

fact { 5 <= #c33_B and #c33_B <= 5 }
sig c33_B extends c1_Book
{}

fact { 6 <= #c34_A and #c34_A <= 6 }
sig c34_A extends c17_Author
{}

