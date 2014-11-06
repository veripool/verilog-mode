// See Line 54

module hangcase (/*AUTOARG*/);

   //
   assign w_rdat_ena       = ({16{foo[ 0]}} & bar ) |
			     ({16{foo[ 1]}} & bar ) |
			     ({16{foo[ 2]}} & bar ) |
			     ({16{foo[ 3]}} & bar ) |
			     ({16{foo[ 4]}} & bar ) |
			     ({16{foo[ 5]}} & bar ) |
			     ({16{foo[ 6]}} & bar ) |
			     ({16{foo[ 7]}} & bar ) |
			     ({16{foo[ 8]}} & bar ) |
			     ({16{foo[ 9]}} & bar ) |
			     ({16{foo[10]}} & bar ) |
			     ({16{foo[11]}} & bar ) |
			     ({16{foo[12]}} & bar ) |
			     ({16{foo[13]}} & bar ) |
			     ({16{foo[14]}} & bar ) |
			     ({16{foo[15]}} & bar ) ;

   //
   assign w_rdat_mrk       = ({16{foo[ 0]}} & bar & baz ) |
			     ({16{foo[ 1]}} & bar & baz ) |
			     ({16{foo[ 2]}} & bar & baz ) |
			     ({16{foo[ 3]}} & bar & baz ) |
			     ({16{foo[ 4]}} & bar & baz ) |
			     ({16{foo[ 5]}} & bar & baz ) |
			     ({16{foo[ 6]}} & bar & baz ) |
			     ({16{foo[ 7]}} & bar & baz ) |
			     ({16{foo[ 8]}} & bar & baz ) |
			     ({16{foo[ 9]}} & bar & baz ) |
			     ({16{foo[10]}} & bar & baz ) |
			     ({16{foo[11]}} & bar & baz ) |
			     ({16{foo[12]}} & bar & baz ) |
			     ({16{foo[13]}} & bar & baz ) |
			     ({16{foo[14]}} & bar & baz ) |
			     ({16{foo[15]}} & bar & baz ) ;

   //
   assign w_wdat_ena_set  = ({16{ena_set}} & col_dec    );
   assign w_wdat_ena_clr  = ({16{ena_clr}} & col_dec    );
   assign w_wdat_mrk_set  = ({16{mrk_set}} & w_rdat_ena );
   assign w_wdat_mrk_clr  = ({16{mrk_clr}} & col_dec    );
   assign w_wdat_ena      = (w_rdat_ena & ~w_wdat_ena_clr) | w_wdat_ena_set;
   assign w_wdat_mrk      = (w_rdat_mrk & ~w_wdat_mrk_clr) | w_wdat_mrk_set;

   //
   assign w_dat15_ena     = foo[15] ? w_wdat_ena : bar;

   //
   assign w_dat15_mrk     = foo[15] ? w_wdat_mrk : baz;

   //^^^^ FIX NEWLINE ABOVE HERE
   //
   assign w_timeout_mrk     = row_check      ?  w_wdat_mrk        : r_timeout_mrk;

endmodule
