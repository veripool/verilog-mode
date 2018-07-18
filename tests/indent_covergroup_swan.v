module m;
   bit[0:0] a, b, c;
   covergroup g;
            cp_ab: coverpoint {a,b} {
				     bins one = {1};
				     bins two = {2};
				                                    }

	              cp_ab_if_c: coverpoint {a,b} iff c {
							  bins one = {1};
							  bins two = {2};
							          }

		              cp_ab_if_c_slice: coverpoint {a,b} iff c[0] {
									   bins one = {1};
									   bins two = {2};
									                                                        }

				          cp_a_if_bc: coverpoint {a,b} iff {b,c} {
										  bins one = {1};
										  bins two = {2};
										                                                    }

					                cp_a_slice : coverpoint a[0] {
										      bins one = {1};
										      bins two = {2};
										                                                }

							                cp_a_slice_if_b : coverpoint a[0] iff b {
														 bins one = {1};
														 bins two = {2};
														               }

									              cp_a_if_b_slice : coverpoint a iff b[0] {
															       bins one = {1};
															       bins two = {2};
															                                                              }

											                cp_a_slice_if_b_slice : coverpoint a[0] iff b[0] {
																			  bins one = {1};
																			  bins two = {2};
																			                                                                    }
													  endgroup
endmodule
