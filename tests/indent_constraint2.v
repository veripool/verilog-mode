
constraint Cepon_gate_random::grant_relations_c {
						 foreach (grant_relation_m[index]) {
										    if ((index == 0) && (last_start_time_m < time_stamp_m+`MINIMUM_TIME_TO_GATE)) grant_relation_m[index] == EPON_GATE_IN_ORDER;
										    
										    else {
   
   grant_relation_m[index] dist {
				 EPON_GATE_IN_ORDER :/55,
				 EPON_GATE_1ST_CONTAINS_2ND :/5,
				 EPON_GATE_2ND_CONTAINS_1ST :/5,
				 EPON_GATE_1ST_START_2ND_START :/5,
				 EPON_GATE_2ND_START_1ST_START :/5,
				 EPON_GATE_NO_GAP_1ST :/5,
				 EPON_GATE_NO_GAP_2ND :/5,
				 EPON_GATE_1CC_GAP :/5,
				 EPON_GATE_1CC_INTERLEAVE :/5,
				 EQUAL :/5
                        };

}
										    
										    }
						 
						 }
