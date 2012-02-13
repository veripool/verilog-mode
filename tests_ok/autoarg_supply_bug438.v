module top
  (
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input supply0 VDD, // To inst of inst_module.v
   input supply1 VDD_from_child, // To inst of inst_module.v
   input supply1 VSS, // To inst of inst_module.v
   input         non_supply             // To inst of inst_module.v
   // End of automatics
   );
   
   /*AUTOWIRE*/
   
   inst_module inst (/*AUTOINST*/
                     // Inputs
                     .VDD               (VDD),
                     .VSS               (VSS),
                     .non_supply        (non_supply),
                     .VDD_from_child    (VDD_from_child));
endmodule

module inst_module (input supply0 VDD,
                    input supply1 VSS,
                    input         non_supply,
                    input supply1 VDD_from_child
                    );
   
endmodule
