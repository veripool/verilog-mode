// bug1259

class trial_good; // this works because the variable class_name has been renamed clazz_name
   string clazz_name="trial_good";
   function void f();
   endfunction // f
endclass // trial_good

class trial_bad; // this fools the autocommenter, that ends reporting "function" as class name
   string class_name="trial_bad";
   function void f();
   endfunction // f
endclass // trial_bad

// Local Variables:
// verilog-auto-endcomments: t
// End:
