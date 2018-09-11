// issue 928 - 'pure virtual' items in classes break indentation
package p;
virtual class c extends parent;
pure virtual protected task t(type_t a, type_t b);
function f(string s="");
blah;
endfunction:f
endclass
endpackage
