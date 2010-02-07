
`include "vmm.sv"

class my_xactor extends vmm_xactor;
   typedef enum { AA, BB, CC } e_myenum;
   typedef class t_mydata;
   typedef class t_myclass;
   
   int    myint;
   int    myintarr[10];
   int    myintda[];
   int    myintaa_int[int];
   int    myintaa_str[string];
   
   string mystr;
   string mystrarr[10];
   string mystrda[];
   string mystraa_int[int];
   string mystraa_str[string];
   
   e_myenum     myenum;
   e_myenum     myenumarr[10];
   e_myenum     myenumda[];
   e_myenum     myenumaa_int[int];
   e_myenum     myenumaa_str[string];
   
   t_mydata     mydata;
   t_mydata     mydataarr[10];
   t_mydata     mydatada[];
   t_mydata     mydataaa_int[int];
   t_mydata     mydataaa_str[string];
   
   t_myclass    myclass;
   t_myclass    myclassarr[10];
   t_myclass    myclassda[];
   t_myclass    myclassaa_int[int];
   t_myclass    myclassaa_str[string];
   
   vmm_channel  mych;
   vmm_channel  mycharr[10];
   vmm_channel  mychda[];
   vmm_channel  mychaa_int[int];
   vmm_channel  mychaa_str[string];
   
   vmm_xactor   myxact;
   vmm_xactor   myxactarr[10];
   vmm_xactor   myxactda[];
   vmm_xactor   myxactaa_int[int];
   vmm_xactor   myxactaa_str[string];
   
   vmm_subenv   mysub;
   vmm_subenv   mysubarr[10];
   vmm_subenv   mysubda[];
   vmm_subenv   mysubaa_int[int];
   vmm_subenv   mysubaa_str[string];
   
   vmm_scenario mysc;
   
   `vmm_data_member_begin(my_xactor)
     `vmm_data_member_scalar(myint, DO_ALL)
      `vmm_data_member_scalar_array(myintarr, DO_ALL )
      `vmm_data_member_da(myintda, DO_ALL )
      `vmm_data_member_scalar_aa_scalar(myintaa_int, DO_ALL )
      `vmm_data_member_scalar_aa_string(myintaa_str, DO_ALL )
      
      `vmm_data_member_string(mystr, DO_ALL)
      `vmm_data_member_string_array(mystrarr, DO_ALL)
      `vmm_data_member_string_da(mystrda, DO_ALL)
      `vmm_data_member_string_aa_scalar(mystraa_int, DO_ALL)
      `vmm_data_member_string_aa_string(mystraa_str, DO_ALL)
      
      `vmm_data_member_enum(myenum, DO_ALL)
      `vmm_data_member_enum_array(myenumarr, DO_ALL)
      `vmm_data_member_enum_da(myenumda, DO_ALL)
      `vmm_data_member_enum_aa_scalar(myenumaa_int, DO_ALL)
      `vmm_data_member_enum_aa_string(myenumaa_str, DO_ALL)
      
      `vmm_data_member_vmm_data(mydata, DO_ALL, DO_DEEP )
      `vmm_data_member_vmm_data_array(mydataarr, DO_ALL, DO_DEEP )
      `vmm_data_member_vmm_data_da(mydatada, DO_ALL, DO_DEEP )
      `vmm_data_member_vmm_data_aa_scalar(mydataaa_int, DO_ALL, DO_DEEP )
      `vmm_data_member_vmm_data_aa_string(mydataaa_str, DO_ALL, DO_DEEP )
      
      `vmm_data_member_handle(myclass, DO_ALL )
      `vmm_data_member_handle_array(myclassarr, DO_ALL )
      `vmm_data_member_handle_da(myclassda, DO_ALL )
      `vmm_data_member_handle_aa_scalar(myclassaa_int, DO_ALL )
      `vmm_data_member_handle_aa_string(myclassaa_str, DO_ALL )
   `vmm_data_member_end(my_xactor)
   
   `vmm_env_member_begin(my_xactor)
     `vmm_env_member_scalar(myint, DO_ALL)
      `vmm_env_member_scalar_array(myintarr, DO_ALL )
      `vmm_env_member_da(myintda, DO_ALL )
      `vmm_env_member_scalar_aa_scalar(myintaa_int, DO_ALL )
      `vmm_env_member_scalar_aa_string(myintaa_str, DO_ALL )
      
      `vmm_env_member_string(mystr, DO_ALL)
      `vmm_env_member_string_array(mystrarr, DO_ALL)
      `vmm_env_member_string_da(mystrda, DO_ALL)
      `vmm_env_member_string_aa_scalar(mystraa_int, DO_ALL)
      `vmm_env_member_string_aa_string(mystraa_str, DO_ALL)
      
      `vmm_env_member_enum(myenum, DO_ALL)
      `vmm_env_member_enum_array(myenumarr, DO_ALL)
      `vmm_env_member_enum_da(myenumda, DO_ALL)
      `vmm_env_member_enum_aa_scalar(myenumaa_int, DO_ALL)
      `vmm_env_member_enum_aa_string(myenumaa_str, DO_ALL)
      
      `vmm_env_member_vmm_data(mydata, DO_ALL )
      `vmm_env_member_vmm_data_array(mydataarr, DO_ALL )
      `vmm_env_member_vmm_data_da(mydatada, DO_ALL )
      `vmm_env_member_vmm_data_aa_scalar(mydataaa_int, DO_ALL )
      `vmm_env_member_vmm_data_aa_string(mydataaa_str, DO_ALL )
      
      `vmm_env_member_channel(mych, DO_ALL )
      `vmm_env_member_channel_array(mycharr, DO_ALL )
      `vmm_env_member_channel_da(mychda, DO_ALL )
      `vmm_env_member_channel_aa_scalar(mychaa_int, DO_ALL )
      `vmm_env_member_channel_aa_string(mychaa_str, DO_ALL )
      
      `vmm_env_member_xactor(myxact, DO_ALL )
      `vmm_env_member_xactor_array(myxactarr, DO_ALL )
      `vmm_env_member_xactor_da(myxactda, DO_ALL )
      `vmm_env_member_xactor_aa_scalar(myxactaa_int, DO_ALL )
      `vmm_env_member_xactor_aa_string(myxactaa_str, DO_ALL )
      
      `vmm_env_member_subenv(mysub, DO_ALL )
      `vmm_env_member_subenv_array(mysubarr, DO_ALL )
      `vmm_env_member_subenv_da(mysubda, DO_ALL )
      `vmm_env_member_subenv_aa_scalar(mysubaa_int, DO_ALL )
      `vmm_env_member_subenv_aa_string(mysubaa_str, DO_ALL )
   `vmm_env_member_end(my_xactor)
   
   `vmm_scenario_member_begin(my_xactor)
     `vmm_scenario_member_scalar(myint, DO_ALL)
      `vmm_scenario_member_scalar_array(myintarr, DO_ALL )
      `vmm_scenario_member_da(myintda, DO_ALL )
      `vmm_scenario_member_scalar_aa_scalar(myintaa_int, DO_ALL )
      `vmm_scenario_member_scalar_aa_string(myintaa_str, DO_ALL )
      
      `vmm_scenario_member_string(mystr, DO_ALL)
      `vmm_scenario_member_string_array(mystrarr, DO_ALL)
      `vmm_scenario_member_string_da(mystrda, DO_ALL)
      `vmm_scenario_member_string_aa_scalar(mystraa_int, DO_ALL)
      `vmm_scenario_member_string_aa_string(mystraa_str, DO_ALL)
      
      `vmm_scenario_member_enum(myenum, DO_ALL)
      `vmm_scenario_member_enum_array(myenumarr, DO_ALL)
      `vmm_scenario_member_enum_da(myenumda, DO_ALL)
      `vmm_scenario_member_enum_aa_scalar(myenumaa_int, DO_ALL)
      `vmm_scenario_member_enum_aa_string(myenumaa_str, DO_ALL)
      
      `vmm_scenario_member_vmm_data(mydata, DO_ALL, DO_DEEP )
      `vmm_scenario_member_vmm_data_array(mydataarr, DO_ALL, DO_DEEP )
      `vmm_scenario_member_vmm_data_da(mydatada, DO_ALL, DO_DEEP )
      `vmm_scenario_member_vmm_data_aa_scalar(mydataaa_int, DO_ALL, DO_DEEP )
      `vmm_scenario_member_vmm_data_aa_string(mydataaa_str, DO_ALL, DO_DEEP )
      
      `vmm_scenario_member_handle(myclass, DO_ALL )
      `vmm_scenario_member_handle_array(myclassarr, DO_ALL )
      `vmm_scenario_member_handle_da(myclassda, DO_ALL )
      `vmm_scenario_member_handle_aa_scalar(myclassaa_int, DO_ALL )
      `vmm_scenario_member_handle_aa_string(myclassaa_str, DO_ALL )
      
      `vmm_scenario_member_vmm_scenario(mysc, DO_ALL )
   `vmm_scenario_member_end(my_xactor)
   
   `vmm_subenv_member_begin(my_xactor)
     `vmm_subenv_member_scalar(myint, DO_ALL)
      `vmm_subenv_member_scalar_array(myintarr, DO_ALL )
      `vmm_subenv_member_da(myintda, DO_ALL )
      `vmm_subenv_member_scalar_aa_scalar(myintaa_int, DO_ALL )
      `vmm_subenv_member_scalar_aa_string(myintaa_str, DO_ALL )
      
      `vmm_subenv_member_string(mystr, DO_ALL)
      `vmm_subenv_member_string_array(mystrarr, DO_ALL)
      `vmm_subenv_member_string_da(mystrda, DO_ALL)
      `vmm_subenv_member_string_aa_scalar(mystraa_int, DO_ALL)
      `vmm_subenv_member_string_aa_string(mystraa_str, DO_ALL)
      
      `vmm_subenv_member_enum(myenum, DO_ALL)
      `vmm_subenv_member_enum_array(myenumarr, DO_ALL)
      `vmm_subenv_member_enum_da(myenumda, DO_ALL)
      `vmm_subenv_member_enum_aa_scalar(myenumaa_int, DO_ALL)
      `vmm_subenv_member_enum_aa_string(myenumaa_str, DO_ALL)
      
      `vmm_subenv_member_vmm_data(mydata, DO_ALL )
      `vmm_subenv_member_vmm_data_array(mydataarr, DO_ALL )
      `vmm_subenv_member_vmm_data_da(mydatada, DO_ALL )
      `vmm_subenv_member_vmm_data_aa_scalar(mydataaa_int, DO_ALL )
      `vmm_subenv_member_vmm_data_aa_string(mydataaa_str, DO_ALL )
      
      `vmm_subenv_member_channel(mych, DO_ALL )
      `vmm_subenv_member_channel_array(mycharr, DO_ALL )
      `vmm_subenv_member_channel_da(mychda, DO_ALL )
      `vmm_subenv_member_channel_aa_scalar(mychaa_int, DO_ALL )
      `vmm_subenv_member_channel_aa_string(mychaa_str, DO_ALL )
      
      `vmm_subenv_member_xactor(myxact, DO_ALL )
      `vmm_subenv_member_xactor_array(myxactarr, DO_ALL )
      `vmm_subenv_member_xactor_da(myxactda, DO_ALL )
      `vmm_subenv_member_xactor_aa_scalar(myxactaa_int, DO_ALL )
      `vmm_subenv_member_xactor_aa_string(myxactaa_str, DO_ALL )
      
      `vmm_subenv_member_subenv(mysub, DO_ALL )
      `vmm_subenv_member_subenv_array(mysubarr, DO_ALL )
      `vmm_subenv_member_subenv_da(mysubda, DO_ALL )
      `vmm_subenv_member_subenv_aa_scalar(mysubaa_int, DO_ALL )
      `vmm_subenv_member_subenv_aa_string(mysubaa_str, DO_ALL )
   `vmm_subenv_member_end(my_xactor)
   
   `vmm_xactor_member_begin(my_xactor)
     `vmm_xactor_member_scalar(myint, DO_ALL)
      `vmm_xactor_member_scalar_array(myintarr, DO_ALL )
      `vmm_xactor_member_da(myintda, DO_ALL )
      `vmm_xactor_member_scalar_aa_scalar(myintaa_int, DO_ALL )
      `vmm_xactor_member_scalar_aa_string(myintaa_str, DO_ALL )
      
      `vmm_xactor_member_string(mystr, DO_ALL)
      `vmm_xactor_member_string_array(mystrarr, DO_ALL)
      `vmm_xactor_member_string_da(mystrda, DO_ALL)
      `vmm_xactor_member_string_aa_scalar(mystraa_int, DO_ALL)
      `vmm_xactor_member_string_aa_string(mystraa_str, DO_ALL)
      
      `vmm_xactor_member_enum(myenum, DO_ALL)
      `vmm_xactor_member_enum_array(myenumarr, DO_ALL)
      `vmm_xactor_member_enum_da(myenumda, DO_ALL)
      `vmm_xactor_member_enum_aa_scalar(myenumaa_int, DO_ALL)
      `vmm_xactor_member_enum_aa_string(myenumaa_str, DO_ALL)
      
      `vmm_xactor_member_vmm_data(mydata, DO_ALL )
      `vmm_xactor_member_vmm_data_array(mydataarr, DO_ALL )
      `vmm_xactor_member_vmm_data_da(mydatada, DO_ALL )
      `vmm_xactor_member_vmm_data_aa_scalar(mydataaa_int, DO_ALL )
      `vmm_xactor_member_vmm_data_aa_string(mydataaa_str, DO_ALL )
      
      `vmm_xactor_member_channel(mych, DO_ALL )
      `vmm_xactor_member_channel_array(mycharr, DO_ALL )
      `vmm_xactor_member_channel_da(mychda, DO_ALL )
      `vmm_xactor_member_channel_aa_scalar(mychaa_int, DO_ALL )
      `vmm_xactor_member_channel_aa_string(mychaa_str, DO_ALL )
      
      `vmm_xactor_member_xactor(myxact, DO_ALL )
      `vmm_xactor_member_xactor_array(myxactarr, DO_ALL )
      `vmm_xactor_member_xactor_da(myxactda, DO_ALL )
      `vmm_xactor_member_xactor_aa_scalar(myxactaa_int, DO_ALL )
      `vmm_xactor_member_xactor_aa_string(myxactaa_str, DO_ALL )
   `vmm_xactor_member_end(my_xactor)
   
endclass: my_xactor
