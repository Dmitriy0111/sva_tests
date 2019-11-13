/*
*  File            :   base_class.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.07
*  Language        :   SystemVerilog
*  Description     :   This is ahb driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef BASE_CLASS__SV
`define BASE_CLASS__SV

class base_class;

    string          name;
    string          full_name;

    base_class      parent;

    printer         printer_ = new();

    extern virtual task run();

    extern function          string     get_name();
    extern function          void       print();
    extern function          string     sprint();
    extern task                         copy(base_class other_obj);
    extern function          base_class clone();
    extern function          bit        compare();
    extern virtual  function void       help_f(base_class this_obj = null, logic [7 : 0] operation);

endclass : base_class

task base_class::run();
endtask : run

function string base_class::get_name();
    return name;
endfunction : get_name

function void base_class::print();
    help_f( null , `PRINT_FLAG );
    printer_.print_items_table();
endfunction : print

function string base_class::sprint();
    help_f( null , `PRINT_FLAG );
    return printer_.sprint_items_table();
endfunction : sprint

function void base_class::help_f(base_class this_obj = null, logic [7 : 0] operation);

endfunction : help_f

task base_class::copy(base_class other_obj);
    help_f( other_obj , `COPY_FLAG );
endtask : copy

function base_class base_class::clone();
    base_class clone_obj = new();
    clone_obj.copy(this);
    return clone_obj;
endfunction : clone

function bit base_class::compare();

endfunction : compare

`endif // BASE_CLASS__SV
