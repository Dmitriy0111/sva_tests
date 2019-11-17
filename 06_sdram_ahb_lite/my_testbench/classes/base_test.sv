/*
*  File            :   base_test.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.07
*  Language        :   SystemVerilog
*  Description     :   This is random test
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef BASE_TEST__SV
`define BASE_TEST__SV

class base_test extends base_class;

    extern         function new(string name = "", base_class parent = null);
    extern virtual task     build();
    extern virtual task     connect();
    extern virtual task     run();
    
endclass : base_test

function base_test::new(string name = "", base_class parent = null);
    super.new(name,parent);
endfunction : new

task base_test::build();
endtask : build

task base_test::connect();
endtask : connect

task base_test::run();
endtask : run

`endif // BASE_TEST__SV
