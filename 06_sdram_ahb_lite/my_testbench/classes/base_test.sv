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

class base_test;

    extern virtual task run();
    extern virtual task connect();
    
endclass : base_test

task base_test::connect();
endtask : connect

task base_test::run();
endtask : run

`endif // BASE_TEST__SV
