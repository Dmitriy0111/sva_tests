/*
*  File            :   direct_test.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.06
*  Language        :   SystemVerilog
*  Description     :   This is direct test
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef DIRECT_TEST__SV
`define DIRECT_TEST__SV

class direct_test extends base_test;

    direct_gen                  direct_gen;
    ahb_agent                   ahb_agt;

    socket      #(ahb_trans)    gen2drv = new();

    extern function new(name = "");
    extern task     connect();
    extern task     run();
    
endclass : direct_test

function direct_test::new(name = "");
    direct_gen = new("DIRECT_GEN");
    ahb_agt  = new("AHB_AGT",this);
endfunction : new

task direct_test::connect();
    ahb_agt.connect();
    
    ahb_agt.ahb_drv.item_sock.connect(gen2drv);
    direct_gen.gen2drv.connect(gen2drv);
endtask : connect

task direct_test::run();
    fork
        direct_gen.run();
        ahb_agt.run();
    join_none
endtask : run

`endif // DIRECT_TEST__SV
