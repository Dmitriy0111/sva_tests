/*
*  File            :   rand_test.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.06
*  Language        :   SystemVerilog
*  Description     :   This is random test
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef RAND_TEST__SV
`define RAND_TEST__SV

class rand_test extends base_test;

    random_gen                  rand_gen;
    ahb_agent                   ahb_agt;

    socket      #(ahb_trans)    gen2drv = new();

    extern function new(string name = "", base_class parent);
    extern task     run();
    extern task     build();
    extern task     connect();
    
endclass : rand_test

function rand_test::new(string name = "", base_class parent);
    super.new(name,parent);
endfunction : new

task rand_test::build();
    rand_gen = new("RAND_GEN");
    ahb_agt  = ahb_agent::creator_::create_obj("AHB_AGT",this);
    ahb_agt.build();
endtask : build

task rand_test::connect();
    ahb_agt.connect();

    ahb_agt.ahb_drv.item_sock.connect(gen2drv);
    rand_gen.gen2drv.connect(gen2drv);
endtask : connect

task rand_test::run();
    fork
        rand_gen.run();
        ahb_agt.run();
    join_none
endtask : run

`endif // RAND_TEST__SV
