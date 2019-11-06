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

class rand_test;

    ahb_driver                  ahb_driver_0;
    random_gen                  random_gen_0;
    socket      #(ahb_trans)    gen2drv = new(2);

    extern function new(name = "", virtual ahb_lite_if ahb_vif);
    extern task     run();
    extern task     connect();
    
endclass : rand_test

function rand_test::new(name = "", virtual ahb_lite_if ahb_vif);
    ahb_driver_0 = new("AHB_DRIVER", ahb_vif);
    random_gen_0 = new("RANDOM_GEN", ahb_vif);
endfunction : new

task rand_test::connect();
    ahb_driver_0.gen2drv.connect(gen2drv);
    random_gen_0.gen2drv.connect(gen2drv);
endtask : connect

task rand_test::run();
    fork
        ahb_driver_0.run();
        random_gen_0.run();
    join
endtask : run

`endif // RAND_TEST__SV
