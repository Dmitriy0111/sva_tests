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

    ahb_driver                  ahb_drv;
    random_gen                  rand_gen;
    ahb_monitor                 ahb_mon;
    ahb_coverage                ahb_cov;

    socket      #(ahb_trans)    gen2drv = new(2);
    socket      #(ahb_trans)    mon2cov = new(1);

    extern function new(name = "", virtual ahb_lite_if ahb_vif);
    extern task     run();
    extern task     connect();
    
endclass : rand_test

function rand_test::new(name = "", virtual ahb_lite_if ahb_vif);
    ahb_drv  = new("AHB_DRV"  , ahb_vif);
    rand_gen = new("RAND_GEN" , ahb_vif);
    ahb_mon  = new("AHB_MON"  , ahb_vif);
    ahb_cov  = new("AHB_COV"  , ahb_vif);
endfunction : new

task rand_test::connect();
    ahb_drv.gen2drv.connect(gen2drv);
    rand_gen.gen2drv.connect(gen2drv);
    
    ahb_mon.mon2cov.connect(mon2cov);
    ahb_cov.mon2cov.connect(mon2cov);
endtask : connect

task rand_test::run();
    fork
        ahb_drv.run();
        rand_gen.run();
        ahb_mon.run();
        ahb_cov.run();
    join_none
endtask : run

`endif // RAND_TEST__SV
