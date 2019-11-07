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

    ahb_driver                  ahb_drv;
    direct_gen                  direct_gen;
    ahb_monitor                 ahb_mon;
    ahb_coverage                ahb_cov;

    socket      #(ahb_trans)    gen2drv = new(2);
    socket      #(ahb_trans)    mon2cov = new(1);

    extern function new(name = "", virtual ahb_lite_if ahb_vif);
    extern task     connect();
    extern task     run();
    
endclass : direct_test

function direct_test::new(name = "", virtual ahb_lite_if ahb_vif);
    ahb_drv    = new("AHB_DRV"    , ahb_vif);
    direct_gen = new("DIRECT_GEN" , ahb_vif);
    ahb_mon    = new("AHB_MON"    , ahb_vif);
    ahb_cov    = new("AHB_COV"    , ahb_vif);
endfunction : new

task direct_test::connect();
    ahb_drv.gen2drv.connect(gen2drv);
    direct_gen.gen2drv.connect(gen2drv);

    ahb_mon.mon2cov.connect(mon2cov);
    ahb_cov.mon2cov.connect(mon2cov);
endtask : connect

task direct_test::run();
    fork
        ahb_drv.run();
        direct_gen.run();
        ahb_mon.run();
        ahb_cov.run();
    join_none
endtask : run

`endif // DIRECT_TEST__SV
