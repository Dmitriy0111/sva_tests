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

class direct_test;

    ahb_driver                  ahb_driver_0;
    direct_gen                  direct_gen_0;
    socket      #(ahb_trans)    gen2drv = new(2);

    extern function new(name = "", virtual ahb_lite_if ahb_vif);
    extern task     connect();
    extern task     run();
    
endclass : direct_test

function direct_test::new(name = "", virtual ahb_lite_if ahb_vif);
    ahb_driver_0 = new("AHB_DRIVER", ahb_vif);
    direct_gen_0 = new("DIRECT_GEN", ahb_vif);
endfunction : new

task direct_test::connect();
    ahb_driver_0.gen2drv.connect(gen2drv);
    direct_gen_0.gen2drv.connect(gen2drv);
endtask : connect

task direct_test::run();
    fork
        ahb_driver_0.run();
        direct_gen_0.run();
    join
endtask : run

`endif // DIRECT_TEST__SV
