/*
*  File            :   random_gen.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.06
*  Language        :   SystemVerilog
*  Description     :   This is random test generator
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef RANDOM_GEN__SV
`define RANDOM_GEN__SV

class random_gen extends base_gen;

    extern function new(string name);
    extern task     run();

endclass : random_gen

function random_gen::new(string name);
    super.new(name, vif);
    db_resource#(virtual ahb_lite_if)::get("ahb_test_if", vif);
endfunction : new

task random_gen::run();
    @(posedge vif.HRESETn);
    repeat(200) @(posedge vif.HCLK);
    
    repeat(20000)
    begin
        ahb_tr.make_tr();
        gen2drv.send_msg(ahb_tr);
        gen2drv.wait_side();
    end
endtask : run

`endif // RANDOM_GEN__SV
