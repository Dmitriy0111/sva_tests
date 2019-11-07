/*
*  File            :   base_gen.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.06
*  Language        :   SystemVerilog
*  Description     :   This is base test generator
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef BASE_GEN__SV
`define BASE_GEN__SV

class base_gen;

    virtual ahb_lite_if     vif;
    string                  name;

    ahb_trans               ahb_tr = new();

    socket  #(ahb_trans)    gen2drv = new(2);

    extern function new(string name = "", virtual ahb_lite_if vif = null);
    extern virtual task run();

endclass : base_gen

function base_gen::new(string name = "", virtual ahb_lite_if vif = null);
    this.name = name;
    this.vif = vif;
endfunction : new

task base_gen::run();
endtask : run

`endif // BASE_GEN__SV
