/*
*  File            :   ahb_coverage.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.07
*  Language        :   SystemVerilog
*  Description     :   This is ahb driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef AHB_COVERAGE__SV
`define AHB_COVERAGE__SV

class ahb_coverage;

    virtual ahb_lite_if     vif;
    string                  name;

    ahb_trans               ahb_trans_rec = new();

    socket  #(ahb_trans)    mon2cov = new(1);

    extern function new(string name, virtual ahb_lite_if vif);
    extern task     run();

endclass : ahb_coverage

function ahb_coverage::new(string name, virtual ahb_lite_if vif);
    this.name = name;
    this.vif = vif;
endfunction : new

task ahb_coverage::run();
    forever
    begin
        mon2cov.rec_msg(0, ahb_trans_rec);
        $info( { this.name , ahb_trans_rec.to_str() } );
    end
endtask : run

`endif // AHB_COVERAGE__SV
