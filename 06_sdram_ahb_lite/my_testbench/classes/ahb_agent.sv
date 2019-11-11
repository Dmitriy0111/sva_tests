/*
*  File            :   ahb_agent.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.08
*  Language        :   SystemVerilog
*  Description     :   This is ahb agent
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef AHB_AGENT__SV
`define AHB_AGENT__SV

class ahb_agent extends base_class;

    ahb_driver                  ahb_drv;
    ahb_monitor                 ahb_mon;
    ahb_coverage                ahb_cov;
    socket      #(ahb_trans)    mon2cov = new();

    extern function new(string name, base_class parent);
    extern task     connect();
    extern task     run();

endclass : ahb_agent

function ahb_agent::new(string name, base_class parent);
    this.name = name;
    this.parent = parent;
    ahb_drv  = new("AHB_DRV", this);
    ahb_mon  = new("AHB_MON", this);
    ahb_cov  = new("AHB_COV", this);
endfunction : new

task ahb_agent::connect();
    ahb_mon.mon2cov.connect(mon2cov);
    ahb_cov.mon2cov.connect(mon2cov);
endtask : connect

task ahb_agent::run();
    fork
        ahb_drv.run();
        ahb_mon.run();
        ahb_cov.run();
    join_none
endtask : run

`endif // AHB_AGENT__SV
