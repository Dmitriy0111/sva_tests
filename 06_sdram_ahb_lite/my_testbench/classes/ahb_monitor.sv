/*
*  File            :   ahb_monitor.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.07
*  Language        :   SystemVerilog
*  Description     :   This is ahb driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef AHB_MONITOR__SV
`define AHB_MONITOR__SV

class ahb_monitor;

    virtual ahb_lite_if     vif;
    string                  name;

    ahb_trans               ahb_trans_0 = new();

    socket  #(ahb_trans)    mon2cov = new(1);

    /* 
        ahb_slave signals
                               --------------
        HSEL        -[0  : 0]->| AHB slave  |
        HADDR       -[31 : 0]->|            |
        HWRITE      -[0  : 0]->|            |-[0  : 0]->HREADYOUT
        HSIZE       -[2  : 0]->|            |-[0  : 0]->HRESP
        HBURST      -[2  : 0]->|            |
        HPROT       -[3  : 0]->|            |-[31 : 0]->HRDATA
        HTRANS      -[1  : 0]->|            |
        HMASTLOCK   -[0  : 0]->|            |
        HREADY      -[0  : 0]->|            |
                               |            |
        HWDATA      -[31 : 0]->|            |
                               --------------
    */

    extern function new(string name, virtual ahb_lite_if vif);
    extern task     wait_clk();
    extern task     wait_data_cycle(ahb_trans ahb_trans_);
    extern task     run();

endclass : ahb_monitor

function ahb_monitor::new(string name, virtual ahb_lite_if vif);
    this.name = name;
    this.vif = vif;
endfunction : new

task ahb_monitor::wait_clk();
    @(posedge vif.HCLK);
endtask : wait_clk

task ahb_monitor::run();
    @(posedge vif.HRESETn);
    forever
    begin
        #0;
        this.wait_clk();
        if( vif.HREADY && vif.HSEL && vif.HREADYOUT )
        begin
            ahb_trans_0.N++;
            ahb_trans_0.wr_rd = vif.HWRITE;
            ahb_trans_0.addr = vif.HADDR;
            ahb_trans_0.size = vif.HSIZE;
            fork
                wait_data_cycle(ahb_trans_0);
            join_none
        end
    end
endtask : run

task ahb_monitor::wait_data_cycle(ahb_trans ahb_trans_);
    ahb_trans local_trans = new();
    local_trans.N = ahb_trans_.N;
    local_trans.addr = ahb_trans_.addr;
    local_trans.data = ahb_trans_.data;
    local_trans.size = ahb_trans_.size;
    local_trans.wr_rd = ahb_trans_.wr_rd;
    if( local_trans.wr_rd )
    begin
        this.wait_clk();
        local_trans.data = vif.HWDATA;
    end
    else
    begin
        for(;;)
        begin
            this.wait_clk();
            if( vif.HREADYOUT == '1 )
            begin
                local_trans.data = vif.HRDATA;
                break;
            end
        end
    end
    mon2cov.send_msg(0,local_trans);
    $info( { this.name , local_trans.to_str() } );
endtask : wait_data_cycle

`endif // AHB_MONITOR__SV
