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

class ahb_monitor extends base_class;

    virtual ahb_lite_if     vif;

    ahb_trans               ahb_trans_0 = new();

    socket  #(ahb_trans)    mon2cov = new();

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

    extern function new(string name, base_class parent);
    extern task     wait_clk();
    extern task     wait_data_cycle(ahb_trans ahb_trans_);
    extern task     run();

endclass : ahb_monitor

function ahb_monitor::new(string name, base_class parent);
    this.name = name;
    this.parent = parent;
    if( !db_resource#(virtual ahb_lite_if)::get("ahb_test_if", vif) )
        $fatal();
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
    local_trans.copy(ahb_trans_);
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
    mon2cov.send_msg(local_trans);
    $info( { this.name , local_trans.to_str() } );
endtask : wait_data_cycle

`endif // AHB_MONITOR__SV
