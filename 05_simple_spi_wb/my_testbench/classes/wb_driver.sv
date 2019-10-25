/*
*  File            :   wb_driver.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.25
*  Language        :   SystemVerilog
*  Description     :   This is wishbone driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef WB_DRIVER__SV
`define WB_DRIVER__SV

class wb_driver;

    virtual wb_if   wb_vif;

    function new(virtual wb_if wb_vif);
        this.wb_vif = wb_vif;
    endfunction : new

    task set_adr(logic [31 : 0] v);
        wb_vif.ADR = v;
    endtask : set_adr

    task set_data_o(logic [31 : 0] v);
        wb_vif.DATA_O = v;
    endtask : set_data_o

    function logic [31 : 0] read_data_i();
        return wb_vif.DATA_I;
    endfunction : read_data_i

    function logic [0 : 0] read_ack();
        return wb_vif.ACK;
    endfunction : read_ack

    task set_we(logic [0 : 0] v);
        wb_vif.WE = v;
    endtask : set_we

    task set_stb(logic [0 : 0] v);
        wb_vif.STB = v;
    endtask : set_stb

    task set_cyc(logic [0 : 0] v);
        wb_vif.CYC = v;
    endtask : set_cyc

    task we_h();
        this.set_we('1);
    endtask : we_h

    task we_l();
        this.set_we('0);
    endtask : we_l

    task stb_h();
        this.set_stb('1);
    endtask : stb_h

    task stb_l();
        this.set_stb('0);
    endtask : stb_l

    task cyc_h();
        this.set_cyc('1);
    endtask : cyc_h

    task cyc_l();
        this.set_cyc('0);
    endtask : cyc_l

    task wait_clk(integer n=1);
        repeat(n)
        @(posedge wb_vif.CLK);
    endtask : wait_clk

    task wait_ack();
        @(posedge wb_vif.ACK);
    endtask : wait_ack

    task reset_signals();
        this.we_l();
        this.stb_l();
        this.cyc_l();
        this.set_adr('0);
        this.set_data_o('0);
    endtask : reset_signals

    task write_data(logic [7 : 0] w_addr, logic [7 : 0] w_data);
        this.set_adr(w_addr);
        this.set_data_o(w_data);
        this.we_h();
        this.cyc_h();
        this.stb_h();
        this.wait_ack();
        this.wait_clk();
        this.we_l();
        this.cyc_l();
        this.stb_l();
        this.wait_clk();
    endtask : write_data

    task read_data(logic [7 : 0] r_addr, ref logic [7 : 0] r_data);
        this.set_adr(r_addr);
        this.we_l();
        this.cyc_h();
        this.stb_h();
        this.wait_ack();
        r_data = this.read_data_i();
        this.wait_clk();
        this.we_l();
        this.cyc_l();
        this.stb_l();
        this.wait_clk();
    endtask : read_data

endclass : wb_driver

`endif // WB_DRIVER__SV
