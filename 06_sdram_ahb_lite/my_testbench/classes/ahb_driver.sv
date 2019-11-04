/*
*  File            :   ahb_driver.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.01.01
*  Language        :   SystemVerilog
*  Description     :   This is ahb driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef AHB_DRIVER__SV
`define AHB_DRIVER__SV

class ahb_driver;

    virtual ahb_lite_if     vif;
    string                  name;

    function new(string name, virtual ahb_lite_if vif);
        this.name = name;
        this.vif = vif;
    endfunction : new

    task set_haddr(logic [31 : 0] value);
        vif.HADDR = value;
    endtask : set_haddr

    task set_hburst(logic [2 : 0] value);
        vif.HBURST = value;
    endtask : set_hburst

    task set_hmastlock(logic [0 : 0] value);
        vif.HMASTLOCK = value;
    endtask : set_hmastlock

    task set_hprot(logic [3 : 0] value);
        vif.HPROT = value;
    endtask : set_hprot

    task set_hsel(logic [0 : 0] value);
        vif.HSEL = value;
    endtask : set_hsel

    task set_hsize(logic [2 : 0] value);
        vif.HSIZE = value;
    endtask : set_hsize

    task set_htrans(logic [1 : 0] value);
        vif.HTRANS = value;
    endtask : set_htrans

    task set_hwdata(logic [31 : 0] value);
        vif.HWDATA = value;
    endtask : set_hwdata

    task set_hwrite(logic [0 : 0] value);
        vif.HWRITE = value;
    endtask : set_hwrite

    task set_hready(logic [0 : 0] value);
        vif.HREADY = value;
    endtask : set_hready

    task get_hrdata(ref logic [31 : 0] value);
        value = vif.HRDATA;
    endtask : get_hrdata

    task get_hreadyout(ref logic [0 : 0] value);
        value = vif.HREADYOUT;
    endtask : get_hreadyout

    task get_hresp(ref logic [0 : 0] value);
        value = vif.HRESP;
    endtask : get_hresp

    task reset_signals();
        this.set_haddr('0);
        this.set_hburst('0);
        this.set_hmastlock('0);
        this.set_hprot('0);
        this.set_hsel('0);
        this.set_hsize('0);
        this.set_htrans('0);
        this.set_hwdata('0);
        this.set_hwrite('0);
        this.set_hready('0);
    endtask : reset_signals

    task wait_clk();
        @(posedge vif.HCLK);
    endtask : wait_clk

    task write_data(logic [31 : 0] w_addr, logic [31 : 0] w_data);
        this.set_haddr(w_addr);
        this.set_hwdata(w_data);
        this.set_hsel('1);
        this.set_hsize(3'b010);
        this.wait_clk();
        
    endtask : write_data

endclass : ahb_driver

`endif // AHB_DRIVER__SV
