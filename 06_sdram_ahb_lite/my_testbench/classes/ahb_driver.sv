/*
*  File            :   ahb_driver.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.01
*  Language        :   SystemVerilog
*  Description     :   This is ahb driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef AHB_DRIVER__SV
`define AHB_DRIVER__SV

class ahb_driver extends base_driver #(ahb_trans);

    `OBJECT_BEGIN( ahb_driver )

    virtual ahb_lite_if     vif;

    ahb_trans               ahb_trans_0;

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
    extern task     set_haddr(logic [31 : 0] value);
    extern task     set_hburst(logic [2 : 0] value);
    extern task     set_hmastlock(logic [0 : 0] value);
    extern task     set_hprot(logic [3 : 0] value);
    extern task     set_hsel(logic [0 : 0] value);
    extern task     set_hsize(logic [2 : 0] value);
    extern task     set_htrans(logic [1 : 0] value);
    extern task     set_hwdata(logic [31 : 0] value);
    extern task     set_hwrite(logic [0 : 0] value);
    extern task     set_hready(logic [0 : 0] value);
    extern task     get_hrdata(ref logic [31 : 0] value);
    extern task     get_hreadyout(ref logic [0 : 0] value);
    extern task     get_hresp(ref logic [0 : 0] value);
    extern task     reset_signals();
    extern task     wait_clk();
    extern task     addr_pipe();
    extern task     data_pipe();
    extern task     build();
    extern task     run();

endclass : ahb_driver

function ahb_driver::new(string name, base_class parent);
    super.new(name,parent);
    if( !db_resource#(virtual ahb_lite_if)::get("ahb_test_if", vif) )
        $fatal();
    $display("Created %s", this.get_name());
endfunction : new

task ahb_driver::set_haddr(logic [31 : 0] value);
    vif.HADDR = value;
endtask : set_haddr

task ahb_driver::set_hburst(logic [2 : 0] value);
    vif.HBURST = value;
endtask : set_hburst

task ahb_driver::set_hmastlock(logic [0 : 0] value);
    vif.HMASTLOCK = value;
endtask : set_hmastlock

task ahb_driver::set_hprot(logic [3 : 0] value);
    vif.HPROT = value;
endtask : set_hprot

task ahb_driver::set_hsel(logic [0 : 0] value);
    vif.HSEL = value;
endtask : set_hsel

task ahb_driver::set_hsize(logic [2 : 0] value);
    vif.HSIZE = value;
endtask : set_hsize

task ahb_driver::set_htrans(logic [1 : 0] value);
    vif.HTRANS = value;
endtask : set_htrans

task ahb_driver::set_hwdata(logic [31 : 0] value);
    vif.HWDATA = value;
endtask : set_hwdata

task ahb_driver::set_hwrite(logic [0 : 0] value);
    vif.HWRITE = value;
endtask : set_hwrite

task ahb_driver::set_hready(logic [0 : 0] value);
    vif.HREADY = value;
endtask : set_hready

task ahb_driver::get_hrdata(ref logic [31 : 0] value);
    value = vif.HRDATA;
endtask : get_hrdata

task ahb_driver::get_hreadyout(ref logic [0 : 0] value);
    value = vif.HREADYOUT;
endtask : get_hreadyout

task ahb_driver::get_hresp(ref logic [0 : 0] value);
    value = vif.HRESP;
endtask : get_hresp

task ahb_driver::reset_signals();
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

task ahb_driver::wait_clk();
    @(posedge vif.HCLK);
endtask : wait_clk

task ahb_driver::addr_pipe();
    ahb_trans local_trans;
    item_sock.rec_msg(local_trans);
    ahb_trans_0.copy(local_trans);
    $info( { ahb_trans_0.full_name , ahb_trans_0.sprint() } );
    this.set_haddr(ahb_trans_0.addr);
    this.set_hsel('1);
    this.set_hwrite( ahb_trans_0.wr_rd );
    this.set_hsize( ahb_trans_0.size );
    this.set_htrans(2'b10);
    this.set_hready('1);
    for(;;)
    begin
        this.wait_clk();
        if( vif.HREADYOUT == '1 )
            break;
    end
    this.set_hready('0);
    item_sock.trig_side();
endtask : addr_pipe

task ahb_driver::data_pipe();
    this.set_hwdata(ahb_trans_0.data);
    for(;;)
    begin
        this.wait_clk();
        if( vif.HREADYOUT == '1 )
            break;
    end
endtask : data_pipe

task ahb_driver::build();
    ahb_trans_0 = ahb_trans::creator_::create_obj("AHB_ITEM",this);
endtask : build

task ahb_driver::run();
    @(posedge vif.HRESETn);
    this.reset_signals();
    forever
    begin
        addr_pipe();
        fork
            data_pipe();
        join_none
    end
endtask : run

`endif // AHB_DRIVER__SV
