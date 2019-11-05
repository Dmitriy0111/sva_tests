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

class ahb_driver;

    virtual ahb_lite_if     vif;
    string                  name;

    sock_data               write_sock_data;
    sock_data               read_sock_data;

    socket  #(sock_data)    write_sock = new(2);
    socket  #(sock_data)    read_sock = new(2);

    logic   [31 : 0]        haddr_q [$];
    logic   [31 : 0]        hdata_q [$];

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

    function new(string name, virtual ahb_lite_if vif);
        this.name = name;
        this.vif = vif;
    endfunction : new

    task connect_write_sock(socket #(sock_data) write_sock);
        this.write_sock = write_sock;
    endtask : connect_write_sock

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

    task addr_pipe();
        write_sock.rec_msg(0, write_sock_data);
        $info("%s write addr = 0x%h write data = 0x%h", name, write_sock_data.addr, write_sock_data.data);
        this.set_haddr(write_sock_data.addr);
        this.set_hsel('1);
        this.set_hwrite('1);
        this.set_hsize(3'b010);
        this.set_htrans(2'b10);
        this.set_hready('1);
        do
        begin
            this.wait_clk();
        end
        while( vif.HREADYOUT != '1 );
        this.set_hready('0);
        write_sock.trig_side(1);
    endtask : addr_pipe

    task data_pipe();
        this.set_hwdata(write_sock_data.data);
        do
        begin
            this.wait_clk();
        end
        while( vif.HREADYOUT != '1 );
    endtask : data_pipe

    task run();
        forever
        begin
            addr_pipe();
            fork
                data_pipe();
            join_none
        end
    endtask : run

endclass : ahb_driver

`endif // AHB_DRIVER__SV
