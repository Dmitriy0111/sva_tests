/*
*  File            :   ahb_trans.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.01
*  Language        :   SystemVerilog
*  Description     :   This is ahb transaction
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef AHB_TRANS__SV
`define AHB_TRANS__SV

class ahb_trans;

    string                      name;

    rand    logic   [31 : 0]    addr;
    rand    logic   [31 : 0]    data;
    rand    logic   [0  : 0]    wr_rd;
    rand    logic   [2  : 0]    size;

    int                         N = 0;

    constraint addr_c {
        addr inside { [0 : 2**14-1] };
        ( addr & 3 ) == '0;
    }

    constraint data_c {
        data inside { [0 : 2**32-1] };
    }

    constraint wr_rd_c {
        wr_rd inside { 1'b0, 1'b1 };
    }

    constraint size_c {
        size inside { 3'b010 , 3'b001 , 3'b000 };
    }

    extern function string to_str();
    extern task            print();
    extern task            make_tr();
    extern task            copy(ahb_trans other_ahb_trans);

endclass : ahb_trans

function string ahb_trans::to_str();
    string ret_str;
    ret_str = { ret_str , $psprintf("\nTR_NUMBER = %d", N) };
    ret_str = { ret_str , $psprintf("\nTR_ADDR   = 0x%h", addr) };
    ret_str = { ret_str , $psprintf("\nTR_DATA   = 0x%h", data) };
    ret_str = { ret_str , $psprintf("\nTR_SIZE   = %s", ( ( size == 3'b010 ) ? "WORD ": ( size == 3'b001 ) ? "HWORD" : ( size == 3'b000 ) ? "BYTE " : "UNK" ) ) };
    ret_str = { ret_str , $psprintf("\nWR_RD     = %s", wr_rd ? "WRITE" : "READ ") };
    return ret_str;
endfunction : to_str

task ahb_trans::print();
    $info(this.to_str());
endtask : print

task ahb_trans::make_tr();
    if( !this.randomize() )
        $fatal("randomization error!");
    N++;
endtask : make_tr

task ahb_trans::copy(ahb_trans other_ahb_trans);
    this.name = other_ahb_trans.name;
    this.addr = other_ahb_trans.addr;
    this.data = other_ahb_trans.data;
    this.wr_rd = other_ahb_trans.wr_rd;
    this.size = other_ahb_trans.size;
    this.N = other_ahb_trans.N;
endtask : copy

`endif // AHB_TRANS__SV
