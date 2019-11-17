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

class ahb_trans extends base_class;

    `OBJECT_BEGIN( ahb_trans )

    rand    logic   [31 : 0]    addr;
    rand    logic   [31 : 0]    data;
    rand    logic   [0  : 0]    wr_rd;
    rand    logic   [2  : 0]    size;
    
    string                      size_str;
    string                      wr_rd_str;
    int                         tr_number = 0;

    `FIELD_BEGIN( ahb_trans )
        `FIELD_INT          ( tr_number , `ALL_FLAGS_ON | `RADIX_DEC )
        `FIELD_INT          ( addr      , `ALL_FLAGS_ON | `RADIX_HEX )
        `FIELD_INT          ( data      , `ALL_FLAGS_ON | `RADIX_HEX )
        `FIELD_INT          ( wr_rd     , `ALL_FLAGS_ON | `RADIX_HEX )
        `FIELD_INT          ( size      , `ALL_FLAGS_ON | `RADIX_HEX )
        `FIELD_STRING       ( wr_rd_str , `ALL_FLAGS_ON              )
        `FIELD_STRING       ( size_str  , `ALL_FLAGS_ON              )
    `FIELD_END

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
    extern task            make_tr();
    extern function void   post_randomize();
    extern task            str2logic_fields();
    extern task            logic2str_fields();

    function new(string name ="", base_class parent = null);
        super.new(name, parent);
    endfunction : new

endclass : ahb_trans

function string ahb_trans::to_str();
    string ret_str;
    ret_str = { ret_str , $psprintf("\nTR_NUMBER = %0d", tr_number) };
    ret_str = { ret_str , $psprintf("\nTR_ADDR   = 0x%h", addr) };
    ret_str = { ret_str , $psprintf("\nTR_DATA   = 0x%h", data) };
    ret_str = { ret_str , $psprintf("\nTR_SIZE   = %s", size_str) };
    ret_str = { ret_str , $psprintf("\nWR_RD     = %s", wr_rd_str) };
    return ret_str;
endfunction : to_str

task ahb_trans::make_tr();
    if( !this.randomize() )
        $fatal("randomization error!");
    tr_number++;
endtask : make_tr

function void ahb_trans::post_randomize();
    this.logic2str_fields();
endfunction : post_randomize

task ahb_trans::str2logic_fields();
    case( wr_rd_str )
        "READ"  : wr_rd = 1'b0;
        "WRITE" : wr_rd = 1'b1;
        default : wr_rd = 1'b1;
    endcase
    case( size_str )
        "BYTE"  : size = 3'b000;
        "HWORD" : size = 3'b001;
        "WORD"  : size = 3'b010;
        default : size = 3'b010;
    endcase
endtask : str2logic_fields

task ahb_trans::logic2str_fields();
    case( wr_rd )
        1'b0    : wr_rd_str = "READ";
        1'b1    : wr_rd_str = "WRITE";
        default : wr_rd_str = "UNK";
    endcase
    case( size )
        3'b000  : size_str = "BYTE";
        3'b001  : size_str = "HWORD";
        3'b010  : size_str = "WORD";
        default : size_str = "UNK";
    endcase
endtask : logic2str_fields

`endif // AHB_TRANS__SV
