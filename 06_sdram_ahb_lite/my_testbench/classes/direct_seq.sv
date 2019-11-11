/*
*  File            :   direct_seq.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.11
*  Language        :   SystemVerilog
*  Description     :   This is direct sequence
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef DIRECT_SEQ__SV
`define DIRECT_SEQ__SV

class direct_seq extends base_seq;

    int     file_p = 0;

    extern function     new(string name);
    extern task         seq_run();
    extern function bit pars_file();

endclass : direct_seq

function direct_seq::new(string name);
    super.new(name);
    file_p = $fopen("../06_sdram_ahb_lite/my_testbench/direct_test.txt","r");
    if( file_p == 0 )
    begin
        $display("Direct test file not open!");
        $stop;
    end
endfunction : new

task direct_seq::seq_run();
    for(;;)
    begin
        if( !pars_file() )
            break;
    end
endtask : seq_run

// N addr data wr_rd size
function bit direct_seq::pars_file();
    logic   [31 : 0]    addr;
    logic   [31 : 0]    data;
    string              wr_rd;
    string              size;
    int                 N;
    if( $fscanf(file_p,"%d %h %h %s %s",N,addr,data,wr_rd,size) == -1 )
        return '0;
    item.addr = addr;
    item.data = data;
    item.N    = N;
    item.size = ( size == "WORD"  ? 3'b010 : 
                  size == "HWORD" ? 3'b001 :
                  size == "BYTE"  ? 3'b000 : 3'b010 );
    item.wr_rd = ( wr_rd == "WRITE"  ? '1 : '0 );
    return '1;
endfunction : pars_file

`endif // DIRECT_SEQ__SV
