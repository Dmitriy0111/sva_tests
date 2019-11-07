/*
*  File            :   direct_gen.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.06
*  Language        :   SystemVerilog
*  Description     :   This is direct test generator
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef DIRECT_GEN__SV
`define DIRECT_GEN__SV

class direct_gen extends base_gen;

    int     file_p = 0;

    extern function     new(string name, virtual ahb_lite_if vif);
    extern task         run();
    extern function bit pars_file();

endclass : direct_gen

function direct_gen::new(string name, virtual ahb_lite_if vif);
    super.new(name, vif);
    file_p = $fopen("../06_sdram_ahb_lite/my_testbench/direct_test.txt","r");
    if( file_p == 0 )
    begin
        $display("Direct test file not open!");
        $stop;
    end
endfunction : new

task direct_gen::run();
    @(posedge vif.HRESETn);
    repeat(200) @(posedge vif.HCLK);
    
    for(;;)
    begin
        if( !pars_file() )
            break;
        if( ahb_tr.wr_rd == '1 )
            gen2drv.send_msg(0, ahb_tr);
        gen2drv.wait_side(1);
    end
endtask : run

// N addr data wr_rd size
function bit direct_gen::pars_file();
    logic   [31 : 0]    addr;
    logic   [31 : 0]    data;
    string              wr_rd;
    string              size;
    int                 N;
    if( $fscanf(file_p,"%d %h %h %s %s",N,addr,data,wr_rd,size) == -1 )
        return '0;
    ahb_tr.addr = addr;
    ahb_tr.data = data;
    ahb_tr.N    = N;
    ahb_tr.size = ( size == "WORD"  ? 3'b010 : 
                    size == "HWORD" ? 3'b001 :
                    size == "BYTE"  ? 3'b000 : 3'b010 );
    ahb_tr.wr_rd = ( wr_rd == "WRITE"  ? '1 : '0 );
    return '1;
endfunction : pars_file

`endif // DIRECT_GEN__SV
