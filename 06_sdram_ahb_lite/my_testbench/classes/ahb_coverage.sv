/*
*  File            :   ahb_coverage.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.07
*  Language        :   SystemVerilog
*  Description     :   This is ahb driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef AHB_COVERAGE__SV
`define AHB_COVERAGE__SV

class ahb_coverage extends base_class;

    ahb_trans               ahb_trans_rec = new();

    socket  #(ahb_trans)    mon2cov = new();

    covergroup ahb_cg();
        ahb_haddr_cp : coverpoint ahb_trans_rec.addr
        {
            bins haddr[16] = { [0 : 2**14-1] };
        }
        ahb_hwrite_cp : coverpoint ahb_trans_rec.wr_rd
        {
            bins WRITE = { 1'b1 };
            bins READ  = { 1'b0 };
        }
        read_write_cp : coverpoint ahb_trans_rec.wr_rd
        {
            bins WRITE2READ  = ( 1'b1 => 1'b0 );
            bins READ2WRITE  = ( 1'b0 => 1'b1 );
            bins WRITE2WRITE = ( 1'b1 => 1'b1 );
            bins READ2READ   = ( 1'b0 => 1'b0 );
        }
        ahb_size_cp : coverpoint ahb_trans_rec.size
        {
            bins BYTE_S  = { 3'b000 };
            bins HWORD_S = { 3'b001 };
            bins WORD_S  = { 3'b010 };
        }
        ahb_haddr_hsize_hwrite_cross : cross ahb_haddr_cp, ahb_size_cp, ahb_hwrite_cp;
    endgroup : ahb_cg

    extern function new(string name, base_class parent);
    extern task     run();
    extern task     trig_cov();

endclass : ahb_coverage

function ahb_coverage::new(string name, base_class parent);
    this.name = name;
    this.ahb_cg = new();
    this.parent = parent;
endfunction : new

task ahb_coverage::run();
    forever
    begin
        mon2cov.rec_msg(ahb_trans_rec);
        $info( { this.name , ahb_trans_rec.to_str() } );
        this.trig_cov();
    end
endtask : run

task ahb_coverage::trig_cov();
    ahb_cg.sample();
endtask : trig_cov

`endif // AHB_COVERAGE__SV
