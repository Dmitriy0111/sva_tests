/*
*  File            :   base_seq.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.11
*  Language        :   SystemVerilog
*  Description     :   This is base sequence
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef BASE_SEQ__SV
`define BASE_SEQ__SV

class base_seq extends base_class;

    ahb_trans   item;

    extern         function new(string name);
    extern virtual task     seq_run();

endclass : base_seq

function base_seq::new(string name);
    this.name = name;
endfunction : new

task base_seq::seq_run();
endtask : seq_run

`endif // BASE_SEQ__SV
