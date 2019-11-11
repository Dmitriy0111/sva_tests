/*
*  File            :   rand_seq.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.11
*  Language        :   SystemVerilog
*  Description     :   This is random sequence
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef RAND_SEQ__SV
`define RAND_SEQ__SV

class rand_seq extends base_seq;

    extern function new(string name);
    extern task     seq_run();

endclass : rand_seq

function rand_seq::new(string name);
    super.new(name);
    this.name = name;
endfunction : new

task rand_seq::seq_run();
    repeat(20000)
    begin
        item.make_tr();
    end
endtask : seq_run

`endif // RAND_SEQ__SV
