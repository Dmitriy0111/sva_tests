/*
*  File            :   base_class.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.07
*  Language        :   SystemVerilog
*  Description     :   This is ahb driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef BASE_CLASS__SV
`define BASE_CLASS__SV

class base_class;

    string          name;

    base_class      parent;

    extern virtual task run();

endclass : base_class

task base_class::run();
endtask : run

`endif // BASE_CLASS__SV
