/*
*  File            :   base_driver.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.11
*  Language        :   SystemVerilog
*  Description     :   This is base driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef BASE_DRIVER__SV
`define BASE_DRIVER__SV

class base_driver #(type seq_type) extends base_class;

    socket  #(seq_type)     item_sock = new();

    extern function new(string name, base_class parent);

endclass : base_driver

function base_driver::new(string name, base_class parent);
    super.new(name,parent);
endfunction : new

`endif // BASE_DRIVER__SV
