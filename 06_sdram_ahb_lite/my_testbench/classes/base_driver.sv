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

endclass : base_driver

`endif // BASE_DRIVER__SV
