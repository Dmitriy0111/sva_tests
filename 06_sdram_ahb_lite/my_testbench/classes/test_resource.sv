/*
*  File            :   test_resource.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.11
*  Language        :   SystemVerilog
*  Description     :   This is resource class
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef TEST_RESOURCE__SV
`define TEST_RESOURCE__SV

class test_resource #(type T);

    T       res_value;
    string  res_name;

    extern function        new(T res_value = null, string res_name="");
    extern function string get_name();

endclass : test_resource

function test_resource::new(T res_value = null, string res_name="");
    this.res_value = res_value;
    this.res_name = res_name;
endfunction : new

function string test_resource::get_name();
    return this.res_name;
endfunction : get_name

`endif // TEST_RESOURCE__SV
