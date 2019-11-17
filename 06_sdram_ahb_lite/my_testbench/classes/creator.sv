/*
*  File            :   creator.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.14
*  Language        :   SystemVerilog
*  Description     :   This is class for creating components
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef CREATOR__SV
`define CREATOR__SV

typedef class base_class;

class creator #(type T);

    static function T create_obj(string name, base_class parent);
        T obj = new(name, parent);
        obj.full_name = { parent.full_name , "." , name };
        return obj;
    endfunction : create_obj

endclass : creator

`endif // CREATOR__SV
