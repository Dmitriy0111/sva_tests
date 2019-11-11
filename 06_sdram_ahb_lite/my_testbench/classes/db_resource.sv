/*
*  File            :   db_resource.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.11
*  Language        :   SystemVerilog
*  Description     :   This is resource database
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef DB_RESOURCE__SV
`define DB_RESOURCE__SV

class db_resource #(type T);

    static  test_resource   #(T)    res[$];

    extern static task         set(string name, T in_res);
    extern static function bit get(string name, inout T out_res);

endclass : db_resource

static task db_resource::set(string name, T in_res);
    test_resource #(T) new_res = new(in_res, name);
    test_resource #(T) test_queue [$];
    test_queue = res.find with( item.get_name() == name );
    if( test_queue.size() == 0 )
        res.push_back(new_res);
endtask : set

static function bit db_resource::get(string name, inout T out_res);
    test_resource #(T) test_res = new();
    foreach( res[i] )
        if( res[i].get_name() == name )
        begin
            out_res = res[i].res_value;
            return '1;
        end
    return '0;
endfunction : get

`endif // DB_RESOURCE__SV
