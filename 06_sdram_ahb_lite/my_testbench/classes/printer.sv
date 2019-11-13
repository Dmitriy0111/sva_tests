/*
*  File            :   printer.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.12
*  Language        :   SystemVerilog
*  Description     :   This is printer task
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef PRINTER__SV
`define PRINTER__SV

typedef struct {
    string  name;
    string  size;
    string  val;
} print_item;

class printer;

    print_item      print_item_q [$];

    int             name_len = 0;
    int             val_len = 0;
    int             size_len = 0;

    extern task            print_item_int(logic [31 : 0] value, int size_b, int radix, string name);
    extern task            print_item_enum(logic [31 : 0] value, string value_str, int size_b, int radix, string name);
    extern task            print_item_string(string value, string name);
    extern task            find_max_item_len();
    extern task            print_items();
    extern task            print_items_table();
    extern function string sprint_items_table();

endclass : printer

task printer::print_item_int(logic [31 : 0] value, int size_b, int radix, string name);
    print_item local_item;
    local_item.size = $psprintf("%0d", size_b );
    local_item.name = name;
    case( radix & `RADIX_MASK)
        `RADIX_BIN  : local_item.val = $psprintf("'b%0b", value);
        `RADIX_OCT  : local_item.val = $psprintf("'o%0o", value);
        `RADIX_DEC  : local_item.val = $psprintf("'d%0d", value);
        `RADIX_HEX  : local_item.val = $psprintf("'h%0h", value);
        default     : local_item.val = $psprintf("'d%0d", value);
    endcase
    print_item_q.push_back(local_item);
endtask : print_item_int

task printer::print_item_enum(logic [31 : 0] value, string value_str, int size_b, int radix, string name);
    print_item local_item;
    local_item.name = name;
    local_item.size = $psprintf("%0d", size_b );
    case( radix & `RADIX_MASK)
        `RADIX_BIN  : local_item.val = $psprintf("%s('b%0b)", value_str, value);
        `RADIX_OCT  : local_item.val = $psprintf("%s('o%0o)", value_str, value);
        `RADIX_DEC  : local_item.val = $psprintf("%s('d%0d)" , value_str, value);
        `RADIX_HEX  : local_item.val = $psprintf("%s('h%0h)", value_str, value);
        default     : local_item.val = $psprintf("%s('d%0d)" , value_str, value);
    endcase
    print_item_q.push_back(local_item);
endtask : print_item_enum

task printer::print_item_string(string value, string name);
    print_item local_item;
    local_item.name = name;
    local_item.val = value;
    local_item.size = $psprintf("%0d", value.len() );
    print_item_q.push_back(local_item);
endtask : print_item_string

task printer::find_max_item_len();
    if( ( name_len == 0 ) && ( val_len == 0 ) && ( size_len == 0 ))
        begin
        foreach( print_item_q[i] )
        begin
            if( name_len < print_item_q[i].name.len() )
                name_len = print_item_q[i].name.len();
            if( val_len < print_item_q[i].val.len() )
                val_len = print_item_q[i].val.len();
            if( size_len < print_item_q[i].size.len())
                size_len = print_item_q[i].size.len();
        end
        name_len += 4;
        size_len += 4;
    end
endtask : find_max_item_len

task printer::print_items();
    string local_str;
    for( ; print_item_q.size() != 0 ; )
    begin
        local_str = { print_item_q[0].name , " " , print_item_q[0].val };
        print_item_q.pop_front();
        $display(local_str);
    end
endtask : print_items

task printer::print_items_table();
    string header;
    string local_str;
    find_max_item_len();
    header = { "Name" , { ( name_len - 4 ) {" "} } , "Size" , { ( size_len - 4 ) {" "} } , "Value" };
    $display( header );
    for( ; print_item_q.size() != 0 ; )
    begin
        local_str = { print_item_q[0].name , { ( name_len - print_item_q[0].name.len() ) { " " } } , print_item_q[0].size , { ( size_len - print_item_q[0].size.len() ) { " " } } , print_item_q[0].val };
        print_item_q.pop_front();
        $display(local_str);
    end
endtask : print_items_table

function string printer::sprint_items_table();
    string ret_str;
    find_max_item_len();
    ret_str = { "\nName" , { ( name_len - 4 ) {" "} } , "Size" , { ( size_len - 4 ) {" "} } , "Value" };
    for( ; print_item_q.size() != 0 ; )
    begin
        ret_str = { ret_str , { "\n" , print_item_q[0].name , { ( name_len - print_item_q[0].name.len() ) { " " } } , print_item_q[0].size , { ( size_len - print_item_q[0].size.len() ) { " " } } , print_item_q[0].val } };
        print_item_q.pop_front();
    end
    return ret_str;
endfunction : sprint_items_table

`endif // PRINTER__SV
