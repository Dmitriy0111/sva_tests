/*
*  File            :   macro.svh
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.12
*  Language        :   SystemVerilog
*  Description     :   This is file with macro functions
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef MACRO__SV
`define MACRO__SV

`define PRINT_FLAG_N    1
`define COPY_FLAG_N     2
`define RADIX_BIN_N     3
`define RADIX_OCT_N     4
`define RADIX_DEC_N     5
`define RADIX_HEX_N     6

`define PRINT_FLAG      ( 32'h1 << `PRINT_FLAG_N )
`define COPY_FLAG       ( 32'h1 << `COPY_FLAG_N )
`define RADIX_BIN       ( 32'h1 << `RADIX_BIN_N )
`define RADIX_OCT       ( 32'h1 << `RADIX_OCT_N )
`define RADIX_DEC       ( 32'h1 << `RADIX_DEC_N )
`define RADIX_HEX       ( 32'h1 << `RADIX_HEX_N )
`define RADIX_DEF       `RADIX_DEC
`define RADIX_MASK      ( `RADIX_BIN | `RADIX_OCT | `RADIX_DEC | `RADIX_HEX)

`define ALL_FLAGS_ON    ( `PRINT_FLAG | `COPY_FLAG )
`define ALL_FLAGS_OFF   'h00

`define FIELD_STRING( ARG , FLAGS ) \
    case( operation ) \
        `PRINT_FLAG: \
            begin \
                if( FLAGS & `PRINT_FLAG ) \
                    printer_.print_item_string(ARG,`"ARG`"); \
            end \
        `COPY_FLAG: \
            begin \
                if( FLAGS & `COPY_FLAG ) \
                    ARG = local_obj.ARG; \
            end \
    endcase \

`define FIELD_INT( ARG , FLAGS ) \
    case( operation ) \
        `PRINT_FLAG: \
            begin \
                if( FLAGS & `PRINT_FLAG ) \
                    printer_.print_item_int(ARG,$bits(ARG) ,FLAGS,`"ARG`"); \
            end \
        `COPY_FLAG: \
            begin \
                if( FLAGS & `COPY_FLAG ) \
                    ARG = local_obj.ARG; \
            end \
    endcase \

`define FIELD_ENUM( ARG , FLAGS ) \
    case( operation ) \
        `PRINT_FLAG: \
            begin \
                if( FLAGS & `PRINT_FLAG ) \
                    printer_.print_item_enum(ARG,ARG.name,$bits(ARG),FLAGS,`"ARG`"); \
            end \
        `COPY_FLAG: \
            begin \
                if( FLAGS & `COPY_FLAG ) \
                    ARG = local_obj.ARG; \
            end \
    endcase \

`define FIELD_INT_ARR( ARG , FLAGS ) \
    case( operation ) \
        `PRINT_FLAG: \
            begin \
                if( FLAGS & `PRINT_FLAG ) \
                    foreach( ARG[i] ) \
                        printer_.print_item_int(ARG[i],$bits(ARG[i]) ,FLAGS, { `"ARG`" , $psprintf("[%0d]", i) } ); \
            end \
        `COPY_FLAG: \
            begin \
                if( FLAGS & `COPY_FLAG ) \
                    ARG = local_obj.ARG; \
            end \
    endcase \

`define FIELD_BEGIN(T) \
    function void help_f(base_class this_obj, logic [7 : 0] operation); \
        T   local_obj; \
        $cast(local_obj, this_obj); \

`define FIELD_END \
    endfunction : help_f \

`endif // MACRO__SV
