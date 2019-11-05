/*
*  File            :   ahb_driver.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.01
*  Language        :   SystemVerilog
*  Description     :   This is ahb driver
*  Copyright(c)    :   2019 Vlasov D.V.
*/

package test_pkg;

    typedef struct
    {
        logic   [31 : 0]    addr;
        logic   [31 : 0]    data;
        logic   [0  : 0]    op;
    } sock_data;

    `include    "classes/socket.sv"
    `include    "classes/ahb_driver.sv"

endpackage : test_pkg
