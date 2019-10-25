/*
*  File            :   wb_if.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.25
*  Language        :   SystemVerilog
*  Description     :   This is wishbone interface
*  Copyright(c)    :   2019 Vlasov D.V.
*/

interface wb_if(input logic CLK, input logic RST);

    logic   [7 : 0]     ADR;
    logic   [7 : 0]     DATA_O;
    logic   [7 : 0]     DATA_I;
    logic   [0 : 0]     WE;
    logic   [0 : 0]     STB;
    logic   [0 : 0]     ACK;
    logic   [0 : 0]     CYC;

    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                       Properties                                      //
    ///////////////////////////////////////////////////////////////////////////////////////////

    property unk_data_wr;
        @(posedge CLK)
        disable iff( RST )
        ( WE && STB && CYC ) |-> ( !$isunknown(DATA_O) );
    endproperty : unk_data_wr

    property unk_addr_wr;
        @(posedge CLK)
        disable iff( RST )
        ( WE && STB && CYC ) |-> ( !$isunknown(ADR) );
    endproperty : unk_addr_wr
    
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                  Assertions and covers                                //
    ///////////////////////////////////////////////////////////////////////////////////////////

    unk_data_wr_a : assert property( unk_data_wr ) else $warning("unk_data_wr_a: FAIL");
    unk_data_wr_c : cover  property( unk_data_wr )      ;// $info("unk_data_wr_a: PASS");

    unk_addr_wr_a : assert property( unk_addr_wr ) else $warning("unk_addr_wr_a: FAIL");
    unk_addr_wr_c : cover  property( unk_addr_wr )      ;// $info("unk_addr_wr_a: PASS");

endinterface : wb_if
