/*
*  File            :   ahb_lite_if.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.01.01
*  Language        :   SystemVerilog
*  Description     :   This is ahb lite interface
*  Copyright(c)    :   2019 Vlasov D.V.
*/

interface ahb_lite_if(
    input   logic   [0 : 0]    HCLK,
    input   logic   [0 : 0]    HRESETn
);

    logic   [31 : 0]    HADDR;
    logic   [2  : 0]    HBURST;
    logic   [0  : 0]    HMASTLOCK;
    logic   [3  : 0]    HPROT;
    logic   [0  : 0]    HSEL;
    logic   [2  : 0]    HSIZE;
    logic   [1  : 0]    HTRANS;
    logic   [31 : 0]    HWDATA;
    logic   [0  : 0]    HWRITE;
    logic   [0  : 0]    HREADY;
    logic   [31 : 0]    HRDATA;
    logic   [0  : 0]    HREADYOUT;
    logic   [0  : 0]    HRESP;
    
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                       Properties                                      //
    ///////////////////////////////////////////////////////////////////////////////////////////

    property unk_p(cond,test_v);
        @(posedge HCLK)
        disable iff( !HRESETn )
        ( cond ) |-> ( ! $isunknown(test_v) );
    endproperty : unk_p
    
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                  Assertions and covers                                //
    ///////////////////////////////////////////////////////////////////////////////////////////

    haddr_unk_a     : assert property( unk_p( HSEL && HREADY , HADDR )      ) else $warning("haddr_unk_a : FAIL");
    haddr_unk_c     : cover  property( unk_p( HSEL && HREADY , HADDR )      )      ;// $info("haddr_unk_c : PASS");

    hsize_unk_a     : assert property( unk_p( HSEL && HREADY , HSIZE )      ) else $warning("hsize_unk_a : FAIL");
    hsize_unk_c     : cover  property( unk_p( HSEL && HREADY , HSIZE )      )      ;// $info("hsize_unk_c : PASS");
    
    hburst_unk_a    : assert property( unk_p( HSEL && HREADY , HBURST )     ) else $warning("hburst_unk_a : FAIL");
    hburst_unk_c    : cover  property( unk_p( HSEL && HREADY , HBURST )     )      ;// $info("hburst_unk_c : PASS");

    hmastlock_unk_a : assert property( unk_p( HSEL && HREADY , HMASTLOCK )  ) else $warning("hmastlock_unk_a : FAIL");
    hmastlock_unk_c : cover  property( unk_p( HSEL && HREADY , HMASTLOCK )  )      ;// $info("hmastlock_unk_c : PASS");

    hprot_unk_a     : assert property( unk_p( HSEL && HREADY , HPROT )      ) else $warning("hprot_unk_a : FAIL");
    hprot_unk_c     : cover  property( unk_p( HSEL && HREADY , HPROT )      )      ;// $info("hprot_unk_c : PASS");

    htrans_unk_a    : assert property( unk_p( HSEL && HREADY , HTRANS )     ) else $warning("htrans_unk_a : FAIL");
    htrans_unk_c    : cover  property( unk_p( HSEL && HREADY , HTRANS )     )      ;// $info("htrans_unk_c : PASS");

    hresp_unk_a     : assert property( unk_p( HREADYOUT      , HRESP )      ) else $warning("hresp_unk_a : FAIL");
    hresp_unk_c     : cover  property( unk_p( HREADYOUT      , HRESP )      )      ;// $info("hresp_unk_c : PASS");

endinterface : ahb_lite_if
