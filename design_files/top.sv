//===================================================================== 
/// Description: 
// this is the top file of our dut, this module should never be changed
// Designer : sjl_519021910940@sjtu.edu.cn
// ==================================================================== 
/* don't change the signal */

module dut_top(
    //input bus
    icb_bus.slave icb_bus,

    //ouput bus
    apb_bus.master apb_bus_0,
    apb_bus.master apb_bus_1,
    apb_bus.master apb_bus_2,
    apb_bus.master apb_bus_3

);

/* put your code here */ 
//changed by Huang Chaofan, extraordinary.h@sjtu.edu.cn, 11.05

//for example
logic wfifo_full;
logic wfifo_empty;
logic wfifo_wen;
logic wfifo_ren;
logic [63:0]wfifo_wdata;
logic [31:0]wfifo_rdata;

logic rfifo_full;
logic rfifo_empty;
logic rfifo_wen;
logic rfifo_ren;
logic [63:0]rfifo_wdata;
logic [63:0]rfifo_rdata;

logic [63:0] control;
logic [63:0] wdata;
logic [63:0] key;

logic [1:0] apb_state;
logic [31:0] rdata;


//icb_slave module
icb_slave u_icb_slave(
    .icb_bus     (icb_bus     ),
    .wfifo_full  (wfifo_full  ),
    .rfifo_empty (rfifo_empty ),
    .apb_state   (apb_state   ),
    .rfifo_rdata (rfifo_rdata ),
    .wfifo_wen   (wfifo_wen   ),
    .rfifo_ren   (rfifo_ren   ),
    .control     (control     ),
    .wdata       (wdata       ),
    .key         (key         )
);

//apb_master module
apb_master u_apb_master(
    .control     (control     ),
    .wfifo_empty (wfifo_empty ),
    .rfifo_full  (rfifo_full  ),
    .wfifo_rdata (wfifo_rdata ),
    .wfifo_ren   (wfifo_ren   ),
    .rfifo_wen   (rfifo_wen   ),
    .apb_state   (apb_state   ),
    .rdata       (rdata       ),
    .apb_bus_0   (apb_bus_0   ),
    .apb_bus_1   (apb_bus_1   ),
    .apb_bus_2   (apb_bus_2   ),
    .apb_bus_3   (apb_bus_3   )
);


//decrypt module
codec decrypt(
    .data_i (wdata       ),
    .key    (key         ),
    .data_o (wfifo_wdata )
);

//encrypt module
codec encrypt(
    .data_i ({32'b0, rdata} ),
    .key    (key            ),
    .data_o (rfifo_wdata    )
);

//wfifo module
fifo 
#(
    .BUF_SIZE   (16     ),
    .ADDR_SIZE  (4      ),
    .DATA_WIDTH (32     )
)
wfifo(
    .wclk   (icb_bus.clk      ),
    .wrst_n (icb_bus.rst_n    ),
    .wen    (wfifo_wen        ),
    .data_w (wfifo_wdata[31:0]),
    .full   (wfifo_full       ),
    .rclk   (apb_bus_0.clk    ),
    .rrst_n (apb_bus_0.rst_n  ),
    .ren    (wfifo_ren        ),
    .data_r (wfifo_rdata      ),
    .empty  (wfifo_empty      )
);

//rfifo module
fifo 
#(
    .BUF_SIZE   (16         ),
    .ADDR_SIZE  (4          ),
    .DATA_WIDTH (64         )
)
rfifo(
    .wclk   (apb_bus_0.clk   ),
    .wrst_n (apb_bus_0.rst_n ),
    .wen    (rfifo_wen       ),
    .data_w (rfifo_wdata     ),
    .full   (rfifo_full      ),
    .rclk   (icb_bus.clk     ),
    .rrst_n (icb_bus.rst_n   ),
    .ren    (rfifo_ren       ),
    .data_r (rfifo_rdata     ),
    .empty  (rfifo_empty     )
);

endmodule