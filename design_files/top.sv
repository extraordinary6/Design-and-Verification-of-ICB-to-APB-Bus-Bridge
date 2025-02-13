//===================================================================== 
/// Description: 
// this is the top file of our dut, this module should never be changed
// Designer : sjl_519021910940@sjtu.edu.cn
// ==================================================================== 
/* don't change the signal */
`timescale 1ns/1ps
`include "cfig.svh"

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
logic [4:0] w_wptr;       // wfifo write pointer
logic [4:0] w_wptr_g;     // wfifo write pointer (gray)
logic [4:0] w_wptr_gd2;   // wfifo write pointer (gray, delay 2 cycles)
logic [4:0] w_rptr;
logic [4:0] w_rptr_g;
logic [4:0] w_rptr_gd2;

logic rfifo_full;
logic rfifo_empty;
logic rfifo_wen;
logic rfifo_ren;
logic [63:0]rfifo_wdata;
logic [63:0]rfifo_rdata;
logic [4:0] r_wptr;
logic [4:0] r_wptr_g;
logic [4:0] r_wptr_gd2;
logic [4:0] r_rptr;
logic [4:0] r_rptr_g;
logic [4:0] r_rptr_gd2;

logic [63:0] control;
logic [63:0] wdata;
logic [63:0] key;
logic        wdata_vld;

logic [1:0]  apb_state;
logic [31:0] rdata;
logic        rdata_vld;

logic decrypt_vldo;
logic encrypt_vldo;

// The input for bind cannot be an expression
// logic [31:0] wfifo_datai;
// logic [63:0] encrypt_datai;

// assign wfifo_datai = wfifo_wdata[31:0];
// assign encrypt_datai = {32'b0, rdata};


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
    .key         (key         ),
    .wdata_vld   (wdata_vld   )
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
    .rdata_vld   (rdata_vld   ),
    .apb_bus_0   (apb_bus_0   ),
    .apb_bus_1   (apb_bus_1   ),
    .apb_bus_2   (apb_bus_2   ),
    .apb_bus_3   (apb_bus_3   )
);



`ifdef DES
    //decrypt module
    codec_des 
    #(
        .ENCRYPT (0)
    )
    u_decrypt(
        .clk     (icb_bus.clk  ),
        .rst_n   (icb_bus.rst_n),
        .data_i  (wdata        ),
        .valid_i (wdata_vld    ),
        .key     (key          ),
        .data_o  (wfifo_wdata  ),
        .valid_o (decrypt_vldo )
    );

    //encrypt module
    codec_des 
    #(
        .ENCRYPT (1)
    )
    u_encrypt(
        .clk     (apb_bus_0.clk  ),
        .rst_n   (apb_bus_0.rst_n),
        .data_i  ({32'b0, rdata} ),
        .valid_i (rdata_vld      ),
        .key     (key            ),
        .data_o  (rfifo_wdata    ),
        .valid_o (encrypt_vldo   ) 
    );

`else
    //decrypt module
    codec decrypt(
        `ifdef CHECK
        .clk    (icb_bus.clk  ),
        .rst_n  (icb_bus.rst_n),
        `endif 
        .data_i (wdata        ),
        .key    (key          ),
        .data_o (wfifo_wdata  )
    );

    //encrypt module
    codec encrypt(
        `ifdef CHECK
        .clk    (apb_bus_0.clk  ),
        .rst_n  (apb_bus_0.rst_n),
        `endif 
        .data_i ({32'b0, rdata} ),
        .key    (key            ),
        .data_o (rfifo_wdata    )
    );
`endif

//wfifo module
fifo 
#(
    .BUF_SIZE   (16     ),
    .ADDR_SIZE  (4      ),
    .DATA_WIDTH (32     )
)
wfifo(
    .wclk       (icb_bus.clk      ),
    .wrst_n     (icb_bus.rst_n    ),
    .wen        (wfifo_wen        ),
    .data_w     (wfifo_wdata[31:0]),
    .full       (wfifo_full       ),
    .wr_ptr     (w_wptr           ),
    .wr_ptr_g   (w_wptr_g         ),
    .wr_ptr_gd2 (w_wptr_gd2       ),
    .rclk       (apb_bus_0.clk    ),
    .rrst_n     (apb_bus_0.rst_n  ),
    .ren        (wfifo_ren        ),
    .data_r     (wfifo_rdata      ),
    .empty      (wfifo_empty      ),
    .rd_ptr     (w_rptr           ),
    .rd_ptr_g   (w_rptr_g         ),
    .rd_ptr_gd2 (w_rptr_gd2       )
);

//rfifo module
fifo 
#(
    .BUF_SIZE   (16         ),
    .ADDR_SIZE  (4          ),
    .DATA_WIDTH (64         )
)
rfifo(
    .wclk       (apb_bus_0.clk   ),
    .wrst_n     (apb_bus_0.rst_n ),
    .wen        (rfifo_wen       ),
    .data_w     (rfifo_wdata     ),
    .full       (rfifo_full      ),
    .wr_ptr     (r_wptr          ),
    .wr_ptr_g   (r_wptr_g        ),
    .wr_ptr_gd2 (r_wptr_gd2      ),
    .rclk       (icb_bus.clk     ),
    .rrst_n     (icb_bus.rst_n   ),
    .ren        (rfifo_ren       ),
    .data_r     (rfifo_rdata     ),
    .empty      (rfifo_empty     ),
    .rd_ptr     (r_rptr          ),
    .rd_ptr_g   (r_rptr_g        ),
    .rd_ptr_gd2 (r_rptr_gd2      )
);

/*  Assertion Bind */

`ifdef CHECK
    // WFIFO Assertion
    bind fifo:wfifo fifo_assertion #(
        .ID         (0          ),
        .BUF_SIZE   (16         ),
        .ADDR_SIZE  (4          ),
        .DATA_WIDTH (32         )
    )
    fifo_assertion_bind_wfifo (
        .wclk       (wclk       ),
        .wrst_n     (wrst_n     ),
        .wen        (wen        ),
        .data_w     (data_w     ),
        .full       (full       ),
        .wr_ptr     (wr_ptr     ),
        .wr_ptr_g   (wr_ptr_g   ),
        .wr_ptr_gd2 (wr_ptr_gd2 ),
        .rclk       (rclk       ),
        .rrst_n     (rrst_n     ),
        .ren        (ren        ),
        .data_r     (data_r     ),
        .empty      (empty      ),
        .rd_ptr     (rd_ptr     ),
        .rd_ptr_g   (rd_ptr_g   ),
        .rd_ptr_gd2 (rd_ptr_gd2 )
    );


    // RFIFO Assertion
    bind fifo:rfifo fifo_assertion #(
        .ID         (1          ),
        .BUF_SIZE   (16         ),
        .ADDR_SIZE  (4          ),
        .DATA_WIDTH (64         )
    )
    fifo_assertion_bind_rfifo (
        .wclk       (wclk       ),
        .wrst_n     (wrst_n     ),
        .wen        (wen        ),
        .data_w     (data_w     ),
        .full       (full       ),
        .wr_ptr     (wr_ptr     ),
        .wr_ptr_g   (wr_ptr_g   ),
        .wr_ptr_gd2 (wr_ptr_gd2 ),
        .rclk       (rclk       ),
        .rrst_n     (rrst_n     ),
        .ren        (ren        ),
        .data_r     (data_r     ),
        .empty      (empty      ),
        .rd_ptr     (rd_ptr     ),
        .rd_ptr_g   (rd_ptr_g   ),
        .rd_ptr_gd2 (rd_ptr_gd2 )
    );

    `ifdef DES

        // Decrypt Assertion
        bind codec_des:u_decrypt des_assertion #(
            .ID(0)
        )
        des_assertion_bind_decrypt (
            .clk     (clk     ),
            .rst_n   (rst_n   ),
            .data_i  (data_i  ),
            .valid_i (valid_i ),
            .key     (key     ),
            .data_o  (data_o  ),
            .valid_o (valid_o )
        );

        // Encrypt Assertion
        bind codec_des:u_encrypt des_assertion #(
            .ID(1)
        )
        des_assertion_bind_encrypt (
            .clk     (clk     ),
            .rst_n   (rst_n   ),
            .data_i  (data_i  ),
            .valid_i (valid_i ),
            .key     (key     ),
            .data_o  (data_o  ),
            .valid_o (valid_o )
        );

    `else
        
        // Decrypt Assertion
        bind codec:decrypt xor_assertion #(
            .ID(0)
        )
        xor_assertion_bind_decrypt (
            .clk    (clk          ),
            .rst_n  (rst_n        ),
            .data_i (data_i       ),
            .key    (key          ),
            .data_o (data_o       )
        );

        // Encrypt Assertion
        bind codec:encrypt xor_assertion #(
            .ID(1)
        )
        xor_assertion_bind_encrypt (
            .clk    (clk          ),
            .rst_n  (rst_n        ),
            .data_i (data_i       ),
            .key    (key          ),
            .data_o (data_o       )
        );
    `endif
`endif

endmodule