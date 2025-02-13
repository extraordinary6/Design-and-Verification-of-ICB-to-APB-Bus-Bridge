`timescale 1ns/1ps
//=====================================================================
// Description:
// The Testbench for asynchronous FIFO
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 11.9 Initial version, Huang Chaofan
// ====================================================================

module fifo_tb;
logic           rst_n;

logic           wclk;
logic           wen;
logic [31:0]    data_w;

logic           rclk;
logic           ren;
logic [31:0]    data_r;

logic           full;
logic           empty;

initial begin
  rst_n  <= 1;
  wclk   <= 0;
  wen    <= 0;
  data_w <= 32'b0;
  rclk   <= 0;
  ren    <= 0;

  # 10 rst_n <= 0;
  # 20 rst_n <= 1;
end

initial begin
  #200 wen <= 1;
       ren <= 0;
  #400 wen <= 0;
       ren <= 1;
  #300 wen <= 1;
       ren <= 0;
  #130 ren <= 1;
  #100
  repeat(100)
    begin
        #50 wen <= {$random}%2 ;
        ren <= {$random}%2 ;
    end
end

always #15   wclk  = ~wclk;
always #10   rclk  = ~rclk;
always #30   data_w <= {$random}%33'h100000000;

fifo 
#(
    .BUF_SIZE   (8    ),
    .ADDR_SIZE  (3    ),
    .DATA_WIDTH (32   )
)
u_fifo(
    .wclk   (wclk   ),
    .wrst_n (rst_n ),
    .wen    (wen    ),
    .data_w (data_w ),
    .full   (full   ),
    .rclk   (rclk   ),
    .rrst_n (rst_n ),
    .ren    (ren    ),
    .data_r (data_r ),
    .empty  (empty  )
);


initial begin
  #10000 $finish              ;
  $fsdbDumpfile("async_fifo.fsdb");
  $fsdbDumpvars              ;
  $fsdbDumpMDA               ;
end
endmodule
