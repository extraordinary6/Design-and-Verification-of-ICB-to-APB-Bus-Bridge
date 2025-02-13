`timescale 1ns/1ns
`include "uvm_pkg.sv"
//`include "C:/questasim64_10.4c/verilog_src/uvm-1.2/src/uvm_pkg.sv"  //also ok by jiang

`include "../rtl/apb_bus.sv"
`include "../rtl/apb_master.sv"
`include "../rtl/cfig.svh"
`include "../rtl/codec_des.sv"
`include "../rtl/codec.sv"
`include "../rtl/dut.sv"
`include "../rtl/fifo.sv"
`include "../rtl/icb_bus.sv"
`include "../rtl/icb_slave.sv"
`include "../rtl/top.sv"

`include "icb_assertion.sv"
`include "apb_assertion.sv"
`include "xor_assertion.sv"
`include "des_assertion.sv"
`include "fifo_assertion.sv"

`include "my_sequence_pkg.sv"
`include "my_agent_pkg.sv"
`include "my_env_pkg.sv"
`include "my_test_pkg.sv"

module my_top;
    import uvm_pkg::*;
    import my_sequence_pkg::*;
    import my_agent_pkg::*;
    import my_env_pkg::*;
    import my_test_pkg::*;
    parameter NUM_ENV = 3;
    parameter ICB_PERIOD = 10;       // ICB Clock Period
    parameter APB_PERIOD = 10;       // APB Clock Period
    genvar i;

    generate
        for(i = 0; i < NUM_ENV; i++) begin
            logic icb_clk;
            initial begin
                icb_clk = 0;
                forever #(ICB_PERIOD/2) icb_clk = ~icb_clk;
            end

            logic apb_clk;
            initial begin
                apb_clk = 0;
                forever #(APB_PERIOD/2) apb_clk = ~apb_clk;
            end

            logic rst_n;
            initial begin
                rst_n = 0;
                repeat(10) @(negedge icb_clk);
                rst_n = 1;
            end

            icb_bus icb(icb_clk, rst_n);
            apb_bus apb0(apb_clk, rst_n);
            apb_bus apb1(apb_clk, rst_n);
            apb_bus apb2(apb_clk, rst_n);
            apb_bus apb3(apb_clk, rst_n);

            initial begin
                icb.icb_cmd_valid = 0;

                icb.icb_cmd_read = 0;

                icb.icb_rsp_valid = 0;

            end

            dut #(.ID(i)) 
            i_dut
            (
                // input bus
                .icb(           icb             ),

                // output bus
                .apb0(          apb0            ),
                .apb1(          apb1            ),
                .apb2(          apb2            ),
                .apb3(          apb3            )
            );

            // // assertion bind
            // `ifdef CHECK
            //     bind genblk1[i].i_dut.i_dut_top icb_assertion 
            //     icb_assertion_bind_dut_top (
            //         .icb(           genblk1[i].i_dut.icb.others      )
            //     );

            //     bind genblk1[i].i_dut.i_dut_top apb_assertion #(.ID(0))
            //     apb_assertion_bind_dut_top0 (
            //         .apb(           genblk1[i].i_dut.apb0.others      )
            //     );

            //     bind genblk1[i].i_dut.i_dut_top apb_assertion #(.ID(1))
            //     apb_assertion_bind_dut_top1 (
            //         .apb(           genblk1[i].i_dut.apb1.others      )
            //     );

            //     bind genblk1[i].i_dut.i_dut_top apb_assertion #(.ID(2))
            //     apb_assertion_bind_dut_top2 (
            //         .apb(           genblk1[i].i_dut.apb2.others      )
            //     );

            //     bind genblk1[i].i_dut.i_dut_top apb_assertion #(.ID(3))
            //     apb_assertion_bind_dut_top3 (
            //         .apb(           genblk1[i].i_dut.apb3.others      )
            //     );
            // `endif

            initial begin
                uvm_config_db #(virtual icb_bus)::set(null, "uvm_test_top", $sformatf("icb_vif%1d", i), icb);

                
                uvm_config_db #(virtual apb_bus)::set(null, "uvm_test_top", $sformatf("apb_vif%1d 0", i), apb0);
                uvm_config_db #(virtual apb_bus)::set(null, "uvm_test_top", $sformatf("apb_vif%1d 1", i), apb1);
                uvm_config_db #(virtual apb_bus)::set(null, "uvm_test_top", $sformatf("apb_vif%1d 2", i), apb2);
                uvm_config_db #(virtual apb_bus)::set(null, "uvm_test_top", $sformatf("apb_vif%1d 3", i), apb3);
            end
        end

    endgenerate
    
    initial begin
        run_test();
    end
endmodule : my_top