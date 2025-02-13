//=====================================================================
// Description:
// This file build the environment for the whole test environment
// Designer : lynnxie@sjtu.edu.cn
// Revision History
// V0 date:2024/11/11 Initial version, lynnxie@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

// ATTENTION: mailbox only records handler, therefore, scoreboard and read/write should be parallel, 
//            or some address/data will be miss, especially for continuous read.

package env;
    
    import icb_agent_pkg::*;
    import apb_agent_pkg::*;
    import scoreboard_pkg::*;
    import objects_pkg::*;

    class env_ctrl;

        // FUNC : grab data
        //=============================================================
        // the new function is to build the class object's subordinates

        // first declare subordinates
        // add the apb agents
        icb_agent       icb_agent;
        // ...
        apb_agent       apb_agent0;
        apb_agent       apb_agent1;
        apb_agent       apb_agent2;
        apb_agent       apb_agent3;
        scoreboard      scoreboard;


        mailbox #(icb_trans) icb2sb;
        mailbox #(apb_trans) apb2sb0;
        mailbox #(apb_trans) apb2sb1;
        mailbox #(apb_trans) apb2sb2;
        mailbox #(apb_trans) apb2sb3;

        

        // new them
        function new();         

            this.icb2sb = new(32);
            this.apb2sb0 = new(32);
            this.apb2sb1 = new(32);
            this.apb2sb2 = new(32);
            this.apb2sb3 = new(32);

            this.icb_agent = new(this.icb2sb);
            // remember to new the apb agents
            // ...
            this.apb_agent0 = new(this.apb2sb0);
            this.apb_agent1 = new(this.apb2sb1);
            this.apb_agent2 = new(this.apb2sb2);
            this.apb_agent3 = new(this.apb2sb3);
            
            this.scoreboard = new(this.icb2sb,
                                  this.apb2sb0,
                                  this.apb2sb1,
                                  this.apb2sb2,
                                  this.apb2sb3);

        endfunction //new()

        // CONNECT
        //=============================================================
        // the set_interface function is to connect the interface to itself
        // and then also connect to its subordinates
        // (only if used)
        function void set_intf(
            virtual icb_bus     icb,
            // remember to set the apb intf
            // ...
            virtual apb_bus     apb0,
            virtual apb_bus     apb1,
            virtual apb_bus     apb2,
            virtual apb_bus     apb3
        );
            // connect to agent
            this.icb_agent.set_intf(icb);
            // ...
            this.apb_agent0.set_intf(apb0);
            this.apb_agent1.set_intf(apb1);
            this.apb_agent2.set_intf(apb2);
            this.apb_agent3.set_intf(apb3);
        endfunction



        // RUN
        //=============================================================
        // manage your work here : 
        // (1) receive the command from the testbench
        // (2) call its subordinates to work
        task run(string state);
            localparam  CTRL_ADDR = 32'h2000_0000;
            localparam  STAT_ADDR = 32'h2000_0008;
            localparam  WDATA_ADDR = 32'h2000_0010;
            localparam  RDATA_ADDR = 32'h2000_0018;
            localparam  KEY_ADDR = 32'h2000_0020;

            case (state)
                "ICB Write": begin // test: ICB -> Bus Bridge -> APB
                    $display("=============================================================");
                    $display("[TB- ENV ] Start work : ICB Write !");

                    $display("[TB- ENV ] Write KEY register.");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_ffff_ffff, KEY_ADDR);

                    $display("[TB- ENV ] Write CTRL register.");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_0000_0001, CTRL_ADDR);

                    $display("[TB- ENV ] Write WDATA register x16 (every twice for ctrl packet and data packet).");
                    fork
                        this.icb_agent.seq_tran(1'b0, 8'h00, 1'b0, 16);
                                            //read, mask, cmd_read, num
                        this.apb_agent0.seq_tran(8); //standby
                        this.apb_agent1.seq_tran(8); //standby
                        this.apb_agent2.seq_tran(8); //standby
                        this.apb_agent3.seq_tran(8); //standby
                    join_any
                    
                    #1000;
                    disable fork;
                end
                "ICB Read": begin // test: APB -> Bus Bridge -> ICB
                    $display("=============================================================");
                    $display("[TB- ENV ] Start work : ICB Read !");

                    //prepare stage
                    // this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_ffff_ffff, KEY_ADDR);
                    // this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_0000_0001, CTRL_ADDR);

                    $display("[TB- ENV ] Read CTRL register.");
                    this.icb_agent.single_tran(1'b1, 8'h00, 64'h0000_0000_0000_0000, CTRL_ADDR);

                    $display("[TB- ENV ] Read STATE register.");
                    this.icb_agent.single_tran(1'b1, 8'h00, 64'h0000_0000_0000_0000, STAT_ADDR);

                    $display("[TB- ENV ] Read WDATA register.");
                    this.icb_agent.single_tran(1'b1, 8'h00, 64'h0000_0000_0000_0000, WDATA_ADDR);

                    $display("[TB- ENV ] Read KEY register.");
                    this.icb_agent.single_tran(1'b1, 8'h00, 64'h0000_0000_0000_0000, KEY_ADDR);

                    $display("[TB- ENV ] Read RDATA register x8.");
                    fork
                        this.icb_agent.seq_tran(1'b0, 8'h00, 1'b1, 16);
                                            //read, mask, cmd_read, num
                        this.apb_agent0.seq_tran(8); //standby
                        this.apb_agent1.seq_tran(8); //standby
                        this.apb_agent2.seq_tran(8); //standby
                        this.apb_agent3.seq_tran(8); //standby
                    join_any

                    this.icb_agent.seq_tran(1'b1, 8'h00, 1'b0, 8);

                    disable fork;
                    #1000;
                end
                "WFIFO test": begin
                    $display("=============================================================");
                    $display("[TB- ENV ] Start work : WFIFO test !");

                    $display("[TB- ENV ] Write KEY register.");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_ffff_ffff, KEY_ADDR);

                    $display("[TB- ENV ] Write WDATA register for fifo depth.");
                    for (int i = 0; i < 16; i = i + 1) begin
                        this.icb_agent.single_tran(1'b0, 8'h00, i, WDATA_ADDR);
                    end

                    #100;

                    $display("[TB- ENV ] Write CTRL register.");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_0000_0001, CTRL_ADDR);
                    #1000;
                end
                "APB Master test": //test the cross clock domain issue: the mismatch of bus speed
                begin
                    $display("=============================================================");
                    $display("[TB- ENV ] Start work : APB Master test !");

                    $display("[TB- ENV ] Write KEY register.");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_ffff_ffff, KEY_ADDR);
                    

                    $display("[TB- ENV ] Write CTRL register.");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_0000_0001, CTRL_ADDR);

                    $display("[TB- ENV ] Write WDATA register for control packet1");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_ffff_fef9, WDATA_ADDR);

                    #100;

                    $display("[TB- ENV ] Write WDATA register for data packet1");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_ffff_ffee, WDATA_ADDR);

                    #200;

                    this.apb_agent0.single_tran(32'h0000_1234);

                    #100;

                    $display("[TB- ENV ] Write WDATA register for control packet2");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_ffff_fdf5, WDATA_ADDR);

                    #100;

                    $display("[TB- ENV ] Write WDATA register for data packet2");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000_0000_ffff_fff0, WDATA_ADDR);

                    #200;

                    this.apb_agent1.single_tran(32'h0000_4321);

                    #1000;

                end
                "DES test": //test the DES and the transport, only can be tested when "`define DES" in cfig.svh
                begin
                    $display("=============================================================");
                    $display("[TB- ENV ] Start work : APB Master test !");

                    $display("[TB- ENV ] Write KEY register.");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h133457799bbcdff1, KEY_ADDR); // des key
                    

                    $display("[TB- ENV ] Write CTRL register.");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h0000000000000001, CTRL_ADDR);

                    $display("[TB- ENV ] Write WDATA register for control packet1");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h5445EC6F0A919646, WDATA_ADDR);

                    #400;

                    $display("[TB- ENV ] Write WDATA register for data packet1");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'hA7C678BF3C3011CF, WDATA_ADDR);

                    this.apb_agent0.single_tran(32'h0000_1234);

                    #400;

                    $display("[TB- ENV ] Write WDATA register for control packet2");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'h2DD5E9BEEAB99163, WDATA_ADDR);

                    #400;

                    $display("[TB- ENV ] Write WDATA register for data packet2");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'hC11B90D1268ED889, WDATA_ADDR);

                    this.apb_agent1.single_tran(32'h0000_4321);

                    #400;

                    $display("[TB- ENV ] Write WDATA register for control packet3");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'hC9FBC100381280B1, WDATA_ADDR);

                    #400;

                    $display("[TB- ENV ] Write WDATA register for data packet3(meaningless)");
                    this.icb_agent.single_tran(1'b0, 8'h00, 64'hA7C678BF3C3011CF, WDATA_ADDR);

                    this.apb_agent0.single_tran(32'h0000_4444);


                    #1000;
                end
                "Time_Run": begin
                    $display("[TB- ENV ] start work : Time_Run !");
                    # 100000;
                    $display("[TB- ENV ] =========================================================================================");
                    $display("[TB- ENV ]  _|_|_|_|_|   _|_|_|   _|      _|   _|_|_|_|         _|_|     _|    _|   _|_|_|_|_|  ");
                    $display("[TB- ENV ]      _|         _|     _|_|  _|_|   _|             _|    _|   _|    _|       _|      ");
                    $display("[TB- ENV ]      _|         _|     _|  _|  _|   _|_|_|         _|    _|   _|    _|       _|      ");
                    $display("[TB- ENV ]      _|         _|     _|      _|   _|             _|    _|   _|    _|       _|      ");
                    $display("[TB- ENV ]      _|       _|_|_|   _|      _|   _|_|_|_|         _|_|       _|_|         _|      ");
                    $display("[TB- ENV ] =========================================================================================");
                end
                default: begin
                    $display("Wrong instruction!");
                end
            endcase
        endtask
    endclass //env_ctrl
endpackage