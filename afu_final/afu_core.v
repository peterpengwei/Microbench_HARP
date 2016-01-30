// Copyright (c) 2013-2015, Intel Corporation
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// * Redistributions of source code must retain the above copyright notice,
// this list of conditions and the following disclaimer.
// * Redistributions in binary form must reproduce the above copyright notice,
// this list of conditions and the following disclaimer in the documentation
// and/or other materials provided with the distribution.
// * Neither the name of Intel Corporation nor the names of its contributors
// may be used to endorse or promote products derived from this software
// without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.


`include "spl_defines.vh"


module afu_core (
    input  wire                             clk,
    input  wire                             reset_n,
    
    input  wire                             spl_enable,
    input  wire                             spl_reset,
    
    // TX_RD request, afu_core --> afu_io
    input  wire                             spl_tx_rd_almostfull,
    output reg                              cor_tx_rd_valid,
    output reg  [57:0]                      cor_tx_rd_addr,
    output reg  [5:0]                       cor_tx_rd_len,  // in CL, 0-64, 1-1, 2-2, ...63-63
    
    
    // TX_WR request, afu_core --> afu_io
    input  wire                             spl_tx_wr_almostfull,    
    output reg                              cor_tx_wr_valid,
    output reg                              cor_tx_dsr_valid,
    output reg                              cor_tx_fence_valid,
    output reg                              cor_tx_done_valid,
    output reg  [57:0]                      cor_tx_wr_addr, 
    output reg  [5:0]                       cor_tx_wr_len, 
    output reg  [511:0]                     cor_tx_data,
             
    // RX_RD response, afu_io --> afu_core
    input  wire                             io_rx_rd_valid,
    input  wire [511:0]                     io_rx_data,    

    // for the last write
    output reg		    		    write_last_sent,
    input wire		    		    write_last_done,
                 
    // afu_csr --> afu_core, afu_id
    input  wire                             csr_id_valid,
    output reg                              csr_id_done,    
    input  wire [31:0]                      csr_id_addr,
//    input  wire [63:0]                      csr_id,
    
    // afu_csr --> afu_core, afu_scratch
    input  wire                             csr_scratch_valid,
    output wire                             csr_scratch_done,    
    input  wire [31:0]                      csr_scratch_addr,
    input  wire [63:0]                      csr_scratch,
        
     // afu_csr --> afu_core, afu_ctx   
    input  wire                             csr_ctx_base_valid,
    input  wire [57:0]                      csr_ctx_base
);


    localparam [2:0]
        TX_RD_STATE_IDLE       = 3'b000,
        TX_RD_STATE_CTX        = 3'b001,
	TX_RD_STATE_WARMUP_LAT = 3'b010,
        TX_RD_STATE_MISS_LAT   = 3'b011,
	TX_RD_STATE_WARMUP_BW  = 3'b100,
        TX_RD_STATE_MISS_BW    = 3'b101,
        TX_RD_STATE_CPLT       = 3'b111;
        
    localparam [0:0]
        RX_RD_STATE__IDLE       = 1'b0,
        RX_RD_STATE__RUN        = 1'b1;
        
    localparam [3:0]
        TX_WR_STATE_IDLE       = 4'b0000,
        TX_WR_STATE_CTX        = 4'b0001,
	TX_WR_STATE_WARMUP_BW  = 4'b0110,
	TX_WR_STATE_WAIT_BW    = 4'b0010,
        TX_WR_STATE_STATUS     = 4'b0011,
        TX_WR_STATE_FENCE      = 4'b0100,
        TX_WR_STATE_TASKDONE   = 4'b0101,
        TX_WR_STATE_MISS_BW    = 4'b1000,
	TX_WR_STATE_WARMUP_LAT = 4'b1001,
	TX_WR_STATE_MISS_LAT   = 4'b1010,
	TX_WR_STATE_WAIT_WMLAT = 4'b1011,
	TX_WR_STATE_WAIT_WMBW  = 4'b1100;
                
    localparam [5:0]                
        AFU_CSR__LATENCY_CNT        = 6'b00_0100,
        AFU_CSR__PERFORMANCE_CNT    = 6'b00_0101;
               
    localparam AFU_ID               = 64'hbeefbeef;

    localparam WARMUP_LOOP_NUM      = 32'h100000;

    reg  [2:0]                      tx_rd_state;
    reg  [3:0]                      tx_wr_state;
    reg                             rx_rd_state;
    
    reg                             ctx_valid;
//    reg  [31:0]                     ctx_delay;
//    reg  [15:0]                     ctx_threshold;
    reg  [57:0]                     ctx_src_ptr;
    reg  [57:0]                     ctx_dst_ptr;
    reg  [31:0]                     ctx_length;
    
    reg  [31:0]                     src_cnt;
    
    reg  [31:0]                     dst_cnt;
    
    wire [31:0]                     lat_cnt_addr;
    wire [31:0]                     bw_cnt_addr;

    reg  [63:0]                     dsr_read_miss_lat_cnt;
    reg  [63:0]                     dsr_read_hit_lat_cnt;
    reg  [63:0]                     dsr_write_miss_lat_cnt;
    reg  [63:0]                     dsr_write_hit_lat_cnt;

    reg  [63:0]                     read_resp_cnt;

    reg  [63:0]                     dsr_read_miss_bw_cnt;
    reg  [63:0]                     dsr_read_hit_bw_cnt;
    reg  [63:0]                     dsr_write_miss_bw_cnt;
    reg  [63:0]                     dsr_write_hit_bw_cnt;

    wire                            csr_id_update;
    wire                            csr_scratch_update;
    reg                             csr_scratch_done_tw;
    
    reg  [57:0]                     status_addr;
    reg                             status_addr_valid;
    reg                             status_addr_cr;
        
    //-----------------------------------------------------------
    // TX_WR
    //-----------------------------------------------------------
    assign csr_id_update = csr_id_valid & (~csr_id_done) & (~spl_tx_wr_almostfull);
//    assign csr_scratch_update = csr_scratch_valid & (~csr_scratch_done) & (~spl_tx_wr_almostfull);
    assign csr_scratch_update = csr_scratch_valid & (~csr_scratch_done) & (~spl_tx_wr_almostfull);   // disable DSR insertion
    assign lat_cnt_addr = csr_id_addr + AFU_CSR__LATENCY_CNT;
    assign bw_cnt_addr = csr_id_addr + AFU_CSR__PERFORMANCE_CNT;
    assign csr_scratch_done = csr_scratch_done_tw;
    
           
    always @(posedge clk) begin
        if ((~reset_n) | spl_reset) begin
            cor_tx_wr_valid <= 1'b0;
            cor_tx_dsr_valid <= 1'b0;
            cor_tx_fence_valid <= 1'b0;
            cor_tx_done_valid <= 1'b0;
            csr_id_done <= 1'b0;
            csr_scratch_done_tw <= 1'b0;
            tx_wr_state <= TX_WR_STATE_IDLE;

	    dsr_write_miss_lat_cnt <= 'b0;
	    dsr_write_hit_lat_cnt <= 'hdeedbeef;
	    dsr_write_miss_bw_cnt <= 'b0;
	    dsr_write_hit_bw_cnt <= 'hdeedbeef;

	    write_last_sent <= 'b0;
        end
        
        else begin
            cor_tx_wr_valid <= 1'b0;
            cor_tx_dsr_valid <= 1'b0;
            cor_tx_fence_valid <= 1'b0;
            csr_id_done <= 1'b0;
            csr_scratch_done_tw <= 1'b0;       

	    write_last_sent <= 'b0;

            case (tx_wr_state)
                TX_WR_STATE_IDLE : begin
                    if (csr_id_update) begin
                        cor_tx_wr_valid <= 1'b1;
                        cor_tx_dsr_valid <= 1'b1;
                        cor_tx_wr_len <= 6'h1;
                        cor_tx_wr_addr <= {26'b0, csr_id_addr};
                        cor_tx_data <= {448'b0, AFU_ID};
                        csr_id_done <= 1'b1;                    
                        tx_wr_state <= TX_WR_STATE_CTX;
                    end
                end
                
                TX_WR_STATE_CTX : begin
                    casex ({csr_scratch_update, ctx_valid})
                        2'b1? : begin
                            cor_tx_wr_valid <= 1'b1;
                            cor_tx_dsr_valid <= 1'b1;
                            cor_tx_wr_len <= 6'h1;
                            cor_tx_wr_addr <= {26'b0, csr_scratch_addr};
                            cor_tx_data <= {448'b0, csr_scratch};
                            csr_scratch_done_tw <= 1'b1;                    
                        end
                    
                        2'b01 : begin                                                            
			    if (~spl_tx_wr_almostfull & tx_rd_state == TX_RD_STATE_CPLT) begin
                                tx_wr_state <= TX_WR_STATE_WARMUP_LAT;
			        dst_cnt <= WARMUP_LOOP_NUM - 'b1;

                                cor_tx_wr_valid <= 1'b1; 
                                cor_tx_wr_len <= 'b1;
                                cor_tx_wr_addr <= ctx_dst_ptr;
                                cor_tx_data <= {64{8'hAF}};
			    end
                        end
                    endcase                                        
                end //  TX_WR_STATE_CTX                                  

		TX_WR_STATE_WARMUP_LAT : begin
                    // prepare next
                    if ((dst_cnt > 32'b1) & ~spl_tx_wr_almostfull) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= cor_tx_wr_addr + 'b1;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= dst_cnt - 'b1;                        
                    end                         

		    // to the next state
		    if ((dst_cnt == 32'b1) & ~spl_tx_wr_almostfull) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= cor_tx_wr_addr + 'b1;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= dst_cnt - 'b1;                        
                        tx_wr_state <= TX_WR_STATE_WAIT_WMLAT;   
			write_last_sent <= 'b1;
		    end
                end    
                                
                TX_WR_STATE_WAIT_WMLAT : begin
		    // to the next state
		    if (write_last_done) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= ctx_dst_ptr;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= ctx_length - 'b1;
			write_last_sent <= 'b1;

			tx_wr_state <= TX_WR_STATE_MISS_LAT;
			// dsr_write_miss_bw_cnt <= 'b0;
		    end
                end    
                                
                TX_WR_STATE_MISS_LAT : begin
		    dsr_write_miss_lat_cnt <= dsr_write_miss_lat_cnt + 'b1;
                                            
                    // prepare next
                    if ((dst_cnt > 32'b0) & write_last_done) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= cor_tx_wr_addr + 'b1;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= dst_cnt - 'b1;                        
			write_last_sent <= 'b1;
                    end                         

		    // to the next state
                    if ((dst_cnt == 32'b0) & write_last_done) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= ctx_dst_ptr;
                        cor_tx_data <= {64{8'hAF}};
			dst_cnt <= WARMUP_LOOP_NUM - 'b1;
                        tx_wr_state <= TX_WR_STATE_WARMUP_BW;   
		    end
                end    

		TX_WR_STATE_WARMUP_BW : begin
                    // prepare next
		    // greedy requesting
                    if ((dst_cnt > 32'b1) & ~spl_tx_wr_almostfull) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= cor_tx_wr_addr + 'b1;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= dst_cnt - 'b1;                        
                    end                         

		    // to the next state
		    if ((dst_cnt == 32'b1) & ~spl_tx_wr_almostfull) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= cor_tx_wr_addr + 'b1;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= dst_cnt - 'b1;                        
                        tx_wr_state <= TX_WR_STATE_WAIT_WMBW;   
			write_last_sent <= 'b1;
		    end
                end    
                                
                TX_WR_STATE_WAIT_WMBW : begin
		    // to the next state
		    if (write_last_done) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= ctx_dst_ptr;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= ctx_length - 'b1;

			tx_wr_state <= TX_WR_STATE_MISS_BW;
		    end
                end    
                                
                TX_WR_STATE_MISS_BW : begin
		    dsr_write_miss_bw_cnt <= dsr_write_miss_bw_cnt + 'b1;
                                            
                    // prepare next
		    // greedy requesting
                    if ((dst_cnt > 32'b1) & ~spl_tx_wr_almostfull) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= cor_tx_wr_addr + 'b1;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= dst_cnt - 'b1;                        
                    end                         

		    // to the next state
		    if ((dst_cnt == 32'b1) & ~spl_tx_wr_almostfull) begin
                        cor_tx_wr_valid <= 1'b1; 
                        cor_tx_wr_len <= 'b1;
                        cor_tx_wr_addr <= cor_tx_wr_addr + 'b1;
                        cor_tx_data <= {64{8'hAF}};
                        dst_cnt <= dst_cnt - 'b1;                        
                        tx_wr_state <= TX_WR_STATE_WAIT_BW;   
			write_last_sent <= 'b1;
		    end
                end    
                                
                TX_WR_STATE_WAIT_BW : begin
		    dsr_write_miss_bw_cnt <= dsr_write_miss_bw_cnt + 'b1;

		    // to the next state
		    if (write_last_done) begin
			// write complete
                        cor_tx_wr_valid <= 1'b1;
                        cor_tx_dsr_valid <= 1'b1;
                        cor_tx_wr_len <= 6'h1; 
                        cor_tx_wr_addr <= {26'b0, lat_cnt_addr};
                        cor_tx_data <= {256'b0, dsr_write_hit_lat_cnt, dsr_write_miss_lat_cnt, dsr_read_hit_lat_cnt, dsr_read_miss_lat_cnt};
                        tx_wr_state <= TX_WR_STATE_STATUS;   
		    end
                end    

                TX_WR_STATE_STATUS : begin
                    if (~spl_tx_wr_almostfull) begin
                        cor_tx_wr_valid <= 1'b1;
                        cor_tx_dsr_valid <= 1'b1;
                        cor_tx_wr_len <= 6'h1; 
                        cor_tx_wr_addr <= {26'b0, bw_cnt_addr};
                        cor_tx_data <= {256'b0, dsr_write_hit_bw_cnt, dsr_write_miss_bw_cnt, dsr_read_hit_bw_cnt, dsr_read_miss_bw_cnt};
                        tx_wr_state <= TX_WR_STATE_FENCE;  
                    end
                end  
                
                TX_WR_STATE_FENCE : begin
                    if (~spl_tx_wr_almostfull) begin
                        cor_tx_wr_valid <= 1'b1;
                        cor_tx_fence_valid <= 1'b1;
                        tx_wr_state <= TX_WR_STATE_TASKDONE;  
                    end
                end  
                                
                TX_WR_STATE_TASKDONE : begin
                    if ((~spl_tx_wr_almostfull) & (~cor_tx_done_valid)) begin
                        cor_tx_wr_valid <= 1'b1;
                        cor_tx_done_valid <= 1'b1;
                        cor_tx_wr_len <= 6'h1;
                        cor_tx_wr_addr <= status_addr;
                        cor_tx_data <= 'h900dbeef;
                    end
                end  

            endcase                    
        end
    end
    
    //-----------------------------------------------------
    // TX_RD request
    //-----------------------------------------------------    
    
    always @(posedge clk) begin
        if ((~reset_n) | spl_reset) begin
            cor_tx_rd_valid <= 1'b0; 
            status_addr_valid <= 1'b0;
            status_addr_cr <= 1'b0;
            tx_rd_state <= TX_RD_STATE_IDLE;            

            dsr_read_miss_lat_cnt <= 'b0;
            dsr_read_hit_lat_cnt <= 'hdeedbeef;
            dsr_read_miss_bw_cnt <= 'b0;
            dsr_read_hit_bw_cnt <= 'hdeedbeef;
	    read_resp_cnt <= 'hdeadbeef;
        end

        else begin
            cor_tx_rd_valid <= 1'b0;
            
            case (tx_rd_state)
                TX_RD_STATE_IDLE : begin
                    if (csr_ctx_base_valid & spl_enable & (~spl_tx_rd_almostfull)) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_addr <= csr_ctx_base;
                        cor_tx_rd_len <= 6'h1;
                        tx_rd_state <= TX_RD_STATE_CTX;
                                                
                        {status_addr_cr, status_addr[28:0]} <= csr_ctx_base[28:0] + 1'b1;
                    end
                end

                TX_RD_STATE_CTX : begin
                    if (~status_addr_valid) begin
                        status_addr_valid <= 1'b1;
                        status_addr[57:29] <= csr_ctx_base[57:29] + status_addr_cr;
                    end
                    
                    if (ctx_valid & ~spl_tx_rd_almostfull) begin                     
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_len <= 1'b1;
                        cor_tx_rd_addr <= ctx_src_ptr;
                        src_cnt <= WARMUP_LOOP_NUM - 1'b1;                        
                        
                        tx_rd_state <= TX_RD_STATE_WARMUP_LAT;
                    end
                end                    
                                
                TX_RD_STATE_WARMUP_LAT : begin
                    // prepare next
		    // Since only one request at a time, it is inpossible to make SPL full
                    if ((src_cnt > 32'b0) & io_rx_rd_valid) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_len <= 1'b1;
                        cor_tx_rd_addr <= cor_tx_rd_addr + 'b1;
                        src_cnt <= src_cnt - 1'b1;                        
                    end                         

		    // to the next state
		    if (src_cnt == 'b0 & io_rx_rd_valid) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_len <= 1'b1;
                        cor_tx_rd_addr <= ctx_src_ptr;
                        src_cnt <= ctx_length - 1'b1;                        

			tx_rd_state <= TX_RD_STATE_MISS_LAT;
		    end
                end    
                                
                TX_RD_STATE_MISS_LAT : begin
		    dsr_read_miss_lat_cnt <= dsr_read_miss_lat_cnt + 'b1;
                                            
                    // prepare next
		    // Since only one request at a time, it is inpossible to make SPL full
                    if ((src_cnt > 32'b0) & io_rx_rd_valid) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_len <= 1'b1;
                        cor_tx_rd_addr <= cor_tx_rd_addr + 'b1;
                        src_cnt <= src_cnt - 1'b1;                        
                    end                         

		    // to the next state
		    if (src_cnt == 'b0 & io_rx_rd_valid) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_len <= 1'b1;
                        cor_tx_rd_addr <= ctx_src_ptr;
                        src_cnt <= WARMUP_LOOP_NUM - 1'b1;                        

			tx_rd_state <= TX_RD_STATE_WARMUP_BW;
		    end
                end    
                                
                TX_RD_STATE_WARMUP_BW : begin
                    // prepare next
		    // Since only one request at a time, it is inpossible to make SPL full
                    if ((src_cnt > 32'b0) & io_rx_rd_valid) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_len <= 1'b1;
                        cor_tx_rd_addr <= cor_tx_rd_addr + 'b1;
                        src_cnt <= src_cnt - 1'b1;                        
                    end                         

		    // to the next state
		    if (src_cnt == 'b0 & io_rx_rd_valid) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_len <= 1'b1;
                        cor_tx_rd_addr <= ctx_src_ptr;
                        src_cnt <= ctx_length - 1'b1;                        

			tx_rd_state <= TX_RD_STATE_MISS_BW;
			read_resp_cnt <= ctx_length;
		    end
                end    
                                
                TX_RD_STATE_MISS_BW : begin
		    dsr_read_miss_bw_cnt <= dsr_read_miss_bw_cnt + 'b1;

		    // counting responses
		    if (read_resp_cnt > 'b1 & io_rx_rd_valid) begin
			read_resp_cnt <= read_resp_cnt - 'b1;
		    end
                                            
                    // prepare next
		    // greedy requesting
                    if ((src_cnt > 32'b0) & ~spl_tx_rd_almostfull) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_len <= 1'b1;
                        cor_tx_rd_addr <= cor_tx_rd_addr + 'b1;
                        src_cnt <= src_cnt - 1'b1;                        
                    end                         

		    // to the next state
		    if (read_resp_cnt == 'b1 & io_rx_rd_valid) begin
			// read complete
			tx_rd_state <= TX_RD_STATE_CPLT;
		    end
                end    
            endcase                    
        end
    end   
    
                    
    //-------------------------------------------------
    // RX_RD response
    //-------------------------------------------------  
    always @(posedge clk) begin
        if ((~reset_n) | spl_reset)begin
            ctx_valid <= 1'b0;
            rx_rd_state <= RX_RD_STATE__IDLE;
        end

        else begin
            case (rx_rd_state)             
                RX_RD_STATE__IDLE : begin
                    if (io_rx_rd_valid) begin
//                        ctx_delay <= io_rx_data[63:32];
//                        ctx_threshold <= io_rx_data[31:16];
                        ctx_src_ptr <= io_rx_data[127:70];
                        ctx_dst_ptr <= io_rx_data[191:134];
                        ctx_length <= io_rx_data[223:192];    
                        ctx_valid <= 1'b1;
                        rx_rd_state <= RX_RD_STATE__RUN;
                    end
                end

            endcase
        end
    end   

endmodule        

