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


module afu_io(
    input  wire                             clk,
    input  wire                             reset_n,
    input  wire                             spl_enable,
    input  wire                             spl_reset,
    
    // AFU TX read request
    output reg                              afu_tx_rd_valid,
    output reg [98:0]                       afu_tx_rd_hdr,
    
    // AFU TX write request
    output reg                              afu_tx_wr_valid,
    output reg                              afu_tx_intr_valid,
    output reg [98:0]                       afu_tx_wr_hdr,
    output reg [511:0]                      afu_tx_data,
    
    // AFU RX read response
    input  wire                             spl_rx_rd_valid,
    input  wire                             spl_rx_wr_valid0,
    input  wire                             spl_rx_cfg_valid,
    input  wire                             spl_rx_intr_valid0,
    input  wire                             spl_rx_umsg_valid,
    input  wire [`CCI_RX_HDR_WIDTH-1:0]     spl_rx_hdr0,
    input  wire [511:0]                     spl_rx_data,
    
    // AFU RX write response
    input  wire                             spl_rx_wr_valid1,
    input  wire                             spl_rx_intr_valid1,
    input  wire [`CCI_RX_HDR_WIDTH-1:0]     spl_rx_hdr1,
       
    // RX, afu_io --> afu_csr
    output reg                              io_rx_csr_valid,
    output reg [13:0]                       io_rx_csr_addr,
    output reg [31:0]                       io_rx_csr_data,
    
    // RX_RD response, afu_io --> afu_core
    output  reg                             io_rx_rd_valid,
    output  reg  [511:0]                    io_rx_data,    

    // for the last write
    input  wire		    		    write_last_sent,
    output reg		    		    write_last_done,
        
    // TX_RD request, afu_core --> afu_io
    input  wire                             cor_tx_rd_valid,
    input  wire [57:0]                      cor_tx_rd_addr,
    input  wire [5:0]                       cor_tx_rd_len,
    
    // TX_WR request, afu_core --> afu_io
    input  wire                             cor_tx_wr_valid,
    input  wire                             cor_tx_dsr_valid,
    input  wire                             cor_tx_fence_valid,
    input  wire                             cor_tx_done_valid,        
    input  wire [57:0]                      cor_tx_wr_addr, 
    input  wire [5:0]                       cor_tx_wr_len,
    input  wire [511:0]                     cor_tx_data       
);


    reg  [5:0]                      tx_wr_tag;
    reg  [5:0]                      tx_rd_tag;           
     
    reg                             tx_wr_block;
    reg  [5:0]                      tx_wr_block_cnt;

    // for the last write
    reg  [5:0]			    last_write_tag;
            
    
    //-------------------------------------------------------            
    // TX_WR, drive afu_tx_wr port
    //-------------------------------------------------------
    always @(posedge clk) begin
        if ((~reset_n) | spl_reset) begin
            afu_tx_wr_valid <= 1'b0;
            afu_tx_intr_valid <= 1'b0;
            tx_wr_tag <= 6'b0;
            tx_wr_block <= 1'b0;

	    // for the last write
	    last_write_tag <= 'b0;
        end

        else begin
            afu_tx_wr_valid <= 1'b0;
            afu_tx_intr_valid <= 1'b0;
            
            if (cor_tx_wr_valid) begin
                afu_tx_wr_valid <= 1'b1;

		if (write_last_sent) last_write_tag <= tx_wr_tag;
                
                case ({cor_tx_dsr_valid, cor_tx_fence_valid, cor_tx_done_valid})
                    3'b100 : begin      // DSR
                        //                     98:93   92:67    66      65:61  60:56   55:52
                        afu_tx_wr_hdr <= {6'h0, 26'b0, 1'b0, 5'b0 ,5'b0, `CCI_REQ_WR ,6'b0, cor_tx_wr_addr[31:0], 8'h3, tx_wr_tag};
                        tx_wr_tag <= tx_wr_tag + 1'b1;
                        
                        // synthesis translate_off
                        assert (~tx_wr_block) else $fatal("driving wr_dsr while wr_block in progress");
                        // synthesis translate_on
                    end
                    
                    3'b010 : begin      // fence
                        afu_tx_wr_hdr <= {6'b0, 26'b0, 6'b0 ,5'b0, `CCI_REQ_WR_FENCE ,6'b0, 32'b0, 14'b0};
                        
                        // synthesis translate_off
                        assert (~tx_wr_block) else $fatal("driving wr_fence while wr_block in progress");
                        // synthesis translate_on                        
                    end
                    
                    3'b001 : begin      // done
                        afu_tx_wr_hdr <= {cor_tx_wr_len, cor_tx_wr_addr[57:32], 1'b1, 5'b0 ,5'b0, `CCI_REQ_WR ,6'b0, cor_tx_wr_addr[31:0], 8'h3, tx_wr_tag};
                        tx_wr_tag <= tx_wr_tag + 1'b1;
                        
                        // synthesis translate_off
                        assert (~tx_wr_block) else $fatal("inserting wr_done while wr_block in progress");
                        // synthesis translate_on                        
                    end                    

                    default : begin     // mem_wr
                        afu_tx_wr_hdr <= {cor_tx_wr_len, cor_tx_wr_addr[57:32], 1'b1, 5'b0 ,5'b0, `CCI_REQ_WR ,6'b0, cor_tx_wr_addr[31:0], 8'h3, tx_wr_tag};
                                                            
                        if (~tx_wr_block) begin                            
                            if (cor_tx_wr_len > 6'h1) begin     // block write
                                tx_wr_block <= 1'b1;
                                tx_wr_block_cnt <= cor_tx_wr_len - 1'b1;
                            end
                            else begin
                                tx_wr_tag <= tx_wr_tag + 1'b1;
                            end
                        end
                        else begin
                            if (tx_wr_block_cnt > 6'h1) begin
                                tx_wr_block_cnt <= tx_wr_block_cnt - 1'b1;
                            end
                            else begin
                                tx_wr_block <= 1'b0;
                                tx_wr_tag <= tx_wr_tag + 1'b1;
                            end
                        end
                    end
                endcase
                    
                afu_tx_data <= cor_tx_data;
            end
        end
    end    
    
                
    //-------------------------------------------------------            
    // TX_RD, drive afu_tx_rd port
    //-------------------------------------------------------
    always @(posedge clk) begin
        if ((~reset_n) | spl_reset) begin
            afu_tx_rd_valid <= 1'b0;
            tx_rd_tag <= 6'b0;
        end

        else begin
            afu_tx_rd_valid <= 1'b0;
            
            if (cor_tx_rd_valid) begin
                afu_tx_rd_valid <= 1'b1;
                afu_tx_rd_hdr <= {cor_tx_rd_len, cor_tx_rd_addr[57:32], 6'b0 ,5'b0, `CCI_REQ_RD ,6'b0, cor_tx_rd_addr[31:0], 8'h2, tx_rd_tag};
                tx_rd_tag <= tx_rd_tag + 1'b1;
            end
        end
    end    
    
                    
    //-------------------------------------------------------            
    // RX, forward CSR to afu_csr
    //-------------------------------------------------------
    always @(posedge clk) begin
        if ((~reset_n) | spl_reset) begin
            io_rx_csr_valid <= 1'b0;
        end

        else begin
            io_rx_csr_valid <= spl_rx_cfg_valid;
            io_rx_csr_addr <= spl_rx_hdr0[13:0];
            io_rx_csr_data <= spl_rx_data[31:0];        
        end
    end
    

    //-------------------------------------------------------            
    // RX, forward data to afu_core
    //-------------------------------------------------------
    always @(posedge clk) begin
        io_rx_rd_valid <= spl_rx_rd_valid;
        io_rx_data <= spl_rx_data;        
    end

    // for the last write
    always @(posedge clk) begin
        if ((~reset_n) | spl_reset) begin
            write_last_done <= 'b0;
        end
        else begin
	    write_last_done <= 'b0;
	    if (spl_rx_wr_valid0 & spl_rx_hdr0[5:0] == last_write_tag) write_last_done <= 'b1;
	    if (spl_rx_wr_valid1 & spl_rx_hdr1[5:0] == last_write_tag) write_last_done <= 'b1;
        end
    end

endmodule        
