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


module afu_top (
    input  wire                             clk,
    input  wire                             reset_n,
    input  wire                             spl_enable,
    input  wire                             spl_reset,
        
    // AFU TX read request
    input  wire                             spl_tx_rd_almostfull,
    output wire                             afu_tx_rd_valid,
    output wire [98:0]                      afu_tx_rd_hdr,
    
    // AFU TX write request
    input  wire                             spl_tx_wr_almostfull,
    output wire                             afu_tx_wr_valid,
    output wire                             afu_tx_intr_valid,
    output wire [98:0]                      afu_tx_wr_hdr,    
    output wire [511:0]                     afu_tx_data,
    
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
    input  wire [`CCI_RX_HDR_WIDTH-1:0]     spl_rx_hdr1    
);


    wire                    io_rx_csr_valid;
    wire [13:0]             io_rx_csr_addr;
    wire [31:0]             io_rx_csr_data;
    
    wire                    io_rx_rd_valid;
    wire [511:0]            io_rx_data;

    wire                    csr_id_valid;
    wire                    csr_id_done;
    wire [31:0]             csr_id_addr;
//    wire [63:0]             csr_id;

    wire                    csr_scratch_valid;
    wire                    csr_scratch_done;
    wire [31:0]             csr_scratch_addr;
    wire [63:0]             csr_scratch;

    wire                    csr_ctx_base_valid;
    wire [57:0]             csr_ctx_base;
    
    wire                    cor_tx_rd_valid;
    wire [57:0]             cor_tx_rd_addr;
    wire [5:0]              cor_tx_rd_len;

    wire                    cor_tx_wr_valid;
    wire                    cor_tx_dsr_valid;
    wire [57:0]             cor_tx_wr_addr;
    wire [5:0]              cor_tx_wr_len;
    wire [511:0]            cor_tx_data;
    wire                    cor_tx_fence_valid;
    wire                    cor_tx_done_valid;

    // for the last write
    wire		    write_last_sent;
    wire		    write_last_done;


    afu_csr afu_csr(
        .clk                        (clk),
        .reset_n                    (reset_n),
        .spl_reset                  (spl_reset),        
             
        // afu_csr-->afu_core, afu_id
        .csr_id_valid               (csr_id_valid),
        .csr_id_done                (csr_id_done),
        .csr_id_addr                (csr_id_addr),
//        .csr_id                     (csr_id),
    
        // afu_csr-->afu_core, afu_scratch
        .csr_scratch_valid          (csr_scratch_valid),
        .csr_scratch_done           (csr_scratch_done),
        .csr_scratch_addr           (csr_scratch_addr),
        .csr_scratch                (csr_scratch),

        // afu_csr-->afu_core, afu_ctx_base
        .csr_ctx_base_valid         (csr_ctx_base_valid),
        .csr_ctx_base               (csr_ctx_base),                

        // RX, afu_io --> afu_csr
        .io_rx_csr_valid            (io_rx_csr_valid),
        .io_rx_csr_addr             (io_rx_csr_addr),
        .io_rx_csr_data             (io_rx_csr_data)
    );
       
    
    afu_core afu_core(
        .clk                        (clk),
        .reset_n                    (reset_n),
        .spl_enable                 (spl_enable),
        .spl_reset                  (spl_reset),
        
        // TX_RD request, afu_core --> afu_io
        .spl_tx_rd_almostfull       (spl_tx_rd_almostfull),
        .cor_tx_rd_valid            (cor_tx_rd_valid),
        .cor_tx_rd_addr             (cor_tx_rd_addr),
        .cor_tx_rd_len              (cor_tx_rd_len),
    
        // TX_WR request, afu_core --> afu_io
        .spl_tx_wr_almostfull       (spl_tx_wr_almostfull),    
        .cor_tx_wr_valid            (cor_tx_wr_valid),
        .cor_tx_dsr_valid           (cor_tx_dsr_valid),
        .cor_tx_fence_valid         (cor_tx_fence_valid),
        .cor_tx_done_valid          (cor_tx_done_valid),                
        .cor_tx_wr_addr             (cor_tx_wr_addr),
        .cor_tx_wr_len              (cor_tx_wr_len),
        .cor_tx_data                (cor_tx_data),
    
        // RX_RD
        .io_rx_rd_valid             (io_rx_rd_valid),
        .io_rx_data                 (io_rx_data),

	// for the last write
	.write_last_sent	    (write_last_sent),
	.write_last_done	    (write_last_done),
            
        // afu_csr-->afu_core, afu_id
        .csr_id_valid               (csr_id_valid),
        .csr_id_done                (csr_id_done),
        .csr_id_addr                (csr_id_addr),
//        .csr_id                     (csr_id),
    
        // afu_csr-->afu_core, afu_scratch
        .csr_scratch_valid          (csr_scratch_valid),
        .csr_scratch_done           (csr_scratch_done),
        .csr_scratch_addr           (csr_scratch_addr),
        .csr_scratch                (csr_scratch),

        // afu_csr-->afu_core, afu_ctx_base
        .csr_ctx_base_valid         (csr_ctx_base_valid),
        .csr_ctx_base               (csr_ctx_base)                                     
    );


    afu_io afu_io(
        .clk                        (clk),
        .reset_n                    (reset_n),
        .spl_enable                 (spl_enable),
        .spl_reset                  (spl_reset),     
        
        // AFU TX read request
        .afu_tx_rd_valid            (afu_tx_rd_valid),
        .afu_tx_rd_hdr              (afu_tx_rd_hdr),
    
        // AFU TX write request
        .afu_tx_wr_valid            (afu_tx_wr_valid),
        .afu_tx_intr_valid          (afu_tx_intr_valid),
        .afu_tx_wr_hdr              (afu_tx_wr_hdr),    
        .afu_tx_data                (afu_tx_data),
    
        // AFU RX read response
        .spl_rx_rd_valid            (spl_rx_rd_valid),
        .spl_rx_wr_valid0           (spl_rx_wr_valid0),
        .spl_rx_cfg_valid           (spl_rx_cfg_valid),
        .spl_rx_intr_valid0         (spl_rx_intr_valid0),
        .spl_rx_umsg_valid          (spl_rx_umsg_valid),
        .spl_rx_hdr0                (spl_rx_hdr0),
        .spl_rx_data                (spl_rx_data),
    
        // AFU RX write response
        .spl_rx_wr_valid1           (spl_rx_wr_valid1),
        .spl_rx_intr_valid1         (spl_rx_intr_valid1),
        .spl_rx_hdr1                (spl_rx_hdr1),
        
        // TX_RD request, afu_core --> afu_io
        .cor_tx_rd_valid            (cor_tx_rd_valid),
        .cor_tx_rd_addr             (cor_tx_rd_addr),
        .cor_tx_rd_len              (cor_tx_rd_len),        
    
        // TX_WR request, afu_core --> afu_io
        .cor_tx_wr_valid            (cor_tx_wr_valid),
        .cor_tx_dsr_valid           (cor_tx_dsr_valid),
        .cor_tx_fence_valid         (cor_tx_fence_valid),
        .cor_tx_done_valid          (cor_tx_done_valid),                
        .cor_tx_wr_addr             (cor_tx_wr_addr), 
        .cor_tx_wr_len              (cor_tx_wr_len),        
        .cor_tx_data                (cor_tx_data),                

        // RX_RD
        .io_rx_rd_valid             (io_rx_rd_valid),
        .io_rx_data                 (io_rx_data),

	// for the last write
	.write_last_sent	    (write_last_sent),
	.write_last_done	    (write_last_done),
        
        // CSR RX
        .io_rx_csr_valid            (io_rx_csr_valid),
        .io_rx_csr_addr             (io_rx_csr_addr),
        .io_rx_csr_data             (io_rx_csr_data)
    );
endmodule        
