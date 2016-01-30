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


module afu_csr(
    input  wire                             clk,
    input  wire                             reset_n,

    input  wire                             spl_reset,        
                
    // RX, afu_io --> afu_csr
    input  wire                             io_rx_csr_valid,
    input  wire [13:0]                      io_rx_csr_addr,
    input  wire [31:0]                      io_rx_csr_data,
    
    // afu_csr-->afu_core, afu_id
    output reg                              csr_id_valid,
    input  wire                             csr_id_done,
    output reg  [31:0]                      csr_id_addr,
//    output reg  [63:0]                      csr_id,
    
    // afu_csr-->afu_core, afu_scratch
    output reg                              csr_scratch_valid,
    input  wire                             csr_scratch_done,
    output reg  [31:0]                      csr_scratch_addr,
    output reg  [63:0]                      csr_scratch,

    // afu_csr-->afu_core, afu_ctx_base
    output reg                              csr_ctx_base_valid,
    output reg  [57:0]                      csr_ctx_base
);


    localparam [5:0]
        AFU_CSR_DSR_BASEL          = 6'b00_0000,   //10'h280,      // a00
        AFU_CSR_DSR_BASEH          = 6'b00_0001,   //10'h281,      // a04
        AFU_CSR_CTX_BASEL          = 6'b00_0010,   //10'h282,      // a08
        AFU_CSR_CTX_BASEH          = 6'b00_0011,   //10'h283,      // a0c  
        AFU_CSR_SCRATCH            = 6'b11_1111;   //10'h2bf;      // afc        
                

    reg  [31:0]                     afu_dsr_base;
    
        
    //--------------------------------------------------------------------
    // RX - afu_csr<--afu_io                 
    //--------------------------------------------------------------------
    always @(posedge clk) begin
        if ((~reset_n) | spl_reset) begin
            csr_id_valid <= 1'b0;
            csr_scratch_valid <= 1'b0;
            csr_ctx_base_valid <= 1'b0;
        end 
        
        else begin
            if (csr_id_done) csr_id_valid <= 1'b0;
            if (csr_scratch_done) csr_scratch_valid <= 1'b0;
                                    
            if (io_rx_csr_valid) begin
                if (io_rx_csr_addr[13:6] == 8'h8a) begin
                    case (io_rx_csr_addr[5:0]) 
                        AFU_CSR_DSR_BASEH : begin                
                            afu_dsr_base[31:26] <= io_rx_csr_data[5:0];
                            
                            // synthesis translate_off
                            assert (io_rx_csr_data[31:6] == 26'b0) else $fatal("afu_dsr_baseh = %x is out of 256GB range",  io_rx_csr_data);
                            // synthesis translate_on                                  
                        end

                        AFU_CSR_DSR_BASEL : begin                
                            afu_dsr_base[25:0] <= io_rx_csr_data[31:6];
                            csr_id_valid <= 1'b1;                            
                            csr_id_addr <= {afu_dsr_base[31:26], io_rx_csr_data[31:6]};
//                            csr_id <= AFU_ID;
                            
                            // synthesis translate_off
                            assert (io_rx_csr_data[5:0] == 6'b0) else $fatal("afu_dsr_basel = %x is not CL aligned", io_rx_csr_data);
                            // synthesis translate_on                                             
                        end

                        AFU_CSR_CTX_BASEH : begin                
                            csr_ctx_base[57:26] <= io_rx_csr_data;
                        end

                        AFU_CSR_CTX_BASEL : begin                
                            csr_ctx_base[25:0] <= io_rx_csr_data[31:6];
                            csr_ctx_base_valid <= 1'b1;
                            
                            // synthesis translate_off
                            assert (io_rx_csr_data[5:0] == 6'b0) else $fatal("csr_afu_ctx_base = %x is not CL aligned", {csr_ctx_base[57:26], io_rx_csr_data});
                            // synthesis translate_on                            
                        end

                        AFU_CSR_SCRATCH : begin                
                            csr_scratch_valid <= 1'b1;                            
                            csr_scratch_addr <= afu_dsr_base + AFU_CSR_SCRATCH;
                            csr_scratch <= {afu_dsr_base[31:0], io_rx_csr_data};
                        end                    
                    endcase
                end
            end
        end
    end // rx csr                

endmodule        
