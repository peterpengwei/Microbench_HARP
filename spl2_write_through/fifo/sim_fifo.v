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


module sim_fifo #(
    parameter FIFO_WIDTH = 32,
    parameter FIFO_DEPTH_BITS = 8,
    parameter FIFO_ALMOSTFULL_THRESHOLD = 2**FIFO_DEPTH_BITS - 4,
    parameter FIFO_ALMOSTEMPTY_THRESHOLD = 2
) (
    input  wire                         clk,
    input  wire                         reset_n,
    
    input  wire                         we,              // input   write enable
    input  wire [FIFO_WIDTH - 1:0]      din,            // input   write data with configurable width
    input  wire                         re,              // input   read enable
    
    output reg  [FIFO_WIDTH - 1:0]      dout,            // output  read data with configurable width    
    output reg  [FIFO_DEPTH_BITS - 1:0] count,              // output  FIFOcount
    output reg                          empty,              // output  FIFO empty
    output reg                          almostempty,              // output  FIFO almost empty
    output reg                          full,               // output  FIFO full                
    output reg                          almostfull         // output  configurable programmable full/ almost full    
);

    // synthesis translate_off
    reg                                 valid;
    reg                                 overflow;
    reg                                 underflow;
    // synthesis translate_on
    
    
    reg  [FIFO_DEPTH_BITS - 1:0]        rp;
    reg  [FIFO_DEPTH_BITS - 1:0]        wp;

`ifdef VENDOR_XILINX    
    (* ram_extract = "yes", ram_style = "block" *)
    reg  [FIFO_WIDTH - 1:0]         mem[2**FIFO_DEPTH_BITS-1:0];
`else
    reg  [FIFO_WIDTH - 1:0]         mem[2**FIFO_DEPTH_BITS-1:0];
`endif
        
        
    always @(posedge clk) begin
        if (~reset_n) begin
            empty <= 1'b1;
            almostempty <= 1'b1;
            full <= 1'b0;
            almostfull <= 1'b0;
            count <= 0;            
            rp <= 0;
            wp <= 0;
            
            // synthesis translate_off
            valid <= 1'b0;
            overflow <= 1'b0;
            underflow <= 1'b0;            
            // synthesis translate_on
        end
        
        else begin
            // synthesis translate_off
            valid <= 0;
            // synthesis translate_on
             
            case ({we, re})
                // write and read at same time
                2'b11 : begin
                    wp <= wp + 1'b1;
//                    mem[wp] <= din;
                    
                    rp <= rp + 1'b1;
//                    dout <= mem[rp];
                    
                    // synthesis translate_off
                    valid <= 1;
                    assert (wp != rp) else $fatal("simultaneous read and write to FIFO");
                    // synthesis translate_on
                end
                
                // write only
                2'b10 : begin
                    if (full) begin                                                
                        // synthesis translate_off
                        overflow <= 1;
                        assert(~full) else $fatal("overflow!");
                        // synthesis translate_on                    
                    end
                    
                    else begin
                        wp <= wp + 1'b1;
//                        mem[wp] <= din;
                        count <= count + 1'b1;

                        empty <= 1'b0;

                        if (count == (FIFO_ALMOSTEMPTY_THRESHOLD-1))
                            almostempty <= 1'b0;
                            
                        if (count == (2**FIFO_DEPTH_BITS-1))
                            full <= 1'b1;

                        if (count == (FIFO_ALMOSTFULL_THRESHOLD-1))
                            almostfull <= 1'b1;
                    end
                end
                
                // read only
                2'b01 : begin
                    if (empty) begin                                               
                        // synthesis translate_off
                        underflow <= 1;
                        assert (!empty) else $fatal("underflow!");
                        // synthesis translate_on
                    end
                    
                    else begin
                        rp <= rp + 1'b1;
//                        dout <= mem[rp];
                        count <= count - 1'b1;                    
                        full <= 0;
                    
                        if (count == FIFO_ALMOSTFULL_THRESHOLD)
                            almostfull <= 1'b0;
                                            
                        if (count == 1)
                            empty <= 1'b1;
                            
                        if (count == FIFO_ALMOSTEMPTY_THRESHOLD)
                            almostempty <= 1'b1;
                        
                        // synthesis translate_off    
                        valid <= 1;  
                        // synthesis translate_on                         
                    end 
                end
                
                default : begin

                end
            endcase
        end
    end


    always @(posedge clk) begin
        if (we == 1'b1)
            mem[wp] <= din;
            
        dout <= mem[rp];            
    end
    
endmodule

