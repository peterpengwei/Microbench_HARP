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


module spl_fifo #(
    parameter FIFO_WIDTH = 32,
    parameter FIFO_DEPTH_BITS = 8,
    parameter FIFO_ALMOSTFULL_THRESHOLD = 2**FIFO_DEPTH_BITS - 4
) (
    input  wire                         clk,
    input  wire                         reset_n,
    
    input  wire                         we,              // input   write enable
    input  wire [FIFO_WIDTH - 1:0]      din,            // input   write data with configurable width

    input  wire                         re,              // input   read enable    
    output reg                          valid,           // dout valid
    output reg  [FIFO_WIDTH - 1:0]      dout,            // output  read data with configurable width    

    output reg  [FIFO_DEPTH_BITS - 1:0] count,              // output  FIFOcount
    output reg                          empty,              // output  FIFO empty
    output reg                          full,               // output  FIFO full                
    output reg                          almostfull         // output  configurable programmable full/ almost full    
);


    reg     overflow;
        
    reg  [FIFO_DEPTH_BITS - 1:0]        rp;
    reg  [FIFO_DEPTH_BITS - 1:0]        wp;
    reg                                 empty_d1;
    
    wire                                mem_we;
    reg                                 mem_re;
    wire [FIFO_WIDTH - 1:0]             mem_dout;
    
        
    spl_sdp_mem #(.DATA_WIDTH(FIFO_WIDTH),
                  .ADDR_WIDTH(FIFO_DEPTH_BITS)) spl_fifo_mem( 
        .clk        (clk),
        .we         (mem_we),
		.re 		(re),
        .raddr      (rp),
        .waddr      (wp),
        .din        (din),
        .dout       (mem_dout)
    );
             
        
    assign mem_we = we & ((~re) | (~empty) | mem_re);
            
    always @(posedge clk) begin
        if (~reset_n) begin
            empty <= 1'b1;
            empty_d1 <= 1'b1;
            full <= 1'b0;
            almostfull <= 1'b0;
            count <= 'b0;	//32'b0;            
            rp <= 'b0;
            wp <= 'b0;
            valid <= 1'b0;
            mem_re <= 1'b0;
            
            overflow <= 1'b0;
        end
        
        else begin
            empty_d1 <= empty;
            valid <= 1'b0;
            mem_re <= 1'b0;
            
            // write and read at same time and fifo is empty, bypass mem, valid din
            if (we & re & empty & (~mem_re)) begin
                valid <= 1'b1;
                dout <= din;
            end
            
            // read and write at same time, advant wp and rp, count is not changing, valid mem_dout
            if (we & re & (~empty)) begin // & (~empty_d1)) begin
                wp <= wp + 1'b1;                    
                rp <= rp + 1'b1;
                mem_re <= 1'b1;
            end
                                        
            // just write, advance wp, increament count
            if (we & ((~re) | (re & empty & mem_re))) begin   // | (we & re & (~empty) & (empty_d1))) begin
                wp <= wp + 1'b1;
                count <= count + 1'b1;

                empty <= 1'b0;

                if (count == (2**FIFO_DEPTH_BITS-1))
                    full <= 1'b1;

                if (count == (FIFO_ALMOSTFULL_THRESHOLD-1))
                    almostfull <= 1'b1;
            end
            
            // just read, decreament count
            if ((~we) & re & (~empty)) begin // & (~empty_d1)) begin
                rp <= rp + 1'b1;
                count <= count - 1'b1;                    
                full <= 1'b0;
                mem_re <= 1'b1;
                
                if (count == FIFO_ALMOSTFULL_THRESHOLD)
                    almostfull <= 1'b0;

                if (count == 1'b1)
                    empty <= 1'b1; 
            end
                       
            if (mem_re) begin
                valid <= 1'b1;  
                dout <= mem_dout;                                                          
            end   

            // synthesis translate_off
            if (reset_n === 1'b1) begin                  
                assert (~(we & (~re) & full)) else $fatal("overflow");   
				assert ((we & re &(wp == rp) & (~empty)) == 1'b0) else 
				    $fatal("read-during-write at same time to location %x", wp);
			end
            // synthesis translate_on                            
        end
    end

endmodule

