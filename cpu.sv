`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/28/2024 06:11:12 AM
// Design Name: 
// Module Name: cpu
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module cpu(
    input rst_n,
    input clk,
    output reg [31:0] imem_addr,
    input [31:0] imem_insn,
    output reg [31:0] dmem_addr,
    inout [31:0] dmem_data,
    output reg dmem_wen
);

    reg [15:0] clock_counter;                                   
    reg [31:0] PC;                                              
    integer pc_trace_file, data_trace_file, i;                
    
    // Defining pipeline registers
    reg [31:0] instruction; 
    
    // Register File Registers
    reg [4:0] write_addr, write_addr_ex, write_addr_mem, write_addr_wb, addr_wb;        
    reg [4:0] read_addr;                                        
    reg [31:0] read_data, read_data_ex;                                       
    
    // Decode stage registers
    reg [6:0] opcode;
    reg [4:0] rd_prev, rd_prev2, rd_prev3, rd;
    reg [2:0] funct3, funct3_de, funct3_ex;
    reg [4:0] rs1;
    reg [11:0] immediate;
    reg [31:0] immediate_extended, immediate_extended_ex;
    
    // Execute stage registers
    reg [31:0] result, result_mem, result_wb, result_haz;
    
    // Valid Checks
    reg if_valid, id_valid, ie_valid, iw_valid, im_valid;
    
    // Hazard and Forward Check
    reg hazard, data_hazard;

    // Register File
    reg [10:0] register_file [7:0];

    // Initialize files for trace data
    initial begin
        // Initialize PC and registers
        for(int i = 0; i < 10; i = i + 1) begin
            register_file[i] = 0;
        end
        PC <= 0;
        dmem_wen <= 0;
        clock_counter <= 0;                             
    end


    // Fetch stage
    always @(posedge clk) begin
        if (!rst_n) begin
            if_valid <= 0;
            clock_counter <= 0;                               
        end else begin
            PC <= PC + 4;                           
            imem_addr <= PC;                             
     
            pc_trace_file = $fopen("heya.txt", "a");          
            $fwrite(pc_trace_file, "%h\n", imem_addr);         
            $fclose(pc_trace_file);                   
                   
            if_valid <= 1;                                     
            clock_counter <= clock_counter + 1;                
        end
    end
    
    always_comb begin      
        instruction = imem_insn;
    end


    // Decode Stage
    always @(posedge clk) begin
        if(!rst_n) begin
            id_valid <= 0;
        end else if(if_valid) begin
            opcode <= instruction[6:0];
            rd <= instruction[11:7];
            funct3 <= instruction[14:12];
            rs1 <= instruction[19:15];
            immediate <= instruction[31:20];
            
            id_valid <= 1;            
        end
    end

    always_comb begin
        if (rd_prev == rs1 || rd_prev2 == rs1 || rd_prev3 == rs1) begin 
            data_hazard = 1;
                
            if (rd_prev == rs1) begin
                read_data = result;    
            end else if (rd_prev2 == rs1) begin
                read_data = result_mem;
            end else if (rd_prev3 == rs1) begin
                read_data = result_haz;
            end 
                
        end else begin 
            data_hazard = 0;
            read_data = register_file[rs1]; 
        end
             
        funct3_de = funct3;     
        write_addr = rd;
        immediate_extended = {{20{immediate[11]}}, immediate};
    end


    // Execute Stage
    always @(posedge clk) begin
        if(!rst_n) begin
            ie_valid = 0;
        end else if(id_valid) begin
            read_data_ex <= read_data; 
            write_addr_ex <= write_addr;
            immediate_extended_ex <= immediate_extended;
            funct3_ex <= funct3_de;

            rd_prev <= write_addr;
            rd_prev2 <= rd_prev;
            rd_prev3 <= rd_prev2;
            
            ie_valid <= 1;
        end 
    end

    always_comb begin 
        case (funct3_ex)
            // ADDI
            3'b000: result = immediate_extended_ex + read_data_ex; 
            
            // SLTI (Set Less Than Immediate)
            3'b010: begin
                if (signed'(read_data_ex) < signed'(immediate_extended_ex)) begin
                    result = 32'h1;
                end else begin
                    result = 32'h0;
                end
            end
            
            // SLTIU (Set Less Than Immediate Unsigned)
            3'b011: begin
                if (read_data_ex < immediate_extended_ex) begin
                    result = 32'h1;
                end else begin
                    result = 32'h0;
                end
            end
            
            // XORI (Bitwise XOR Immediate)
            3'b100: result = read_data_ex ^ immediate_extended_ex;
            
            // ORI (Bitwise OR Immediate)
            3'b110: result = read_data_ex | immediate_extended_ex;
            
            // ANDI (Bitwise AND Immediate)
            3'b111: result = read_data_ex & immediate_extended_ex;
            
            3'b001: 
                case (immediate_extended_ex[11:5])
                    // SLLI (Shift Left Logical Immediate)
                    7'b0000000: result = read_data_ex << immediate_extended_ex[4:0];
                endcase
            
            3'b101: begin
                case (immediate_extended_ex[11:5])
                    // SRLI (Shift Right Logical Immediate)
                    7'b0000000: result = read_data_ex >> immediate_extended_ex[4:0];
                    
                    // SRAI (Shift Right Arithmetic Immediate)
                    7'b0100000:result = $signed(read_data_ex) >>> immediate_extended_ex[4:0]; 
                endcase
            end
            
            default: result = 32'h0; // Default case
        endcase

        write_addr_mem = write_addr_ex;
    end


    // Memory Stage
    always @(posedge clk) begin
        if(!rst_n) begin
            im_valid <= 0;
        end else if(ie_valid) begin  
            result_mem <= result;
            result_haz <= result_mem;
            write_addr_wb <= write_addr_mem;

            dmem_wen <= 1;            
            im_valid <= 1;
        end
    end
  
    
    // Write Back Stage
    always @(posedge clk) begin
        if(!rst_n) begin
            iw_valid = 0;
        end else if(im_valid && dmem_wen) begin
            result_wb <= result_mem;
            addr_wb <= write_addr_wb;
            
            register_file[addr_wb] <= result_wb; 
            
            if (iw_valid) begin             
                data_trace_file = $fopen("beya.txt", "a");
                $fwrite(data_trace_file, "Clock Counter: %d, Register %d: %h\n", clock_counter, addr_wb, result_wb);
                $fclose(data_trace_file);
            end
            
            iw_valid = 1;
        end
    end
    
    
endmodule
