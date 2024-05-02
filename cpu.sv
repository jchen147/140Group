`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 04/02/2024 06:11:12 AM
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
    inout reg [31:0] dmem_data,
    output reg dmem_wen,
    output reg [3:0] byte_en
);

    reg [15:0] clock_counter;                                   
    reg [31:0] PC;                                              
    integer pc_trace_file, data_trace_file, i;                
    
    // Defining pipeline registers
    reg [31:0] instruction; 
    
    // Register File Registers
    reg [4:0] write_addr, write_addr_ex, write_addr_mem, write_addr_wb, addr_wb;        
    reg [4:0] read_addr;                                        
    reg [31:0] read_data, read_data2, read_data_ex, read_data_ex2;                                       
    
    // Decode stage registers
    reg [6:0] opcode, opmem;
    reg [4:0] rd_prev, rd_prev2, rd_prev3, rd2_prev, rd2_prev2, rd2_prev3, rd;
    reg [2:0] funct3, funct3_de, funct3_ex;
    reg [6:0] funct7, funct7_de, funct7_ex;
    reg [4:0] rs1, rs2;
    reg [11:0] immediate;
    reg [4:0] offset, offset_ex, offset_mem, offset_wb;
    reg [6:0] immediate_store, imex, immem, imwb;
    reg [31:0] immediate_extended, immediate_extended_ex;
    
    // Execute stage registers
    reg [31:0] result, result_mem, result_wb, result_haz;
    
    // Valid Checks
    reg if_valid, id_valid, ie_valid, iw_valid, im_valid;
    
    // Hazard and Forward Check
    reg hazard, data_hazard;

    // Register File
    reg [31:0] register_file [31:0];

    reg [31:0] dmem_data_out; // Hold data to be written to memory
    assign dmem_data = dmem_wen ? dmem_data_out : 32'bz; 

    reg [31:0] dmem_addr_de, dmem_addr_ex, dmem_addr_mem;
    reg [31:0] dmem_data_out_de, dmem_data_out_ex, dmem_data_out_mem;

    // Initialize files for trace data
    initial begin
        // Initialize PC and registers
        for(int i = 0; i < 14; i = i + 1) begin
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
            case(instruction[6:0]) 
                7'b0010011: begin   // I-Type
                    opcode <= instruction[6:0];
                    rd <= instruction[11:7];
                    funct3 <= instruction[14:12];
                    rs1 <= instruction[19:15];
                    immediate <= instruction[31:20];
                end
                7'b0110011: begin   // R-Type
                    opcode <= instruction[6:0];
                    rd <= instruction[11:7];
                    funct3 <= instruction[14:12];
                    rs1 <= instruction[19:15];
                    rs2 <= instruction[24:20];
                    funct7 <= instruction[31:25];
                end
                7'b0000011: begin
                    opcode <= instruction[6:0];
                    rd <= instruction[11:7];
                    funct3 <= instruction[14:12];
                    rs1 <= instruction[19:15];
                    immediate <= instruction[31:20];
                end
                7'b0100011: begin
                    opcode <= instruction[6:0];
                    offset <= instruction[11:7];
                    funct3 <= instruction[14:12];
                    rs1 <= instruction[19:15];
                    rs2 <= instruction[24:20];
                    immediate_store <= instruction[31:25];         
                end

            endcase
            
            dmem_addr_de <= 0;
            dmem_data_out_de <= 0;

            case (opmem)
                7'b0100011: begin // S-type (Store)
                    dmem_addr_de = register_file[rs1] + immediate_extended; // Calculate effective address
                    dmem_data_out_de = register_file[rs2]; // Data to store
                end
                7'b0000011: begin // I-type (Load)
                    dmem_addr_de = register_file[rs1] + immediate_extended; // Calculate effective address
                    // Load does not need to set dmem_data_out_de
                    dmem_data_out_de = 32'bz; 
                end
                default: begin
                    dmem_addr_de = 0;
                    dmem_data_out_de = 0;
                end
            endcase
            
            
            id_valid <= 1;            
        end
    end

    always_comb begin
        case(opcode) 
            7'b0010011: begin   // I-Type
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
                   
                immediate_extended = {{20{immediate[11]}}, immediate};
                funct3_de = funct3;     
                write_addr = rd;
            end
                
            7'b0110011: begin   // R-Type
            
                if (rd_prev == rs1) begin 
                    read_data = result;
                    data_hazard = 1;
                end else if (rd_prev2 == rs1) begin
                    read_data = result_mem; 
                    data_hazard = 1;
                end else if (rd_prev3 == rs1) begin
                    read_data = result_haz; 
                    data_hazard = 1;
                end else begin 
                    data_hazard = 0;
                    read_data = register_file[rs1];
                end
                
                if (rd_prev == rs2) begin 
                    read_data2 = result; 
                    data_hazard = 1;
                end else if (rd_prev2 == rs2) begin
                    read_data2 = result_mem;
                    data_hazard = 1;
                end else if (rd_prev3 == rs2) begin
                    read_data2 = result_haz;
                    data_hazard = 1;
                end else begin 
                    data_hazard = 0;
                    read_data2 = register_file[rs2];
                end
                    
                funct7_de = funct7;
                funct3_de = funct3;     
                write_addr = rd;
            end 
            
            7'b0000011: begin
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
                   
                immediate_extended = {{20{immediate[11]}}, immediate};
                funct3_de = funct3;     
                write_addr = rd;
            end
            
            7'b0100011: begin
                if (rd_prev == rs1) begin 
                    read_data = result;
                    data_hazard = 1;
                end else if (rd_prev2 == rs1) begin
                    read_data = result_mem; 
                    data_hazard = 1;
                end else if (rd_prev3 == rs1) begin
                    read_data = result_haz; 
                    data_hazard = 1;
                end else begin 
                    data_hazard = 0;
                    read_data = register_file[rs1];
                end
                
                if (rd_prev == rs2) begin 
                    read_data2 = result; 
                    data_hazard = 1;
                end else if (rd_prev2 == rs2) begin
                    read_data2 = result_mem;
                    data_hazard = 1;
                end else if (rd_prev3 == rs2) begin
                    read_data2 = result_haz;
                    data_hazard = 1;
                end else begin 
                    data_hazard = 0;
                    read_data2 = register_file[rs2];
                end
                
                offset_ex = offset;
                imex = immediate_store;    
                funct3_de = funct3;     
                write_addr = rd;
            end
 
        endcase     
    end


    // Execute Stage
    always @(posedge clk) begin
        if(!rst_n) begin
            ie_valid = 0;
        end else if(id_valid) begin
            case(opcode) 
                7'b0010011: begin   // I-Type
                    read_data_ex <= read_data; 
                    write_addr_ex <= write_addr;
                    immediate_extended_ex <= immediate_extended;
                    funct3_ex <= funct3_de;
        
                    rd_prev <= write_addr;
                    rd_prev2 <= rd_prev;
                    rd_prev3 <= rd_prev2;
                end
                    
                7'b0110011: begin   // R-Type
                    read_data_ex <= read_data; 
                    read_data_ex2 <= read_data2; 
                    
                    write_addr_ex <= write_addr;
                    funct7_ex <= funct7_de;
                    funct3_ex <= funct3_de;
        
                    rd_prev <= write_addr;
                    rd_prev2 <= rd_prev;
                    rd_prev3 <= rd_prev2;
                    
                    rd2_prev <= write_addr;
                    rd2_prev2 <= rd_prev;
                    rd2_prev3 <= rd_prev2;
                end
                
                7'b0000011: begin
                    read_data_ex <= read_data; 
                    write_addr_ex <= write_addr;
                    immediate_extended_ex <= immediate_extended;
                    funct3_ex <= funct3_de;
        
                    rd_prev <= write_addr;
                    rd_prev2 <= rd_prev;
                    rd_prev3 <= rd_prev2;
                end
                
                7'b0100011: begin
                    read_data_ex <= read_data; 
                    read_data_ex2 <= read_data2; 
                    
                    write_addr_ex <= write_addr;
                    funct3_ex <= funct3_de;
        
                    rd_prev <= write_addr;
                    rd_prev2 <= rd_prev;
                    rd_prev3 <= rd_prev2;
                    
                    rd2_prev <= write_addr;
                    rd2_prev2 <= rd_prev;
                    rd2_prev3 <= rd_prev2;
                    
                    offset_mem = offset_ex;
                    immem = imex;
                end
            endcase     
           
            dmem_addr_ex <= dmem_addr_de;
            dmem_data_out_ex <= dmem_data_out_de;
           
            opmem <= opcode;
            ie_valid <= 1;
        end 
    end

    always_comb begin 
        case(opmem) 
            7'b0010011: begin   // I-Type
            
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
                  
            end
                    
            7'b0110011: begin   // R-Type
                case (funct3_ex) 
                    
                    3'b000: begin
                        case (funct7_ex)
                            7'b0000000: result = read_data_ex + read_data_ex2;  // ADD
                            7'b0100000: result = read_data_ex - read_data_ex2;   // SUB                 
                        endcase
                    end
                    
                    3'b001: begin 
                        case (funct7_ex)
                            7'b0000000: result = read_data_ex << read_data_ex2[4:0];  // SLL
                        endcase
                    end
                    
                    // SLT
                    3'b010: begin 
                        case (funct7_ex)
                            7'b0000000: begin 
                                if (signed'(read_data_ex) < signed'(read_data_ex2)) begin
                                    result = 32'h1;
                                end else begin
                                    result = 32'h0;
                                end
                            end
                        endcase
                    end
                    
                    // SLTU
                    3'b011: begin 
                        case (funct7_ex)
                            7'b0000000: begin 
                                if (unsigned'(read_data_ex) < unsigned'(read_data_ex2)) begin
                                    result = 32'h1;
                                end else begin
                                    result = 32'h0;
                                end
                            end
                        endcase
                    end
                    
                    3'b100: begin 
                        case (funct7_ex)
                            7'b0000000: result = read_data_ex ^ read_data_ex2;  // XOR
                        endcase
                    end
                    
                    3'b101: begin 
                        case (funct7_ex)
                            7'b0000000: result = read_data_ex >> read_data_ex2[4:0];  // SRL
                            7'b0100000: result = $signed(read_data_ex) >>> read_data_ex2[4:0];  // SRA
                        endcase
                    end
                    
                    3'b110: begin 
                        case (funct7_ex)
                            7'b0000000: result = read_data_ex | read_data_ex2;  // OR
                        endcase
                    end
                    
                    3'b111: begin 
                        case (funct7_ex)
                            7'b0000000: result = read_data_ex & read_data_ex2;  // AND
                        endcase
                    end
                    
                    default: result = 32'h0; // Default case
                    
                endcase
            end
                
                
//            // Load Instructions
//            7'b0000011: begin
            
//                dmem_addr = read_data_ex + offset_mem;  // Calculate the memory address for load operation
//                dmem_wen = 0;                           // Disable write enable for load operation
            
//                case(funct3_ex)
//                    3'b000: byte_en = 4'b0001;          // LB (load byte)
//                    3'b001: byte_en = 4'b0011;          // LH (load halfword)
//                    3'b010: byte_en = 4'b1111;          // LW (load word)
//                    default: byte_en = 4'b0000;         // Default case
//                endcase
//            end 
            
//            // Store Instructions
//            7'b0100011: begin 
//                dmem_addr <= read_data_ex + offset_mem; // Calculate the memory address for store operation
//                dmem_data <= read_data_ex2;             // Set data to be written to memory
                
//                case(funct3_ex)
//                    3'b000: byte_en <= 4'b0001;     // SB (store byte)
//                    3'b001: byte_en <= 4'b0011;     // SH (store halfword)
//                    3'b010: byte_en <= 4'b1111;     // SW (store word)
//                    default: byte_en <= 4'b0000;    // Default case
//                endcase
//            end
            
        endcase    
       
        write_addr_mem = write_addr_ex;
    end


    // Memory Stage
    always @(posedge clk) begin
        if(!rst_n) begin
            im_valid <= 0;
            byte_en <= 4'b0000;
        end else if(ie_valid) begin  
        
//            if (opmem == 7'b0000011) begin
//                result_mem <= dmem_data; // For loads, result_mem should be the data read from memory
//                dmem_wen <= 0;
//            end else begin
//                result_mem <= result;
//                dmem_wen <= 1;
//            end

            if (opmem == 7'b0100011) begin          // Store instruction
                case (funct3_ex)
                    3'b000: byte_en <= 4'b0001;     // SB
                    3'b001: byte_en <= 4'b0011;     // SH
                    3'b010: byte_en <= 4'b1111;     // SW
                    default: byte_en <= 4'b0000;
                endcase
                dmem_wen <= 1;
                dmem_addr <= dmem_addr_ex;
                dmem_data_out <= dmem_data_out_ex;
            end 
            else if (opmem == 7'b0000011) begin     // Load instruction
                dmem_wen <= 0; 
                byte_en <= 4'b1111;
                case (funct3_ex)
                    3'b000: result_mem = {{24{dmem_data[7]}}, dmem_data[7:0]};      // LB: Sign-extend byte
                    3'b001: result_mem = {{16{dmem_data[15]}}, dmem_data[15:0]};    // LH: Sign-extend half-word
                    3'b010: result_mem = dmem_data;                                 // LW: Direct assignment
                    3'b100: result_mem = {24'b0, dmem_data[7:0]};                   // LBU: Zero-extend byte
                    3'b101: result_mem = {16'b0, dmem_data[15:0]};                  // LHU: Zero-extend half-word
                    default: result_mem = 32'b0;                                    // Default case
                endcase                         
            end
            else begin
                // For R-type or I-Type that do not interact with memory
                result_mem <= result; 
                result_haz <= result_mem;
                write_addr_wb <= write_addr_mem;
                byte_en <= 4'b0000;

                dmem_wen <= 0;  
            end
        
//            result_haz <= result_mem; 
//            write_addr_wb <= write_addr_mem; 
            
            im_valid <= 1;
        end
    end
  
    
    // Write Back Stage
    always @(posedge clk) begin
        if(!rst_n) begin
            iw_valid = 0;
//        end else if(im_valid && dmem_wen) begin
        end else if(im_valid) begin
//            result_wb <= result_mem;
//            addr_wb <= write_addr_wb;
            
            register_file[addr_wb] <= result_wb; 
            
            if(opmem == 7'b0100011 || opmem == 7'b0000011) begin
                result_wb <= result_mem; 
                addr_wb <= write_addr_mem; 
            end
            else begin
                result_wb <= result_mem; 
                addr_wb <= write_addr_wb;
            end    
    
            // Write the result back to the register file
            if (addr_wb != 0) begin 
                register_file[addr_wb] <= result_wb;
            end

            if (iw_valid) begin             
                data_trace_file = $fopen("beya.txt", "a");
                $fwrite(data_trace_file, "Clock Counter: %d, Register %d: %h\n", clock_counter, addr_wb, result_wb);
                $fclose(data_trace_file);
            end
            
            iw_valid = 1;
        end
    end
    
endmodule
