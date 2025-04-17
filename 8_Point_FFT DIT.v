`timescale 1ns / 1ps

module fft_test (
    input clk,
    input reset,
    input enable,
    
    output [15:0] serial_real_out, serial_imag_out,
    output serial_valid,
    
    output reg valid_out,
    input [2:0] rom_addr
);

wire [15:0] y0_real, y1_real, y2_real, y3_real, y4_real, y5_real, y6_real, y7_real;
    wire [15:0] y0_imag, y1_imag, y2_imag, y3_imag, y4_imag, y5_imag, y6_imag, y7_imag;

    wire [15:0] rom_real_out;
    wire [15:0] rom_imag_out;

    // Serial-to-parallel signals
    wire [15:0] sp_real_out_0, sp_real_out_1, sp_real_out_2, sp_real_out_3;
    wire [15:0] sp_real_out_4, sp_real_out_5, sp_real_out_6, sp_real_out_7;

    wire [15:0] sp_imag_out_0, sp_imag_out_1, sp_imag_out_2, sp_imag_out_3;
    wire [15:0] sp_imag_out_4, sp_imag_out_5, sp_imag_out_6, sp_imag_out_7;

    wire sp_frame_complete;

    // ROM instance
    rom_memory_complex rom (
        .clk(clk),
        .enable(enable),
        .addr(rom_addr),
        .real_out(rom_real_out),
        .imag_out(rom_imag_out)
    );

    // Serial-to-parallel converter instance
    serial_to_parallel_complex sp_converter (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .real_in(rom_real_out),
        .imag_in(rom_imag_out),
        .real_out_0(sp_real_out_0), .imag_out_0(sp_imag_out_0),
        .real_out_1(sp_real_out_1), .imag_out_1(sp_imag_out_1),
        .real_out_2(sp_real_out_2), .imag_out_2(sp_imag_out_2),
        .real_out_3(sp_real_out_3), .imag_out_3(sp_imag_out_3),
        .real_out_4(sp_real_out_4), .imag_out_4(sp_imag_out_4),
        .real_out_5(sp_real_out_5), .imag_out_5(sp_imag_out_5),
        .real_out_6(sp_real_out_6), .imag_out_6(sp_imag_out_6),
        .real_out_7(sp_real_out_7), .imag_out_7(sp_imag_out_7),
        .valid(), // unused
        .frame_complete(sp_frame_complete)
    );

    // FFT core instance
    fft_core_file fft_core (
        .x0_real(sp_real_out_0), .x1_real(sp_real_out_1),
        .x2_real(sp_real_out_2), .x3_real(sp_real_out_3),
        .x4_real(sp_real_out_4), .x5_real(sp_real_out_5),
        .x6_real(sp_real_out_6), .x7_real(sp_real_out_7),
        .x0_imag(sp_imag_out_0), .x1_imag(sp_imag_out_1),
        .x2_imag(sp_imag_out_2), .x3_imag(sp_imag_out_3),
        .x4_imag(sp_imag_out_4), .x5_imag(sp_imag_out_5),
        .x6_imag(sp_imag_out_6), .x7_imag(sp_imag_out_7),
        .y0_real(y0_real), .y1_real(y1_real), 
        .y2_real(y2_real), .y3_real(y3_real),
        .y4_real(y4_real), .y5_real(y5_real), 
        .y6_real(y6_real), .y7_real(y7_real),
        .y0_imag(y0_imag), .y1_imag(y1_imag), 
        .y2_imag(y2_imag), .y3_imag(y3_imag),
        .y4_imag(y4_imag), .y5_imag(y5_imag), 
        .y6_imag(y6_imag), .y7_imag(y7_imag)
    );
    
    // Parallel-to-serial converter instance
    parallel_to_serial_complex ps_converter (
        .clk(clk),
        .reset(reset),
        .enable(valid_out),  // Trigger when FFT output is valid
        // Connect FFT outputs
        .y0_real(y0_real), .y0_imag(y0_imag),
        .y1_real(y1_real), .y1_imag(y1_imag),
        .y2_real(y2_real), .y2_imag(y2_imag),
        .y3_real(y3_real), .y3_imag(y3_imag),
        .y4_real(y4_real), .y4_imag(y4_imag),
        .y5_real(y5_real), .y5_imag(y5_imag),
        .y6_real(y6_real), .y6_imag(y6_imag),
        .y7_real(y7_real), .y7_imag(y7_imag),
        // Serial outputs
        .serial_real_out(serial_real_out),
        .serial_imag_out(serial_imag_out),
        .serial_valid(serial_valid),
        .frame_complete()  // Optional: Connect if needed
    );
    
    reg [3:0] valid_counter;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            valid_out <= 0;
            valid_counter <= 0;
        end 
        else if (sp_frame_complete) begin
            valid_out <= 1;
            valid_counter <= 4'd8;
        end 
        else if (valid_counter > 0) begin
            valid_counter <= valid_counter - 1;
        end 
        else begin
            valid_out <= 0;
        end
    end


endmodule



module rom_memory_complex (
    input clk,
    input enable,
    input [2:0] addr,
    output reg [15:0] real_out,
    output reg [15:0] imag_out
);

    // Separate ROMs for real and imaginary parts
    reg [15:0] real_rom [0:7];
    reg [15:0] imag_rom [0:7];

     always @(*) begin
     case(addr)
             //  real and imaginary values in Q8.8 format
         3'b000 :  real_rom[0] = 16'h0C80;  // x[0] real
         3'b001 :  real_rom[1] = 16'hFAB0;  // x[4] real
         3'b010 :  real_rom[2] = 16'h07C0;  // x[2] real
         3'b011 :  real_rom[3] = 16'hFC80;  // x[6] real
         3'b100 :  real_rom[4] = 16'h0100;  // x[1] real
         3'b101 :  real_rom[5] = 16'hF480;  // x[5] real
         3'b110 :  real_rom[6] = 16'h0820;  // x[3] real
         3'b111 :  real_rom[7] = 16'hFD40;  // x[7] real
             endcase
     case(addr)
             3'b000 : imag_rom[0] = 16'hF720;  // x[0] imag
             3'b001  : imag_rom[1] = 16'h0A00;  // x[4] imag
             3'b010  : imag_rom[2] = 16'h0480;  // x[2] imag
             3'b011  : imag_rom[3] = 16'hFA00;  // x[6] imag
             3'b100 :  imag_rom[4] = 16'h0240;  // x[1] imag
             3'b101 : imag_rom[5] = 16'h0680;  // x[5] imag
             3'b110 : imag_rom[6] = 16'hF6C0;  // x[3] imag
             3'b111 : imag_rom[7] = 16'hFE80;  // x[7] imag
             endcase
         end
    always @(posedge clk) begin
        if (enable) begin
            real_out <= real_rom[addr];
            imag_out <= imag_rom[addr];
        end
    end

endmodule


module serial_to_parallel_complex (
    input clk,
    input reset,
    input enable,
    input [15:0] real_in,
    input [15:0] imag_in,
    output reg [15:0] real_out_0, output reg [15:0] imag_out_0,
    output reg [15:0] real_out_1, output reg [15:0] imag_out_1,
    output reg [15:0] real_out_2, output reg [15:0] imag_out_2,
    output reg [15:0] real_out_3, output reg [15:0] imag_out_3,
    output reg [15:0] real_out_4, output reg [15:0] imag_out_4,
    output reg [15:0] real_out_5, output reg [15:0] imag_out_5,
    output reg [15:0] real_out_6, output reg [15:0] imag_out_6,
    output reg [15:0] real_out_7, output reg [15:0] imag_out_7,
    output reg valid,
    output reg frame_complete
);

    reg [2:0] counter;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter <= 0;
            valid <= 0;
            frame_complete <= 0;
            {real_out_0, imag_out_0} <= 0;
            {real_out_1, imag_out_1} <= 0;
            {real_out_2, imag_out_2} <= 0;
            {real_out_3, imag_out_3} <= 0;
            {real_out_4, imag_out_4} <= 0;
            {real_out_5, imag_out_5} <= 0;
            {real_out_6, imag_out_6} <= 0;
            {real_out_7, imag_out_7} <= 0;
        end else if (enable) begin
            valid <= 0;
            frame_complete <= 0;
            case (counter)
                3'd0: begin real_out_0 <= real_in; imag_out_0 <= imag_in; end
                3'd1: begin real_out_1 <= real_in; imag_out_1 <= imag_in; end
                3'd2: begin real_out_2 <= real_in; imag_out_2 <= imag_in; end
                3'd3: begin real_out_3 <= real_in; imag_out_3 <= imag_in; end
                3'd4: begin real_out_4 <= real_in; imag_out_4 <= imag_in; end
                3'd5: begin real_out_5 <= real_in; imag_out_5 <= imag_in; end
                3'd6: begin real_out_6 <= real_in; imag_out_6 <= imag_in; end
                3'd7: begin
                    real_out_7 <= real_in;
                    imag_out_7 <= imag_in;
                    valid <= 1;
                    frame_complete <= 1;
                end
            endcase
            counter <= (counter == 3'd7) ? 0 : counter + 1;
        end else begin
            valid <= 0;
            frame_complete <= 0;
        end
    end

endmodule


module fft_core_file (
    input [15:0] x0_real, x1_real, x2_real, x3_real, x4_real, x5_real, x6_real, x7_real,
    input [15:0] x0_imag, x1_imag, x2_imag, x3_imag, x4_imag, x5_imag, x6_imag, x7_imag,
    output [15:0] y0_real, y1_real, y2_real, y3_real, y4_real, y5_real, y6_real, y7_real,
    output [15:0] y0_imag, y1_imag, y2_imag, y3_imag, y4_imag, y5_imag, y6_imag, y7_imag);

    localparam [15:0] W8_0r = 16'h0100; // 1.0
    localparam [15:0] W8_0i = 16'h0000; // 0.0
    localparam [15:0] W8_1r = 16'h00B5; // 0.7071 
    localparam [15:0] W8_1i = 16'hFF4B; // -0.7071 
    localparam [15:0] W8_2r = 16'h0000; // 0.0
    localparam [15:0] W8_2i = 16'hFF00; // -1.0 (-j)
    localparam [15:0] W8_3r = 16'hFF4B; // -0.7071 
    localparam [15:0] W8_3i = 16'hFF4B; // -0.7071 

   // ========== Stage 1:
    wire [15:0] s1_0r, s1_0i, s1_1r, s1_1i, s1_2r, s1_2i, s1_3r, s1_3i;
    wire [15:0] s1_4r, s1_4i, s1_5r, s1_5i, s1_6r, s1_6i, s1_7r, s1_7i;

    butterfly_1 bf1_0 (
        .a_real(x0_real), .a_imag(x0_imag),
        .b_real(x1_real), .b_imag(x1_imag),
        .sum_real(s1_0r), .sum_imag(s1_0i),
        .diff_real(s1_4r), .diff_imag(s1_4i));
    
    butterfly_1 bf1_1 (
        .a_real(x2_real), .a_imag(x2_imag),
        .b_real(x3_real), .b_imag(x3_imag),
        .sum_real(s1_1r), .sum_imag(s1_1i),
        .diff_real(s1_5r), .diff_imag(s1_5i));
    
    butterfly_1 bf1_2 (
        .a_real(x4_real), .a_imag(x4_imag),
        .b_real(x5_real), .b_imag(x5_imag),
        .sum_real(s1_2r), .sum_imag(s1_2i),
        .diff_real(s1_6r), .diff_imag(s1_6i) );
    
    butterfly_1 bf1_3 (
        .a_real(x6_real), .a_imag(x6_imag),
        .b_real(x7_real), .b_imag(x7_imag),
        .sum_real(s1_3r), .sum_imag(s1_3i),
        .diff_real(s1_7r), .diff_imag(s1_7i));

    // ========== Stage 2: Radix-2 
    wire [15:0] s2_0r, s2_0i, s2_1r, s2_1i, s2_2r, s2_2i, s2_3r, s2_3i;
    wire [15:0] s2_4r, s2_4i, s2_5r, s2_5i, s2_6r, s2_6i, s2_7r, s2_7i;

    // Butterfly 2.0: No twiddle (W8^0 = 1)
       wire [15:0] m = (~s1_5i) + 1'b1;   //16'hFA80; 
       wire [15:0] n=   (~s1_5r) + 1'b1;  //16'h0D10;               
        wire [15:0] p= (~s1_7i) + 1'b1;
        wire [23:8] q= (~s1_7r) + 1'b1;
    butterfly_2 bf2_0 (
        .a_real(s1_0r), .a_imag(s1_0i),
        .b_real(s1_4r), .b_imag(s1_4i),
        .c_real(s1_1r), .c_imag(s1_1i),
         .d_real(m), .d_imag(n),
        .sum_real1(s2_0r), .sum_imag1(s2_0i),
        .diff_real1(s2_1r), .diff_imag1(s2_1i),
        .sum_real2(s2_4r), .sum_imag2(s2_4i),
        .diff_real2(s2_5r), .diff_imag2(s2_5i));

   butterfly_2 bf2_1 (
        .a_real(s1_2r), .a_imag(s1_2i),
        .b_real(s1_6r), .b_imag(s1_6i),
        .c_real(s1_3r), .c_imag(s1_3i),
         .d_real(p), .d_imag(q),
        .sum_real1(s2_2r), .sum_imag1(s2_2i),
        .diff_real1(s2_3r), .diff_imag1(s2_3i),
        .sum_real2(s2_6r), .sum_imag2(s2_6i),
        .diff_real2(s2_7r), .diff_imag2(s2_7i));


    // ========== Stage 3: Final Butterflies and Complex Multipliers ==========
    wire [15:0] c,d,g,h;
        wire [15:0] mk = (~h)+1'b1;
        wire [15:0] pk =(~d)+1'b1;
        wire [15:0] e=(~s2_3i)+1'b1;
         wire [15:0] f=(~s2_3r)+1'b1;
      
      complex_multiplier_1 cm_0(.am(s2_6r),.bm(s2_6i),.cm(c),.dm(d));
      complex_multiplier_2 cm_1(.an(s2_7r),.bn(s2_7i),.gm(g),.hm(h));
    butterfly_3 bf3_0 (
            .a_real(s2_0r), .a_imag(s2_0i),
            .b_real(s2_4r), .b_imag(s2_4i),
            .c_real(s2_1r), .c_imag(s2_1i),
             .d_real(s2_5r), .d_imag(s2_5i),
             .e_real(s2_2r), .e_imag(s2_2i),
              .f_real(c), .f_imag(pk),
               .g_real(e), .g_imag(f),
              .h_real(g), .h_imag(mk),
            .sum_real1(y0_real), .sum_imag1(y0_imag),
            .sum_real2(y1_real), .sum_imag2(y1_imag),
            .sum_real3(y2_real), .sum_imag3(y2_imag),
            .sum_real4(y3_real), .sum_imag4(y3_imag),
            .diff_real1(y4_real), .diff_imag1(y4_imag),
            .diff_real2(y5_real), .diff_imag2(y5_imag),
            .diff_real3(y6_real), .diff_imag3(y6_imag),
             .diff_real4(y7_real), .diff_imag4(y7_imag));
            

endmodule

module butterfly_1 (
    input [15:0] a_real, a_imag, // a real and imaginary
    input [15:0] b_real, b_imag, // b real and imaginary
    output [15:0] sum_real, sum_imag, // a + b
    output [15:0] diff_real, diff_imag // a - b
);

         assign   sum_real = a_real + b_real;
          assign  sum_imag = a_imag + b_imag;
          assign  diff_real = a_real - b_real;
          assign  diff_imag = a_imag - b_imag;

endmodule

module butterfly_2 (
    input [15:0] a_real, a_imag, // a real and imaginary
    input [15:0] b_real, b_imag, // b real and imaginary
    input [15:0] c_real, c_imag, // c real and imaginary
        input [15:0] d_real, d_imag, // d real and imaginary
           output [15:0] sum_real1, sum_imag1, // a+c
         output [15:0] diff_real1, diff_imag1, // a-c
          output [15:0] sum_real2, sum_imag2, // b+d
         output [15:0] diff_real2, diff_imag2 // b-d
);

         assign   sum_real1 = a_real + c_real;
         assign   sum_imag1 = a_imag + c_imag;
         assign   sum_real2 = b_real + d_real;
          assign   sum_imag2 = b_imag + d_imag;
          assign  diff_real1 = a_real - c_real;
          assign  diff_imag1 = a_imag - c_imag;
           assign  diff_real2 = b_real - d_real;
           assign  diff_imag2 = b_imag - d_imag;

endmodule

module butterfly_3 (
    input [15:0] a_real, a_imag, // a real and imaginary
    input [15:0] b_real, b_imag, // b real and imaginary
    input [15:0] c_real, c_imag, // c real and imaginary
     input [15:0] d_real, d_imag, // d real and imaginary
       input [15:0] e_real, e_imag, // e real and imaginary
       input [15:0] f_real, f_imag, // f real and imaginary
        input [15:0] g_real, g_imag, // g real and imaginary
        input [15:0] h_real, h_imag, // h real and imaginary
           output [15:0] sum_real1, sum_imag1, // a+e
          output [15:0] sum_real2, sum_imag2, // b+f
          output [15:0] sum_real3, sum_imag3, // c+g
          output [15:0] sum_real4, sum_imag4, // d+h
          output [15:0] diff_real1, diff_imag1, // a-e
         output [15:0] diff_real2, diff_imag2, // b-f
         output [15:0] diff_real3, diff_imag3, // c-g
         output [15:0] diff_real4, diff_imag4 // d-h
);

         assign   sum_real1 = a_real + e_real;
         assign   sum_imag1 = a_imag + e_imag;
         assign   sum_real2 = b_real + f_real;
          assign   sum_imag2 = b_imag + f_imag;
          assign   sum_real3 = c_real + g_real;
          assign   sum_imag3 = c_imag + g_imag;
          assign   sum_real4 = d_real + h_real;
           assign   sum_imag4 = d_imag + h_imag;
          assign  diff_real1 = a_real - e_real;
          assign  diff_imag1 = a_imag - e_imag;
           assign  diff_real2 = b_real - f_real;
           assign  diff_imag2 = b_imag - f_imag;
           assign  diff_real3 = c_real - g_real;
                     assign  diff_imag3 = c_imag - g_imag;
                      assign  diff_real4 = d_real - h_real;
                      assign  diff_imag4 = d_imag - h_imag;

endmodule

module complex_multiplier_1 (
    input  signed [15:0] am, // Real part
    input  signed [15:0] bm, // Imag part
    output signed [15:0] cm, // Output real
    output signed [15:0] dm  // Output imag
);

    // Q8.8 representation of 0.7071 ? 16'h00B5
    parameter signed [15:0] K1 = 16'h00B5;
    parameter signed [15:0] K2 = 16'hFF4B;

    wire signed [15:0] add_ambm;
    wire signed [15:0] sub_ambm;
    wire signed [31:0] mult_re, mult_im;

    assign add_ambm = am + bm;
    assign sub_ambm = am - bm;

    assign mult_re = add_ambm * K1; // 0.7071(a + b)
    assign mult_im = sub_ambm * K2; // 0.7071(a - b)

    assign cm = mult_re[23:8];   // Q8.8: Take middle 16 bits after Q8.8 x Q8.8
    assign dm = -mult_im[23:8];  // Negated for -j

endmodule
module complex_multiplier_2 (
    input  signed [15:0] an, // Real part
    input  signed [15:0] bn, // Imag part
    output signed [15:0] gm, // Output real
    output signed [15:0] hm  // Output imag
);

    parameter signed [15:0] K1 = 16'hFF4B; //-0.7071

    wire signed [15:0] add_anbn;
    wire signed [15:0] sub_anbn;
    wire signed [31:0] mult_re, mult_im;

    assign add_anbn = an + bn;
    assign sub_anbn = an - bn;

    assign mult_re = sub_anbn * K1; // -0.7071(a - b)
    assign mult_im = add_anbn * K1; // -0.7071(a + b)

    assign gm = mult_re[23:8];   // Q8.8: Take middle 16 bits after Q8.8 x Q8.8
    assign hm = -mult_im[23:8];  // Negated for -j

endmodule

module parallel_to_serial_complex ( 
    input clk,
    input reset,
    input enable,         // Must stay high for 8 cycles
    // Parallel inputs (FFT outputs)
    input [15:0] y0_real, y1_real, y2_real, y3_real, 
    input [15:0] y4_real, y5_real, y6_real, y7_real,
    input [15:0] y0_imag, y1_imag, y2_imag, y3_imag, 
    input [15:0] y4_imag, y5_imag, y6_imag, y7_imag,
    // Serial outputs
    output reg [15:0] serial_real_out,
    output reg [15:0] serial_imag_out,
    output reg serial_valid,
    output reg frame_complete
);

    reg [2:0] counter;  // 3-bit counter (0-7)
    reg frame_complete_delay; // Delayed version of frame_complete

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter <= 0;
            serial_real_out <= 0;
            serial_imag_out <= 0;
            serial_valid <= 0;
            frame_complete <= 0;
            frame_complete_delay <= 0;
        end 
        else if (enable) begin
            // Shift out data sequentially
            case (counter)
                3'd0: begin 
                    serial_real_out <= y0_real; 
                    serial_imag_out <= y0_imag; 
                end
                3'd1: begin 
                    serial_real_out <= y1_real; 
                    serial_imag_out <= y1_imag; 
                end
                3'd2: begin 
                    serial_real_out <= y2_real; 
                    serial_imag_out <= y2_imag; 
                end
                3'd3: begin 
                    serial_real_out <= y3_real; 
                    serial_imag_out <= y3_imag; 
                end
                3'd4: begin 
                    serial_real_out <= y4_real; 
                    serial_imag_out <= y4_imag; 
                end
                3'd5: begin 
                    serial_real_out <= y5_real; 
                    serial_imag_out <= y5_imag; 
                end
                3'd6: begin 
                    serial_real_out <= y6_real; 
                    serial_imag_out <= y6_imag; 
                end
                3'd7: begin 
                    serial_real_out <= y7_real; 
                    serial_imag_out <= y7_imag; 
                end
            endcase

            serial_valid <= 1;  // Data is valid
            counter <= counter + 1;

            // Assert frame_complete_delay at the last sample
            frame_complete_delay <= (counter == 3'd7);
        end 
        else begin
            // When enable=0, reset counter and flags
            counter <= 0;
            serial_valid <= 0;
            frame_complete_delay <= 0;
        end

        // frame_complete pulses one cycle after the last sample
        frame_complete <= frame_complete_delay;
    end
endmodule
