// Reference functions that use Bluespec's '*' operator
function Bit#(TAdd#(n,n)) multiply_unsigned( Bit#(n) a, Bit#(n) b );
    UInt#(n) a_uint = unpack(a);
    UInt#(n) b_uint = unpack(b);
    UInt#(TAdd#(n,n)) product_uint = zeroExtend(a_uint) * zeroExtend(b_uint);
    return pack( product_uint );
endfunction

function Bit#(TAdd#(n,n)) multiply_signed( Bit#(n) a, Bit#(n) b );
    Int#(n) a_int = unpack(a);
    Int#(n) b_int = unpack(b);
    Int#(TAdd#(n,n)) product_int = signExtend(a_int) * signExtend(b_int);
    return pack( product_int );
endfunction

// Exercise 2
// Multiplication by repeated addition
function Bit#(TAdd#(n,n)) multiply_by_adding( Bit#(n) a, Bit#(n) b );
    UInt#(n) a_int = unpack(a);
    UInt#(n) b_int = unpack(b);
    UInt#(TAdd#(n, n)) product = 0;
    UInt#(TAdd#(n, n)) temp_a = zeroExtend(a_int);
    for (Integer i = 0; i < valueOf(n); i = i + 1) begin
        product = product + (b[i] == 0 ? 0 : (temp_a << i));
    end
    return pack( product );
endfunction

// Multiplier Interface
interface Multiplier#( numeric type n );
    method Bool start_ready();
    method Action start( Bit#(n) a, Bit#(n) b );
    method Bool result_ready();
    method ActionValue#(Bit#(TAdd#(n,n))) result();
endinterface


// Exercise 4
// Folded multiplier by repeated addition
module mkFoldedMultiplier( Multiplier#(n) );

    Reg#(UInt#(TAdd#(n, n))) a_reg <- mkReg(0);
    Reg#(Bit#(n)) b_reg <- mkReg(0);
    Reg#(UInt#(TAdd#(n, n))) product <- mkReg(0);
    Reg#(Bool) busy <- mkReg(False);
    Reg#(Bit#(TAdd#(TLog#(n), 1))) i <- mkReg(0);

    rule mul_step(/** guard **/ i < fromInteger(valueOf(n)));
        product <= product + ((b_reg[i]) == 0 ? 0 : (a_reg << i));
        $display("i: %0d, product: %0d", i, product);
        i <= i + 1;
    endrule

    method Action start( Bit#(n) a, Bit#(n) b );
        UInt#(n) a1 = unpack(a);
        a_reg <= zeroExtend(a1);
        b_reg <= b;
        busy <= True;
        product <= 0;
        i <= 0;
    endmethod

    method Bool result_ready();
        return i == fromInteger(valueOf(n));
    endmethod

    method Bool start_ready();
        return !busy;
    endmethod

    method ActionValue#(Bit#(TAdd#(n,n))) result();
        busy <= False;
        return pack( product );
    endmethod

endmodule

// Exercise 6
// Booth Multiplier
module mkBoothMultiplier( Multiplier#(n) );

    Reg#(Bit#(TAdd#(TAdd#(n, n), 1))) m_pos <- mkReg(0);
    Reg#(Bit#(TAdd#(TAdd#(n, n), 1))) m_neg <- mkReg(0);
    Reg#(Bit#(TAdd#(TAdd#(n, n), 1))) p <- mkReg(0);
    Reg#(Bool) busy <- mkReg(False);
    Reg#(Bit#(TAdd#(TLog#(n), 1))) i <- mkReg(0);

    rule booth_step(i < fromInteger(valueOf(n)));
        Bit#(2) pr = p[1:0];
        let p_next = p;
        if (pr == 2'b01) begin
            p_next = p_next + m_pos;
        end
        if (pr == 2'b10) begin
            p_next = p_next + m_neg;
        end
        Int#(TAdd#(TAdd#(n, n), 1)) shifted = unpack(p_next) >> 1;
        p <= pack(shifted);
        i <= i + 1;
    endrule

    method Bool start_ready();
        return !busy;
    endmethod

    method Action start( Bit#(n) a, Bit#(n) b );
        busy <= True;
        i <= 0;
        m_pos <= { a, 0 };
        Int#(n) neg_a = -unpack(a);
        m_neg <= { pack(neg_a), 0 };
        p <= { 0, b, 1'b0 };
    endmethod

    method Bool result_ready();
        return i == fromInteger(valueOf(n));
    endmethod

    method ActionValue#(Bit#(TAdd#(n,n))) result();
        busy <= False;
        return truncateLSB(p);
    endmethod
endmodule

function Bit#(n) arth_shift(Bit#(n) a, Integer n, Bool right);
    Int#(n) a_int = unpack(a);
    if (right) begin
        return  pack(a_int >> n);
    end else begin
        return  pack(a_int <<n);
    end
endfunction

// Exercise 8
// Radix-4 Booth Multiplier
module mkBoothMultiplierRadix4( Multiplier#(n) );

    Reg#(Bit#(TAdd#(TAdd#(n, n), 2))) m_pos <- mkReg(0);
    Reg#(Bit#(TAdd#(TAdd#(n, n), 2))) m_neg <- mkReg(0);
    Reg#(Bit#(TAdd#(TAdd#(n, n), 2))) p <- mkReg(0);
    Reg#(Bool) busy <- mkReg(False);
    Reg#(Bit#(TAdd#(TLog#(n), 1))) i <- mkReg(0);

    rule booth_step(i < fromInteger(valueOf(n)) / 2);
        Bit#(3) pr = p[2:0];
        let p_next = p;
        case(pr)
            'b001 : p_next = p_next + m_pos;
            'b010 : p_next = p_next + m_pos;
            'b101 : p_next = p_next + m_neg;
            'b110 : p_next = p_next + m_neg;
            'b011 : p_next = p_next + arth_shift(m_pos, 1, False);
            'b100 : p_next = p_next + arth_shift(m_neg, 1, False);
        endcase

        p <= arth_shift(p_next, 2, True);
        i <= i + 1;
    endrule

    method Bool start_ready();
        return !busy;
    endmethod

    method Action start( Bit#(n) m, Bit#(n) r );
        busy <= True;
        i <= 0;
        m_pos <= { msb(m), m, 0 };
        m_neg <= { msb(-m), -m, 0 };
        p <= { 0, r, 1'b0 };
    endmethod

    method Bool result_ready();
        return i == fromInteger(valueOf(n) / 2);
    endmethod

    method ActionValue#(Bit#(TAdd#(n,n))) result();
        busy <= False;
        return p[(2*valueOf(n)):1];
    endmethod

endmodule
