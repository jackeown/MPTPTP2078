%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0055+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YJfOjuPDwT

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 2.47s
% Output     : Refutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   61 (  66 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  408 ( 452 expanded)
%              Number of equality atoms :   39 (  43 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t48_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
        = ( k3_xboole_0 @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k3_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X197: $i,X198: $i] :
      ( ( k4_xboole_0 @ ( X197 @ ( k3_xboole_0 @ ( X197 @ X198 ) ) ) )
      = ( k4_xboole_0 @ ( X197 @ X198 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('4',plain,(
    ! [X175: $i,X176: $i] :
      ( ( k2_xboole_0 @ ( X175 @ ( k4_xboole_0 @ ( X176 @ X175 ) ) ) )
      = ( k2_xboole_0 @ ( X175 @ X176 ) ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X179: $i,X180: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X179 @ X180 ) @ X180 ) )
      = ( k4_xboole_0 @ ( X179 @ X180 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ ( X1 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( C @ A ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( X58 @ X59 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( X59 @ X58 ) @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( X58 @ X59 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( X59 @ X58 ) @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ~ ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( X33 @ X32 ) )
      | ~ ( r2_hidden @ ( X33 @ X31 ) )
      | ( X32
       != ( k4_xboole_0 @ ( X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( X33 @ X31 ) )
      | ~ ( r2_hidden @ ( X33 @ ( k4_xboole_0 @ ( X30 @ X31 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ ( X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ ( X2 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ ( X1 @ X0 ) @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ ( X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('14',plain,(
    ! [X77: $i] :
      ( ( X77 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X62: $i,X64: $i,X65: $i] :
      ( ~ ( r2_hidden @ ( X64 @ ( k3_xboole_0 @ ( X62 @ X65 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X62 @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( X1 @ X0 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X197: $i,X198: $i] :
      ( ( k4_xboole_0 @ ( X197 @ ( k3_xboole_0 @ ( X197 @ X198 ) ) ) )
      = ( k4_xboole_0 @ ( X197 @ X198 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) )
      = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('24',plain,(
    ! [X177: $i] :
      ( ( k4_xboole_0 @ ( X177 @ k1_xboole_0 ) )
      = X177 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    ! [X177: $i] :
      ( ( k4_xboole_0 @ ( X177 @ o_0_0_xboole_0 ) )
      = X177 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','28'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('31',plain,(
    ! [X125: $i,X126: $i] :
      ( ( k2_xboole_0 @ ( X125 @ ( k3_xboole_0 @ ( X125 @ X126 ) ) ) )
      = X125 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X1 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ( k3_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
 != ( k3_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['2','32','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
