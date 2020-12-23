%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0105+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rPf8LAixxC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:45 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  221 ( 231 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( A @ B ) )
        = ( k5_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
 != ( k5_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
 != ( k5_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('3',plain,(
    ! [X118: $i,X119: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X118 @ X119 ) @ X118 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('4',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf('8',plain,(
    ! [X211: $i,X212: $i,X213: $i] :
      ( ( k3_xboole_0 @ ( X211 @ ( k4_xboole_0 @ ( X212 @ X213 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X211 @ X212 ) @ X213 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X96: $i,X97: $i] :
      ( ( k5_xboole_0 @ ( X96 @ X97 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( X96 @ X97 ) @ ( k3_xboole_0 @ ( X96 @ X97 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) @ o_0_0_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('12',plain,(
    ! [X185: $i,X186: $i] :
      ( ( k2_xboole_0 @ ( X185 @ ( k4_xboole_0 @ ( X186 @ X185 ) ) ) )
      = ( k2_xboole_0 @ ( X185 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('13',plain,(
    ! [X187: $i] :
      ( ( k4_xboole_0 @ ( X187 @ k1_xboole_0 ) )
      = X187 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X187: $i] :
      ( ( k4_xboole_0 @ ( X187 @ o_0_0_xboole_0 ) )
      = X187 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
 != ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['2','16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
