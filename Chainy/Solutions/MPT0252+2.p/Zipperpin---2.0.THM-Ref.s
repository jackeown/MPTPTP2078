%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0252+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pRqdnASVYo

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   53 (  56 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  289 ( 312 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_10_type,type,(
    sk_C_10: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ ( A @ B ) @ C ) @ C ) )
     => ( r2_hidden @ ( A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ ( A @ B ) @ C ) @ C ) )
       => ( r2_hidden @ ( A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('1',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('2',plain,(
    ! [X359: $i,X360: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X359 @ X360 ) @ X360 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) @ sk_C_10 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( sk_C_10 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) @ sk_C_10 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,
    ( ~ ( r1_tarski @ ( sk_C_10 @ ( k2_xboole_0 @ ( sk_C_10 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) ) )
    | ( sk_C_10
      = ( k2_xboole_0 @ ( sk_C_10 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X363: $i,X364: $i] :
      ( r1_tarski @ ( X363 @ ( k2_xboole_0 @ ( X363 @ X364 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,
    ( sk_C_10
    = ( k2_xboole_0 @ ( sk_C_10 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ ( A @ B ) )
              & ( r1_xboole_0 @ ( A @ C ) ) )
          & ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('10',plain,(
    ! [X331: $i,X332: $i,X334: $i] :
      ( ( r1_xboole_0 @ ( X331 @ X334 ) )
      | ~ ( r1_xboole_0 @ ( X331 @ ( k2_xboole_0 @ ( X332 @ X334 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( X0 @ sk_C_10 ) )
      | ( r1_xboole_0 @ ( X0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X0 @ sk_C_10 ) @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ ( B @ A ) )
          & ( r1_xboole_0 @ ( B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X326: $i,X327: $i] :
      ( ~ ( r1_xboole_0 @ ( X326 @ X327 ) )
      | ~ ( r1_tarski @ ( X326 @ X327 ) )
      | ( v1_xboole_0 @ X326 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ ( X0 @ sk_C_10 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( X0 @ sk_C_10 ) @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('20',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ C ) )
    <=> ( ( r2_hidden @ ( A @ C ) )
        & ( r2_hidden @ ( B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X1105: $i,X1106: $i,X1107: $i] :
      ( ( r2_hidden @ ( X1105 @ X1106 ) )
      | ~ ( r1_tarski @ ( k2_tarski @ ( X1105 @ X1107 ) @ X1106 ) ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('26',plain,(
    r2_hidden @ ( sk_A_2 @ sk_C_10 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
