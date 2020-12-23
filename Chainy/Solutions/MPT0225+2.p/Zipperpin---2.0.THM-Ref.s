%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0225+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cg1H1YYp1s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 102 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  357 ( 870 expanded)
%              Number of equality atoms :   58 ( 147 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ ( A @ B ) ) ) )).

thf('0',plain,(
    ! [X987: $i,X989: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X987 @ X989 ) )
        = ( k1_tarski @ X987 ) )
      | ( r2_hidden @ ( X987 @ X989 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('1',plain,
    ( ( sk_A_2 = sk_B_2 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != ( k1_tarski @ sk_A_2 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_A_2 != sk_B_2 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A_2 != sk_B_2 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A_2 = sk_B_2 )
   <= ( sk_A_2 = sk_B_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k1_tarski @ sk_A_2 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k1_tarski @ sk_A_2 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
        = ( k1_tarski @ sk_A_2 ) )
      & ( sk_A_2 = sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A_2 = sk_B_2 )
   <= ( sk_A_2 = sk_B_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = ( k1_tarski @ sk_B_2 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
        = ( k1_tarski @ sk_A_2 ) )
      & ( sk_A_2 = sk_B_2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X240: $i,X241: $i] :
      ( ( X240 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X240 @ ( k4_xboole_0 @ ( X241 @ X240 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ! [X240: $i,X241: $i] :
      ( ( X240 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X240 @ ( k4_xboole_0 @ ( X241 @ X240 ) ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_B_2 @ ( k1_tarski @ sk_B_2 ) ) )
      | ( ( k1_tarski @ sk_B_2 )
        = o_0_0_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
        = ( k1_tarski @ sk_A_2 ) )
      & ( sk_A_2 = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B_2 )
      = o_0_0_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
        = ( k1_tarski @ sk_A_2 ) )
      & ( sk_A_2 = sk_B_2 ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X972: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X972 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
        = ( k1_tarski @ sk_A_2 ) )
      & ( sk_A_2 = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != ( k1_tarski @ sk_A_2 ) )
    | ( sk_A_2 != sk_B_2 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != ( k1_tarski @ sk_A_2 ) )
    | ( sk_A_2 = sk_B_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('22',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
 != ( k1_tarski @ sk_A_2 ) ),
    inference('sat_resolution*',[status(thm)],['4','20','21'])).

thf('23',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
 != ( k1_tarski @ sk_A_2 ) ),
    inference(simpl_trail,[status(thm)],['2','22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_A_2 )
     != ( k1_tarski @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('26',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A_2 = sk_B_2 ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_A_2 != sk_B_2 )
   <= ( sk_A_2 != sk_B_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    sk_A_2 != sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['4','20'])).

thf('31',plain,(
    sk_A_2 != sk_B_2 ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','31'])).

%------------------------------------------------------------------------------
