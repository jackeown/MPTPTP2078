%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0359+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MxRwX1XAPS

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 6.35s
% Output     : Refutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 298 expanded)
%              Number of leaves         :   32 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  758 (2125 expanded)
%              Number of equality atoms :  111 ( 283 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ ( A @ B ) @ B ) )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ ( A @ B ) @ B ) )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ ( k3_subset_1 @ ( A @ B ) ) ) )
        = B ) ) )).

thf('1',plain,(
    ! [X1508: $i,X1509: $i] :
      ( ( ( k3_subset_1 @ ( X1509 @ ( k3_subset_1 @ ( X1509 @ X1508 ) ) ) )
        = X1508 )
      | ~ ( m1_subset_1 @ ( X1508 @ ( k1_zfmisc_1 @ X1509 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) )
    = sk_B_8 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k4_xboole_0 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( sk_B_8
      = ( k2_subset_1 @ sk_A_2 ) )
    | ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(split,[status(esa)],['8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('10',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( ( k6_subset_1 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) )
      = o_0_0_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('16',plain,(
    ! [X359: $i,X360: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X359 @ X360 ) @ X360 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('17',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X359: $i,X360: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ ( X359 @ X360 ) @ X360 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ ( X1 @ X0 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X104: $i,X105: $i] :
      ( ( k4_xboole_0 @ ( X104 @ X105 ) )
      = ( k5_xboole_0 @ ( X104 @ ( k3_xboole_0 @ ( X104 @ X105 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X104: $i,X105: $i] :
      ( ( k6_subset_1 @ ( X104 @ X105 ) )
      = ( k5_xboole_0 @ ( X104 @ ( k3_xboole_0 @ ( X104 @ X105 ) ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( X0 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('29',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ k1_xboole_0 ) )
      = X302 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ o_0_0_xboole_0 ) )
      = X302 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( X0 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( X0 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( X1 @ X0 ) @ X0 ) )
      = ( k6_subset_1 @ ( X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
      = o_0_0_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(demod,[status(thm)],['14','15','34'])).

thf('36',plain,
    ( ( sk_B_8
      = ( k2_subset_1 @ sk_A_2 ) )
    | ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('37',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,
    ( ( sk_B_8 = sk_A_2 )
    | ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_8 = sk_A_2 )
   <= ( sk_B_8 = sk_A_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('41',plain,
    ( ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) )
   <= ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( sk_B_8 != sk_A_2 )
   <= ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( sk_A_2 != sk_A_2 )
   <= ( ( sk_B_8
       != ( k2_subset_1 @ sk_A_2 ) )
      & ( sk_B_8 = sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( ( sk_B_8 != sk_A_2 )
    | ( sk_B_8
      = ( k2_subset_1 @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('48',plain,
    ( ( sk_B_8 != sk_A_2 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B_8 != sk_A_2 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(split,[status(esa)],['48'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('51',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('52',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ X0 ) )
      = ( k6_subset_1 @ ( X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('55',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('61',plain,
    ( ( sk_B_8
      = ( k2_subset_1 @ sk_A_2 ) )
   <= ( sk_B_8
      = ( k2_subset_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('62',plain,
    ( ( sk_B_8 = sk_A_2 )
   <= ( sk_B_8
      = ( k2_subset_1 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('64',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_A_2 ) )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) )
      & ( sk_B_8
        = ( k2_subset_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B_8 = sk_A_2 )
   <= ( sk_B_8
      = ( k2_subset_1 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('66',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_A_2 ) @ sk_A_2 ) )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) )
      & ( sk_B_8
        = ( k2_subset_1 @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( o_0_0_xboole_0 @ sk_A_2 ) )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) )
      & ( sk_B_8
        = ( k2_subset_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('68',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('70',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) )
    | ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) )
    | ( sk_B_8 = sk_A_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('73',plain,(
    r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ),
    inference('sat_resolution*',[status(thm)],['45','49','71','72'])).

thf('74',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','73'])).

thf('75',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','74'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ ( A @ ( k1_subset_1 @ A ) ) ) ) )).

thf('76',plain,(
    ! [X1550: $i] :
      ( ( k2_subset_1 @ X1550 )
      = ( k3_subset_1 @ ( X1550 @ ( k1_subset_1 @ X1550 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('77',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('78',plain,(
    ! [X1472: $i] :
      ( ( k1_subset_1 @ X1472 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('79',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('80',plain,(
    ! [X1472: $i] :
      ( ( k1_subset_1 @ X1472 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1550: $i] :
      ( X1550
      = ( k3_subset_1 @ ( X1550 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','80'])).

thf('82',plain,(
    sk_A_2 = sk_B_8 ),
    inference(demod,[status(thm)],['2','75','81'])).

thf('83',plain,
    ( ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) )
   <= ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('84',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('85',plain,
    ( ( sk_B_8 != sk_A_2 )
   <= ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_B_8 = sk_A_2 )
   <= ( sk_B_8
      = ( k2_subset_1 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('87',plain,
    ( ( sk_B_8 != sk_A_2 )
   <= ( sk_B_8 != sk_A_2 ) ),
    inference(split,[status(esa)],['48'])).

thf('88',plain,
    ( ( sk_A_2 != sk_A_2 )
   <= ( ( sk_B_8 != sk_A_2 )
      & ( sk_B_8
        = ( k2_subset_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_B_8
     != ( k2_subset_1 @ sk_A_2 ) )
    | ( sk_B_8 = sk_A_2 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_B_8
 != ( k2_subset_1 @ sk_A_2 ) ),
    inference('sat_resolution*',[status(thm)],['45','49','71','89'])).

thf('91',plain,(
    sk_B_8 != sk_A_2 ),
    inference(simpl_trail,[status(thm)],['85','90'])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','91'])).

%------------------------------------------------------------------------------
