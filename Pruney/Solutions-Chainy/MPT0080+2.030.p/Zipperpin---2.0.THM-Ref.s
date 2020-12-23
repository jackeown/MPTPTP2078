%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hePBddcpXA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:07 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 204 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  726 (1445 expanded)
%              Number of equality atoms :   77 ( 157 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['17','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['59','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['58','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['57','75'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','78'])).

thf('80',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hePBddcpXA
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 715 iterations in 0.240s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(t73_xboole_1, conjecture,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.45/0.69       ( r1_tarski @ A @ B ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.69        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.45/0.69            ( r1_xboole_0 @ A @ C ) ) =>
% 0.45/0.69          ( r1_tarski @ A @ B ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.45/0.69  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(l32_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (![X6 : $i, X8 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.45/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf(t41_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.69       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.45/0.69           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.45/0.69  thf(t39_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.45/0.69           = (k2_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.45/0.69           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (((k2_xboole_0 @ sk_C @ k1_xboole_0)
% 0.45/0.69         = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['3', '6'])).
% 0.45/0.69  thf(idempotence_k2_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.69  thf('8', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.45/0.69      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.69  thf(t7_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.69  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.69      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X6 : $i, X8 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.45/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.69  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.45/0.69           = (k2_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.69  thf('15', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.45/0.69      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.69  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (((sk_C) = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.69      inference('demod', [status(thm)], ['7', '16'])).
% 0.45/0.69  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X6 : $i, X8 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.45/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.69  thf(t48_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.69           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.69  thf('23', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.45/0.69           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['21', '22'])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.45/0.69           = (k2_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.69  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['24', '27'])).
% 0.45/0.69  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.45/0.69  thf('30', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.69      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['23', '30'])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['18', '31'])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.45/0.69         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.45/0.69      inference('sup+', [status(thm)], ['17', '32'])).
% 0.45/0.69  thf('34', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(d7_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.69       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      (![X2 : $i, X3 : $i]:
% 0.45/0.69         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.69  thf('36', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.69           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.45/0.69           = (k2_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.69           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('42', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.69           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.45/0.69         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['36', '42'])).
% 0.45/0.69  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.45/0.69         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['46', '47'])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X6 : $i, X8 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.45/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.69  thf('51', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.45/0.69           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.45/0.69           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['50', '51'])).
% 0.45/0.69  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.69  thf('55', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['45', '54'])).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.45/0.69           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ sk_A @ X0)
% 0.45/0.69           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.45/0.69           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.45/0.69  thf('60', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.45/0.69           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('61', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.69           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.45/0.69           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.45/0.69  thf('63', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.45/0.69           = (k4_xboole_0 @ X2 @ 
% 0.45/0.69              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['61', '62'])).
% 0.45/0.69  thf('64', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.45/0.69           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.45/0.69           = (k4_xboole_0 @ X2 @ 
% 0.45/0.69              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.45/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.45/0.69  thf('66', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.69           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['60', '65'])).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.45/0.69           = (k2_xboole_0 @ X9 @ X10))),
% 0.45/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.69  thf('68', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.69           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.45/0.69      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.69  thf('70', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.45/0.69      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.69  thf('71', plain,
% 0.45/0.69      (![X2 : $i, X4 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.69  thf('72', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.69          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['70', '71'])).
% 0.45/0.69  thf('73', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.69      inference('simplify', [status(thm)], ['72'])).
% 0.45/0.69  thf('74', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 0.45/0.69      inference('sup+', [status(thm)], ['59', '73'])).
% 0.45/0.69  thf('75', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 0.45/0.69      inference('sup+', [status(thm)], ['58', '74'])).
% 0.45/0.69  thf('76', plain,
% 0.45/0.69      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.45/0.69      inference('sup+', [status(thm)], ['57', '75'])).
% 0.45/0.69  thf('77', plain,
% 0.45/0.69      (![X2 : $i, X3 : $i]:
% 0.45/0.69         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.69  thf('78', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.69  thf('79', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.45/0.69      inference('demod', [status(thm)], ['33', '78'])).
% 0.45/0.69  thf('80', plain,
% 0.45/0.69      (![X6 : $i, X7 : $i]:
% 0.45/0.69         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.45/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.69  thf('81', plain,
% 0.45/0.69      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['79', '80'])).
% 0.45/0.69  thf('82', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.45/0.69      inference('simplify', [status(thm)], ['81'])).
% 0.45/0.69  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
