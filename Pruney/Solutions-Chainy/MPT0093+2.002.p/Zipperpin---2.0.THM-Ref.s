%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OyX2RF64F4

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:46 EST 2020

% Result     : Theorem 3.61s
% Output     : Refutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 311 expanded)
%              Number of leaves         :   15 ( 106 expanded)
%              Depth                    :   30
%              Number of atoms          :  710 (2341 expanded)
%              Number of equality atoms :   82 ( 262 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t86_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('37',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','42','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != ( k3_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['21','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_B )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('70',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('74',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','19','76','77'])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','80'])).

thf('82',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OyX2RF64F4
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.61/3.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.61/3.80  % Solved by: fo/fo7.sh
% 3.61/3.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.61/3.80  % done 4010 iterations in 3.337s
% 3.61/3.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.61/3.80  % SZS output start Refutation
% 3.61/3.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.61/3.80  thf(sk_C_type, type, sk_C: $i).
% 3.61/3.80  thf(sk_B_type, type, sk_B: $i).
% 3.61/3.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.61/3.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.61/3.80  thf(sk_A_type, type, sk_A: $i).
% 3.61/3.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.61/3.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.61/3.80  thf(t86_xboole_1, conjecture,
% 3.61/3.80    (![A:$i,B:$i,C:$i]:
% 3.61/3.80     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 3.61/3.80       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 3.61/3.80  thf(zf_stmt_0, negated_conjecture,
% 3.61/3.80    (~( ![A:$i,B:$i,C:$i]:
% 3.61/3.80        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 3.61/3.80          ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 3.61/3.80    inference('cnf.neg', [status(esa)], [t86_xboole_1])).
% 3.61/3.80  thf('0', plain, (~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(l32_xboole_1, axiom,
% 3.61/3.80    (![A:$i,B:$i]:
% 3.61/3.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.61/3.80  thf('2', plain,
% 3.61/3.80      (![X2 : $i, X4 : $i]:
% 3.61/3.80         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 3.61/3.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.61/3.80  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['1', '2'])).
% 3.61/3.80  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 3.61/3.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.61/3.80  thf(t83_xboole_1, axiom,
% 3.61/3.80    (![A:$i,B:$i]:
% 3.61/3.80     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.61/3.80  thf('5', plain,
% 3.61/3.80      (![X11 : $i, X12 : $i]:
% 3.61/3.80         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 3.61/3.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.61/3.80  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 3.61/3.80      inference('sup-', [status(thm)], ['4', '5'])).
% 3.61/3.80  thf(commutativity_k3_xboole_0, axiom,
% 3.61/3.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.61/3.80  thf('7', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.61/3.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.61/3.80  thf(t49_xboole_1, axiom,
% 3.61/3.80    (![A:$i,B:$i,C:$i]:
% 3.61/3.80     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 3.61/3.80       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 3.61/3.80  thf('8', plain,
% 3.61/3.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 3.61/3.80           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 3.61/3.80      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.61/3.80  thf('9', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 3.61/3.80           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 3.61/3.80      inference('sup+', [status(thm)], ['7', '8'])).
% 3.61/3.80  thf('10', plain,
% 3.61/3.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 3.61/3.80           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 3.61/3.80      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.61/3.80  thf('11', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 3.61/3.80           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.61/3.80      inference('sup+', [status(thm)], ['9', '10'])).
% 3.61/3.80  thf('12', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X0 @ sk_A)
% 3.61/3.80           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)))),
% 3.61/3.80      inference('sup+', [status(thm)], ['6', '11'])).
% 3.61/3.80  thf(t48_xboole_1, axiom,
% 3.61/3.80    (![A:$i,B:$i]:
% 3.61/3.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.61/3.80  thf('13', plain,
% 3.61/3.80      (![X6 : $i, X7 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 3.61/3.80           = (k3_xboole_0 @ X6 @ X7))),
% 3.61/3.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.61/3.80  thf('14', plain,
% 3.61/3.80      (![X6 : $i, X7 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 3.61/3.80           = (k3_xboole_0 @ X6 @ X7))),
% 3.61/3.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.61/3.80  thf('15', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.61/3.80           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.61/3.80      inference('sup+', [status(thm)], ['13', '14'])).
% 3.61/3.80  thf('16', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_A))
% 3.61/3.80           = (k3_xboole_0 @ sk_A @ 
% 3.61/3.80              (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))))),
% 3.61/3.80      inference('sup+', [status(thm)], ['12', '15'])).
% 3.61/3.80  thf('17', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.61/3.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.61/3.80  thf('18', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.61/3.80           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.61/3.80      inference('sup+', [status(thm)], ['13', '14'])).
% 3.61/3.80  thf('19', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.61/3.80           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.61/3.80      inference('sup+', [status(thm)], ['17', '18'])).
% 3.61/3.80  thf('20', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['1', '2'])).
% 3.61/3.80  thf('21', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.61/3.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.61/3.80  thf('22', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['1', '2'])).
% 3.61/3.80  thf('23', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['1', '2'])).
% 3.61/3.80  thf('24', plain,
% 3.61/3.80      (![X6 : $i, X7 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 3.61/3.80           = (k3_xboole_0 @ X6 @ X7))),
% 3.61/3.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.61/3.80  thf('25', plain,
% 3.61/3.80      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 3.61/3.80      inference('sup+', [status(thm)], ['23', '24'])).
% 3.61/3.80  thf(t3_boole, axiom,
% 3.61/3.80    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.61/3.80  thf('26', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 3.61/3.80      inference('cnf', [status(esa)], [t3_boole])).
% 3.61/3.80  thf('27', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.61/3.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.61/3.80  thf('28', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.61/3.80      inference('demod', [status(thm)], ['25', '26', '27'])).
% 3.61/3.80  thf('29', plain,
% 3.61/3.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 3.61/3.80           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 3.61/3.80      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.61/3.80  thf('30', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 3.61/3.80           = (k4_xboole_0 @ sk_A @ X0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['28', '29'])).
% 3.61/3.80  thf('31', plain,
% 3.61/3.80      (((k3_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.61/3.80      inference('sup+', [status(thm)], ['22', '30'])).
% 3.61/3.80  thf('32', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.61/3.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.61/3.80  thf('33', plain,
% 3.61/3.80      (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.61/3.80      inference('demod', [status(thm)], ['31', '32'])).
% 3.61/3.80  thf('34', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['1', '2'])).
% 3.61/3.80  thf('35', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['33', '34'])).
% 3.61/3.80  thf('36', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.61/3.80           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.61/3.80      inference('sup+', [status(thm)], ['13', '14'])).
% 3.61/3.80  thf('37', plain,
% 3.61/3.80      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 3.61/3.80         = (k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 3.61/3.80      inference('sup+', [status(thm)], ['35', '36'])).
% 3.61/3.80  thf('38', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 3.61/3.80      inference('cnf', [status(esa)], [t3_boole])).
% 3.61/3.80  thf('39', plain,
% 3.61/3.80      (![X6 : $i, X7 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 3.61/3.80           = (k3_xboole_0 @ X6 @ X7))),
% 3.61/3.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.61/3.80  thf('40', plain,
% 3.61/3.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['38', '39'])).
% 3.61/3.80  thf('41', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.61/3.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.61/3.80  thf('42', plain,
% 3.61/3.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['40', '41'])).
% 3.61/3.80  thf('43', plain,
% 3.61/3.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['38', '39'])).
% 3.61/3.80  thf('44', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 3.61/3.80      inference('cnf', [status(esa)], [t3_boole])).
% 3.61/3.80  thf('45', plain,
% 3.61/3.80      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['43', '44'])).
% 3.61/3.80  thf('46', plain,
% 3.61/3.80      (((k1_xboole_0)
% 3.61/3.80         = (k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 3.61/3.80      inference('demod', [status(thm)], ['37', '42', '45'])).
% 3.61/3.80  thf('47', plain,
% 3.61/3.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 3.61/3.80           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 3.61/3.80      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.61/3.80  thf('48', plain,
% 3.61/3.80      (![X2 : $i, X3 : $i]:
% 3.61/3.80         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 3.61/3.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.61/3.80  thf('49', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.80         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.61/3.80          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['47', '48'])).
% 3.61/3.80  thf('50', plain,
% 3.61/3.80      ((((k1_xboole_0) != (k1_xboole_0))
% 3.61/3.80        | (r1_tarski @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ sk_B))),
% 3.61/3.80      inference('sup-', [status(thm)], ['46', '49'])).
% 3.61/3.80  thf('51', plain,
% 3.61/3.80      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['43', '44'])).
% 3.61/3.80  thf('52', plain,
% 3.61/3.80      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ sk_B))),
% 3.61/3.80      inference('demod', [status(thm)], ['50', '51'])).
% 3.61/3.80  thf('53', plain, ((r1_tarski @ k1_xboole_0 @ sk_B)),
% 3.61/3.80      inference('simplify', [status(thm)], ['52'])).
% 3.61/3.80  thf('54', plain,
% 3.61/3.80      (![X2 : $i, X4 : $i]:
% 3.61/3.80         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 3.61/3.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.61/3.80  thf('55', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['53', '54'])).
% 3.61/3.80  thf('56', plain,
% 3.61/3.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 3.61/3.80           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 3.61/3.80      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.61/3.80  thf('57', plain,
% 3.61/3.80      (![X11 : $i, X13 : $i]:
% 3.61/3.80         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 3.61/3.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.61/3.80  thf('58', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.80         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.61/3.80            != (k3_xboole_0 @ X2 @ X1))
% 3.61/3.80          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['56', '57'])).
% 3.61/3.80  thf('59', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k3_xboole_0 @ X0 @ k1_xboole_0))
% 3.61/3.80          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ sk_B))),
% 3.61/3.80      inference('sup-', [status(thm)], ['55', '58'])).
% 3.61/3.80  thf('60', plain,
% 3.61/3.80      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ sk_B)),
% 3.61/3.80      inference('simplify', [status(thm)], ['59'])).
% 3.61/3.80  thf('61', plain,
% 3.61/3.80      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ sk_B)),
% 3.61/3.80      inference('sup+', [status(thm)], ['21', '60'])).
% 3.61/3.80  thf('62', plain,
% 3.61/3.80      (![X11 : $i, X12 : $i]:
% 3.61/3.80         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 3.61/3.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.61/3.80  thf('63', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ sk_B)
% 3.61/3.80           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 3.61/3.80      inference('sup-', [status(thm)], ['61', '62'])).
% 3.61/3.80  thf('64', plain,
% 3.61/3.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 3.61/3.80           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 3.61/3.80      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.61/3.80  thf('65', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B))
% 3.61/3.80           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 3.61/3.80      inference('demod', [status(thm)], ['63', '64'])).
% 3.61/3.80  thf('66', plain,
% 3.61/3.80      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 3.61/3.80         = (k3_xboole_0 @ k1_xboole_0 @ sk_A))),
% 3.61/3.80      inference('sup+', [status(thm)], ['20', '65'])).
% 3.61/3.80  thf('67', plain,
% 3.61/3.80      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['43', '44'])).
% 3.61/3.80  thf('68', plain, (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_A))),
% 3.61/3.80      inference('demod', [status(thm)], ['66', '67'])).
% 3.61/3.80  thf('69', plain,
% 3.61/3.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['40', '41'])).
% 3.61/3.80  thf('70', plain,
% 3.61/3.80      (![X6 : $i, X7 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 3.61/3.80           = (k3_xboole_0 @ X6 @ X7))),
% 3.61/3.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.61/3.80  thf('71', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 3.61/3.80           = (k3_xboole_0 @ X0 @ X0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['69', '70'])).
% 3.61/3.80  thf('72', plain,
% 3.61/3.80      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_A))),
% 3.61/3.80      inference('sup+', [status(thm)], ['68', '71'])).
% 3.61/3.80  thf('73', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 3.61/3.80      inference('cnf', [status(esa)], [t3_boole])).
% 3.61/3.80  thf('74', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_A))),
% 3.61/3.80      inference('demod', [status(thm)], ['72', '73'])).
% 3.61/3.80  thf('75', plain,
% 3.61/3.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 3.61/3.80           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 3.61/3.80      inference('sup+', [status(thm)], ['7', '8'])).
% 3.61/3.80  thf('76', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 3.61/3.80           = (k4_xboole_0 @ sk_A @ X0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['74', '75'])).
% 3.61/3.80  thf('77', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 3.61/3.80           = (k4_xboole_0 @ sk_A @ X0))),
% 3.61/3.80      inference('sup+', [status(thm)], ['74', '75'])).
% 3.61/3.80  thf('78', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         ((k4_xboole_0 @ sk_A @ X0)
% 3.61/3.80           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)))),
% 3.61/3.80      inference('demod', [status(thm)], ['16', '19', '76', '77'])).
% 3.61/3.80  thf('79', plain,
% 3.61/3.80      (![X2 : $i, X3 : $i]:
% 3.61/3.80         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 3.61/3.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.61/3.80  thf('80', plain,
% 3.61/3.80      (![X0 : $i]:
% 3.61/3.80         (((k4_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 3.61/3.80          | (r1_tarski @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)))),
% 3.61/3.80      inference('sup-', [status(thm)], ['78', '79'])).
% 3.61/3.80  thf('81', plain,
% 3.61/3.80      ((((k1_xboole_0) != (k1_xboole_0))
% 3.61/3.80        | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 3.61/3.80      inference('sup-', [status(thm)], ['3', '80'])).
% 3.61/3.80  thf('82', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 3.61/3.80      inference('simplify', [status(thm)], ['81'])).
% 3.61/3.80  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 3.61/3.80  
% 3.61/3.80  % SZS output end Refutation
% 3.61/3.80  
% 3.61/3.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
