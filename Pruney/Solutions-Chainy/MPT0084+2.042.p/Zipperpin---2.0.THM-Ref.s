%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N9u50fyB1Y

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 207 expanded)
%              Number of leaves         :   17 (  74 expanded)
%              Depth                    :   26
%              Number of atoms          :  831 (1575 expanded)
%              Number of equality atoms :   89 ( 167 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('59',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('68',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['77','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['72','86'])).

thf('88',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','91'])).

thf('93',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('94',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N9u50fyB1Y
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 342 iterations in 0.120s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(t77_xboole_1, conjecture,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.20/0.57          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.57        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.20/0.57             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.20/0.57  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(d7_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf(t47_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.20/0.57           = (k4_xboole_0 @ X10 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.20/0.57         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf(t3_boole, axiom,
% 0.20/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.57  thf('6', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf(t48_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.57           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.57  thf(t36_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.57  thf(l32_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.57  thf(t49_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.20/0.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A) = (k1_xboole_0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['7', '14'])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.20/0.57           = (k4_xboole_0 @ X10 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ k1_xboole_0)
% 0.20/0.57         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('19', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.20/0.57         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.20/0.57  thf('22', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.57  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (![X3 : $i, X4 : $i]:
% 0.20/0.57         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.20/0.57          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.57          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.57  thf(t2_boole, axiom,
% 0.20/0.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.57          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_C @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['21', '33'])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.20/0.57         (k4_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.20/0.57           = (k4_xboole_0 @ X10 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.57           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.57           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (((k3_xboole_0 @ sk_B @ 
% 0.20/0.57         (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ sk_A))) = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['36', '37', '40'])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.20/0.57           = (k4_xboole_0 @ X10 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.20/0.57         = (k4_xboole_0 @ sk_B @ 
% 0.20/0.57            (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ sk_A))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.57  thf('44', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      (((sk_B)
% 0.20/0.57         = (k4_xboole_0 @ sk_B @ 
% 0.20/0.57            (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.57           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.57           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (((sk_B) = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['45', '48'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.20/0.57           = (k4_xboole_0 @ X10 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.57           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['50', '51'])).
% 0.20/0.57  thf('53', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (((k3_xboole_0 @ sk_C @ sk_A)
% 0.20/0.57         = (k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sup+', [status(thm)], ['49', '54'])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (((k3_xboole_0 @ sk_C @ sk_A)
% 0.20/0.57         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      ((r1_tarski @ (k3_xboole_0 @ sk_C @ sk_A) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.57      inference('sup+', [status(thm)], ['57', '58'])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.20/0.57         (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.57           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.57  thf('64', plain,
% 0.20/0.57      (((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.20/0.57  thf('65', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.20/0.57           = (k4_xboole_0 @ X10 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      (((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.20/0.57         = (k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['64', '65'])).
% 0.20/0.57  thf('67', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      (((sk_C) = (k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.57  thf('69', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.57  thf('70', plain,
% 0.20/0.57      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.20/0.57         = (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.57      inference('sup+', [status(thm)], ['68', '69'])).
% 0.20/0.57  thf('71', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('72', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.57           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.57           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.57  thf('75', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.20/0.57           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['73', '74'])).
% 0.20/0.57  thf('76', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.57  thf('77', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.57           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.57  thf('78', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('79', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('80', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.57  thf('81', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.20/0.57          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('82', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.57          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.57  thf('83', plain,
% 0.20/0.57      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.57  thf('84', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.57          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.57  thf('85', plain,
% 0.20/0.57      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C)),
% 0.20/0.57      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.57  thf('86', plain,
% 0.20/0.57      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.20/0.57      inference('sup+', [status(thm)], ['77', '85'])).
% 0.20/0.57  thf('87', plain,
% 0.20/0.57      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.20/0.57      inference('sup+', [status(thm)], ['72', '86'])).
% 0.20/0.57  thf('88', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('89', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.57  thf('90', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.57  thf('91', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)) = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.57  thf('92', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['70', '71', '91'])).
% 0.20/0.57  thf('93', plain,
% 0.20/0.57      (![X0 : $i, X2 : $i]:
% 0.20/0.57         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.57  thf('94', plain,
% 0.20/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.57  thf('95', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.57      inference('simplify', [status(thm)], ['94'])).
% 0.20/0.57  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
