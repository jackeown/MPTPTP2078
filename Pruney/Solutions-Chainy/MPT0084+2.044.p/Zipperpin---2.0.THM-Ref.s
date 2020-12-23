%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8OtfX4wdsH

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 285 expanded)
%              Number of leaves         :   18 (  99 expanded)
%              Depth                    :   26
%              Number of atoms          :  836 (2170 expanded)
%              Number of equality atoms :   93 ( 249 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
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
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['19','44'])).

thf('46',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('64',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('73',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('75',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['79','87'])).

thf('89',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76','92'])).

thf('94',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8OtfX4wdsH
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 380 iterations in 0.130s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.58  thf(t77_xboole_1, conjecture,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.58          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.58        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.58             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.21/0.58  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(d7_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.58  thf(t47_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (![X9 : $i, X10 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.21/0.58           = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.58         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.58  thf(t3_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('6', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.58  thf(t51_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.21/0.58       ( A ) ))).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.58           = (X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.58  thf(t46_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.58  thf(t49_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.21/0.58       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.58           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A) = (k1_xboole_0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['7', '12'])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X9 : $i, X10 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.21/0.58           = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ k1_xboole_0)
% 0.21/0.58         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.58           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.58  thf('17', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.58           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.21/0.58         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X9 : $i, X10 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.21/0.58           = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.58  thf(l32_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X3 : $i, X4 : $i]:
% 0.21/0.58         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.58          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.58          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.58  thf(t48_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.21/0.58           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.58  thf('29', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf('31', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.58      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X3 : $i, X5 : $i]:
% 0.21/0.58         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.58  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.58           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X3 : $i, X4 : $i]:
% 0.21/0.58         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.21/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.59  thf('36', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.21/0.59          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.59  thf('37', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.59          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.59  thf('38', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.59  thf('39', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.59  thf('40', plain,
% 0.21/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.59  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.59  thf('42', plain,
% 0.21/0.59      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.59  thf('43', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.59          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['37', '42'])).
% 0.21/0.59  thf('44', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.59  thf('45', plain,
% 0.21/0.59      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.59      inference('sup+', [status(thm)], ['19', '44'])).
% 0.21/0.59  thf('46', plain,
% 0.21/0.59      (![X3 : $i, X5 : $i]:
% 0.21/0.59         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.59  thf('47', plain,
% 0.21/0.59      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.21/0.59         (k4_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.59  thf('48', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.59  thf('49', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.59  thf('50', plain,
% 0.21/0.59      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.59  thf('51', plain,
% 0.21/0.59      (![X9 : $i, X10 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.21/0.59           = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.59  thf('52', plain,
% 0.21/0.59      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.21/0.59         = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.59  thf('53', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.59  thf('54', plain,
% 0.21/0.59      (((sk_B) = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.21/0.59      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.59  thf('55', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.59  thf('56', plain,
% 0.21/0.59      (![X9 : $i, X10 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.21/0.59           = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.59  thf('57', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.21/0.59           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.59  thf('58', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.59  thf('59', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.59      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.59  thf('60', plain,
% 0.21/0.59      (((k3_xboole_0 @ sk_C @ sk_A)
% 0.21/0.59         = (k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.21/0.59      inference('sup+', [status(thm)], ['54', '59'])).
% 0.21/0.59  thf('61', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.59  thf('62', plain,
% 0.21/0.59      (((k3_xboole_0 @ sk_C @ sk_A)
% 0.21/0.59         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.59      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.59  thf('63', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.59  thf('64', plain,
% 0.21/0.59      ((r1_tarski @ (k3_xboole_0 @ sk_C @ sk_A) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.59      inference('sup+', [status(thm)], ['62', '63'])).
% 0.21/0.59  thf('65', plain,
% 0.21/0.59      (![X3 : $i, X5 : $i]:
% 0.21/0.59         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.59  thf('66', plain,
% 0.21/0.59      (((k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.21/0.59         (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.59  thf('67', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.59  thf('68', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.59  thf('69', plain,
% 0.21/0.59      (((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.21/0.59  thf('70', plain,
% 0.21/0.59      (![X9 : $i, X10 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.21/0.59           = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.59  thf('71', plain,
% 0.21/0.59      (((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.21/0.59         = (k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['69', '70'])).
% 0.21/0.59  thf('72', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.59  thf('73', plain,
% 0.21/0.59      (((sk_C) = (k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.59      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.59  thf('74', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.59      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.59  thf('75', plain,
% 0.21/0.59      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.21/0.59         = (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.59      inference('sup+', [status(thm)], ['73', '74'])).
% 0.21/0.59  thf('76', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.59  thf('77', plain,
% 0.21/0.59      (![X16 : $i, X17 : $i]:
% 0.21/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.21/0.59           = (X16))),
% 0.21/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.59  thf('78', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf('79', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X0 @ X1)
% 0.21/0.59           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['77', '78'])).
% 0.21/0.59  thf('80', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('81', plain,
% 0.21/0.59      (![X3 : $i, X5 : $i]:
% 0.21/0.59         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.59  thf('82', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.59  thf('83', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.21/0.59          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.59  thf('84', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.59          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C))),
% 0.21/0.59      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.59  thf('85', plain,
% 0.21/0.59      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.59  thf('86', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.59          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C))),
% 0.21/0.59      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.59  thf('87', plain,
% 0.21/0.59      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C)),
% 0.21/0.59      inference('simplify', [status(thm)], ['86'])).
% 0.21/0.59  thf('88', plain,
% 0.21/0.59      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.21/0.59      inference('sup+', [status(thm)], ['79', '87'])).
% 0.21/0.59  thf('89', plain,
% 0.21/0.59      (![X3 : $i, X5 : $i]:
% 0.21/0.59         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.59  thf('90', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C) = (k1_xboole_0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.59  thf('91', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.59  thf('92', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)) = (k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.59  thf('93', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['75', '76', '92'])).
% 0.21/0.59  thf('94', plain,
% 0.21/0.59      (![X0 : $i, X2 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.59  thf('95', plain,
% 0.21/0.59      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.59  thf('96', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.59      inference('simplify', [status(thm)], ['95'])).
% 0.21/0.59  thf('97', plain, ($false), inference('demod', [status(thm)], ['0', '96'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
