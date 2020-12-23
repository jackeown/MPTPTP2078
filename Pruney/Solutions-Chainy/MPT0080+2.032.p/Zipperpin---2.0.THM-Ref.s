%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U7PfgOaLBu

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:08 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 161 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  716 (1204 expanded)
%              Number of equality atoms :   76 ( 129 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['12','25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['38','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['56','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['55','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['54','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','75'])).

thf('77',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U7PfgOaLBu
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:07:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.57/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.82  % Solved by: fo/fo7.sh
% 0.57/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.82  % done 859 iterations in 0.351s
% 0.57/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.82  % SZS output start Refutation
% 0.57/0.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.82  thf(t73_xboole_1, conjecture,
% 0.57/0.82    (![A:$i,B:$i,C:$i]:
% 0.57/0.82     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.57/0.82       ( r1_tarski @ A @ B ) ))).
% 0.57/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.57/0.82        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.57/0.82            ( r1_xboole_0 @ A @ C ) ) =>
% 0.57/0.82          ( r1_tarski @ A @ B ) ) )),
% 0.57/0.82    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.57/0.82  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.57/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.82  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.57/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.82  thf(l32_xboole_1, axiom,
% 0.57/0.82    (![A:$i,B:$i]:
% 0.57/0.82     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.82  thf('2', plain,
% 0.57/0.82      (![X5 : $i, X7 : $i]:
% 0.57/0.82         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.57/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.57/0.82  thf('3', plain,
% 0.57/0.82      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.57/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.82  thf(t41_xboole_1, axiom,
% 0.57/0.82    (![A:$i,B:$i,C:$i]:
% 0.57/0.82     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.82       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.57/0.82  thf('4', plain,
% 0.57/0.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.57/0.82           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.57/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.82  thf(t39_xboole_1, axiom,
% 0.57/0.82    (![A:$i,B:$i]:
% 0.57/0.82     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.57/0.82  thf('5', plain,
% 0.57/0.82      (![X9 : $i, X10 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.57/0.82           = (k2_xboole_0 @ X9 @ X10))),
% 0.57/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.57/0.82  thf('6', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.57/0.82           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['4', '5'])).
% 0.57/0.82  thf('7', plain,
% 0.57/0.82      (((k2_xboole_0 @ sk_C @ k1_xboole_0)
% 0.57/0.82         = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['3', '6'])).
% 0.57/0.82  thf(commutativity_k2_xboole_0, axiom,
% 0.57/0.82    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.57/0.82  thf('8', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.57/0.82  thf('9', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.57/0.82  thf(t1_boole, axiom,
% 0.57/0.82    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.82  thf('10', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.57/0.82      inference('cnf', [status(esa)], [t1_boole])).
% 0.57/0.82  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.82      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.82  thf('12', plain,
% 0.57/0.82      (((sk_C) = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.57/0.82      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.57/0.82  thf('13', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.57/0.82  thf(t7_xboole_1, axiom,
% 0.57/0.82    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.57/0.82  thf('14', plain,
% 0.57/0.82      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.57/0.82      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.57/0.82  thf('15', plain,
% 0.57/0.82      (![X5 : $i, X7 : $i]:
% 0.57/0.82         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.57/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.57/0.82  thf('16', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.57/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.57/0.82  thf(t48_xboole_1, axiom,
% 0.57/0.82    (![A:$i,B:$i]:
% 0.57/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.82  thf('17', plain,
% 0.57/0.82      (![X14 : $i, X15 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.57/0.82           = (k3_xboole_0 @ X14 @ X15))),
% 0.57/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.82  thf('18', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.57/0.82           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['16', '17'])).
% 0.57/0.82  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.82      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.82  thf('20', plain,
% 0.57/0.82      (![X9 : $i, X10 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.57/0.82           = (k2_xboole_0 @ X9 @ X10))),
% 0.57/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.57/0.82  thf('21', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.82      inference('sup+', [status(thm)], ['19', '20'])).
% 0.57/0.82  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.82      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.82  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.57/0.82      inference('demod', [status(thm)], ['21', '22'])).
% 0.57/0.82  thf('24', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.57/0.82      inference('demod', [status(thm)], ['18', '23'])).
% 0.57/0.82  thf('25', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['13', '24'])).
% 0.57/0.82  thf('26', plain,
% 0.57/0.82      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.57/0.82         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.57/0.82      inference('sup+', [status(thm)], ['12', '25'])).
% 0.57/0.82  thf('27', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.57/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.82  thf(d7_xboole_0, axiom,
% 0.57/0.82    (![A:$i,B:$i]:
% 0.57/0.82     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.57/0.82       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.57/0.82  thf('28', plain,
% 0.57/0.82      (![X2 : $i, X3 : $i]:
% 0.57/0.82         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.57/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.82  thf('29', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.57/0.82      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.82  thf('30', plain,
% 0.57/0.82      (![X14 : $i, X15 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.57/0.82           = (k3_xboole_0 @ X14 @ X15))),
% 0.57/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.82  thf('31', plain,
% 0.57/0.82      (![X9 : $i, X10 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.57/0.82           = (k2_xboole_0 @ X9 @ X10))),
% 0.57/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.57/0.82  thf('32', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.82           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.57/0.82      inference('sup+', [status(thm)], ['30', '31'])).
% 0.57/0.82  thf('33', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.57/0.82  thf('34', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.57/0.82  thf('35', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.57/0.82           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.82      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.57/0.82  thf('36', plain,
% 0.57/0.82      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.57/0.82         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['29', '35'])).
% 0.57/0.82  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.82      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.82  thf('38', plain,
% 0.57/0.82      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.57/0.82         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.57/0.82      inference('demod', [status(thm)], ['36', '37'])).
% 0.57/0.82  thf('39', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.57/0.82      inference('cnf', [status(esa)], [t1_boole])).
% 0.57/0.82  thf('40', plain,
% 0.57/0.82      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.57/0.82      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.57/0.82  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.57/0.82      inference('sup+', [status(thm)], ['39', '40'])).
% 0.57/0.82  thf('42', plain,
% 0.57/0.82      (![X5 : $i, X7 : $i]:
% 0.57/0.82         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.57/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.57/0.82  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.57/0.82      inference('sup-', [status(thm)], ['41', '42'])).
% 0.57/0.82  thf('44', plain,
% 0.57/0.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.57/0.82           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.57/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.82  thf('45', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k1_xboole_0)
% 0.57/0.82           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.57/0.82      inference('sup+', [status(thm)], ['43', '44'])).
% 0.57/0.82  thf('46', plain,
% 0.57/0.82      (![X9 : $i, X10 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.57/0.82           = (k2_xboole_0 @ X9 @ X10))),
% 0.57/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.57/0.82  thf('47', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.57/0.82      inference('demod', [status(thm)], ['45', '46'])).
% 0.57/0.82  thf('48', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.57/0.82           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['4', '5'])).
% 0.57/0.82  thf('49', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.57/0.82           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['47', '48'])).
% 0.57/0.82  thf('50', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.57/0.82      inference('cnf', [status(esa)], [t1_boole])).
% 0.57/0.82  thf('51', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.82      inference('demod', [status(thm)], ['49', '50'])).
% 0.57/0.82  thf('52', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.57/0.82      inference('demod', [status(thm)], ['38', '51'])).
% 0.57/0.82  thf('53', plain,
% 0.57/0.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.57/0.82           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.57/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.82  thf('54', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ sk_A @ X0)
% 0.57/0.82           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['52', '53'])).
% 0.57/0.82  thf('55', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.57/0.82  thf('56', plain,
% 0.57/0.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.57/0.82           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.57/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.82  thf('57', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.57/0.82           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.57/0.82      inference('sup+', [status(thm)], ['4', '5'])).
% 0.57/0.82  thf('58', plain,
% 0.57/0.82      (![X14 : $i, X15 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.57/0.82           = (k3_xboole_0 @ X14 @ X15))),
% 0.57/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.82  thf('59', plain,
% 0.57/0.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.57/0.82           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.57/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.82  thf('60', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.57/0.82           = (k4_xboole_0 @ X2 @ 
% 0.57/0.82              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.57/0.82      inference('sup+', [status(thm)], ['58', '59'])).
% 0.57/0.82  thf('61', plain,
% 0.57/0.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.57/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.57/0.82           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.57/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.82  thf('62', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.57/0.82           = (k4_xboole_0 @ X2 @ 
% 0.57/0.82              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.57/0.82      inference('demod', [status(thm)], ['60', '61'])).
% 0.57/0.82  thf('63', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.57/0.82           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.57/0.82      inference('sup+', [status(thm)], ['57', '62'])).
% 0.57/0.82  thf('64', plain,
% 0.57/0.82      (![X9 : $i, X10 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.57/0.82           = (k2_xboole_0 @ X9 @ X10))),
% 0.57/0.82      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.57/0.82  thf('65', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.57/0.82           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.57/0.82      inference('demod', [status(thm)], ['63', '64'])).
% 0.57/0.82  thf('66', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.57/0.82      inference('demod', [status(thm)], ['45', '46'])).
% 0.57/0.82  thf('67', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.57/0.82      inference('demod', [status(thm)], ['65', '66'])).
% 0.57/0.82  thf('68', plain,
% 0.57/0.82      (![X2 : $i, X4 : $i]:
% 0.57/0.82         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.57/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.82  thf('69', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         (((k1_xboole_0) != (k1_xboole_0))
% 0.57/0.82          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.57/0.82      inference('sup-', [status(thm)], ['67', '68'])).
% 0.57/0.82  thf('70', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.57/0.82      inference('simplify', [status(thm)], ['69'])).
% 0.57/0.82  thf('71', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.82         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 0.57/0.82      inference('sup+', [status(thm)], ['56', '70'])).
% 0.57/0.82  thf('72', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.82         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 0.57/0.82      inference('sup+', [status(thm)], ['55', '71'])).
% 0.57/0.82  thf('73', plain,
% 0.57/0.82      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.57/0.82      inference('sup+', [status(thm)], ['54', '72'])).
% 0.57/0.82  thf('74', plain,
% 0.57/0.82      (![X2 : $i, X3 : $i]:
% 0.57/0.82         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.57/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.82  thf('75', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C) = (k1_xboole_0))),
% 0.57/0.82      inference('sup-', [status(thm)], ['73', '74'])).
% 0.57/0.82  thf('76', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.57/0.82      inference('demod', [status(thm)], ['26', '75'])).
% 0.57/0.82  thf('77', plain,
% 0.57/0.82      (![X5 : $i, X6 : $i]:
% 0.57/0.82         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.57/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.57/0.82  thf('78', plain,
% 0.57/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.57/0.82      inference('sup-', [status(thm)], ['76', '77'])).
% 0.57/0.82  thf('79', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.57/0.82      inference('simplify', [status(thm)], ['78'])).
% 0.57/0.82  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.57/0.82  
% 0.57/0.82  % SZS output end Refutation
% 0.57/0.82  
% 0.57/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
