%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.00OvT5Y6u5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:05 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 897 expanded)
%              Number of leaves         :   19 ( 306 expanded)
%              Depth                    :   23
%              Number of atoms          : 1090 (6368 expanded)
%              Number of equality atoms :  125 ( 807 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ k1_xboole_0 @ sk_A ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ sk_A ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('23',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('33',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','47'])).

thf('49',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','46'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('72',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('79',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','46'])).

thf('88',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('91',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','46'])).

thf('94',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','99'])).

thf('101',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup+',[status(thm)],['81','100'])).

thf('102',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','94'])).

thf('105',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('107',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['101','102','103','104','105','106'])).

thf('108',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','109'])).

thf('111',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['101','102','103','104','105','106'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ sk_C )
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','46'])).

thf('116',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','99'])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 )
    = sk_B ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('121',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['0','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.00OvT5Y6u5
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:29:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 1028 iterations in 0.422s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(t73_xboole_1, conjecture,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.68/0.88       ( r1_tarski @ A @ B ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.88        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.68/0.88            ( r1_xboole_0 @ A @ C ) ) =>
% 0.68/0.88          ( r1_tarski @ A @ B ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.68/0.88  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t12_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i]:
% 0.68/0.88         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.68/0.88      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(d7_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.68/0.88       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]:
% 0.68/0.88         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.68/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.68/0.88  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf('8', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['6', '7'])).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf(t17_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.68/0.88      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.68/0.88      inference('sup+', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('12', plain, ((r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.68/0.88      inference('sup+', [status(thm)], ['8', '11'])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i]:
% 0.68/0.88         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.68/0.88      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.68/0.88  thf('14', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.88  thf(t40_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.68/0.88           = (k4_xboole_0 @ X12 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf(t41_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.68/0.88       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.68/0.88           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ sk_A) @ X0)
% 0.68/0.88           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['16', '17'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.68/0.88           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0))
% 0.68/0.88           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['18', '19'])).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (((k4_xboole_0 @ k1_xboole_0 @ 
% 0.68/0.88         (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.68/0.88         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['3', '20'])).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.68/0.88           = (k4_xboole_0 @ X12 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.68/0.88         (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['24', '25'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.68/0.88         (k2_xboole_0 @ sk_B @ sk_C))
% 0.68/0.88         = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.68/0.88  thf(t3_boole, axiom,
% 0.68/0.88    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.88  thf('29', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf(t48_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['29', '30'])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.68/0.88           = (k4_xboole_0 @ X12 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.68/0.88  thf('33', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['32', '33'])).
% 0.68/0.88  thf('35', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['34', '35'])).
% 0.68/0.88  thf(commutativity_k2_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.88  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['36', '37'])).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.68/0.88      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i]:
% 0.68/0.88         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.68/0.88      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['40', '41'])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['42', '43'])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['39', '44'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['38', '45'])).
% 0.68/0.88  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['31', '46'])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      (((k1_xboole_0)
% 0.68/0.88         = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['28', '47'])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.88      inference('demod', [status(thm)], ['23', '48'])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.68/0.88           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.68/0.88           = (k4_xboole_0 @ X2 @ 
% 0.68/0.88              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['50', '51'])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.68/0.88           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.68/0.88           = (k4_xboole_0 @ X2 @ 
% 0.68/0.88              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.68/0.88      inference('demod', [status(thm)], ['52', '53'])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.68/0.88         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['49', '54'])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['34', '35'])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      (((k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.68/0.88         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.68/0.88  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['31', '46'])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.68/0.88           = (k4_xboole_0 @ X2 @ 
% 0.68/0.88              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.68/0.88      inference('demod', [status(thm)], ['52', '53'])).
% 0.68/0.88  thf('61', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 0.68/0.88           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.68/0.88              (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['59', '60'])).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.68/0.88           = (k4_xboole_0 @ X12 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['62', '63'])).
% 0.68/0.88  thf('65', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['34', '35'])).
% 0.68/0.88  thf('67', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['62', '63'])).
% 0.68/0.88  thf('68', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('demod', [status(thm)], ['61', '64', '65', '66', '67'])).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['42', '43'])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['68', '69'])).
% 0.68/0.88  thf('71', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['6', '7'])).
% 0.68/0.88  thf('72', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('73', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('74', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['72', '73'])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      (((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.68/0.88         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['71', '74'])).
% 0.68/0.88  thf('76', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('77', plain,
% 0.68/0.88      (((sk_C) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['75', '76'])).
% 0.68/0.88  thf('78', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['39', '44'])).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      (((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_C)
% 0.68/0.88         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['77', '78'])).
% 0.68/0.88  thf('80', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.88  thf('81', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 0.68/0.88         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['79', '80'])).
% 0.68/0.88  thf('82', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['62', '63'])).
% 0.68/0.88  thf('83', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('84', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['82', '83'])).
% 0.68/0.88  thf('85', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf('86', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['84', '85'])).
% 0.68/0.88  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['31', '46'])).
% 0.68/0.88  thf('88', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.68/0.88           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('89', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.68/0.88           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['87', '88'])).
% 0.68/0.88  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['36', '37'])).
% 0.68/0.88  thf('91', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.68/0.88           = (k4_xboole_0 @ X12 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.68/0.88  thf('92', plain,
% 0.68/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['90', '91'])).
% 0.68/0.88  thf('93', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['31', '46'])).
% 0.68/0.88  thf('94', plain,
% 0.68/0.88      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['92', '93'])).
% 0.68/0.88  thf('95', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['89', '94'])).
% 0.68/0.88  thf('96', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k3_xboole_0 @ X17 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('97', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.68/0.88           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['95', '96'])).
% 0.68/0.88  thf('98', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('99', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['97', '98'])).
% 0.68/0.88  thf('100', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['86', '99'])).
% 0.68/0.88  thf('101', plain,
% 0.68/0.88      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ 
% 0.68/0.88         (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_C)) = (sk_C))),
% 0.68/0.88      inference('sup+', [status(thm)], ['81', '100'])).
% 0.68/0.88  thf('102', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.68/0.88           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('103', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.88  thf('104', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['89', '94'])).
% 0.68/0.88  thf('105', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.68/0.88           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('106', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['34', '35'])).
% 0.68/0.89  thf('107', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.68/0.89      inference('demod', [status(thm)],
% 0.68/0.89                ['101', '102', '103', '104', '105', '106'])).
% 0.68/0.89  thf('108', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.68/0.89           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.89  thf('109', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ sk_C @ X0)
% 0.68/0.89           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['107', '108'])).
% 0.68/0.89  thf('110', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.68/0.89           = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.68/0.89      inference('sup+', [status(thm)], ['70', '109'])).
% 0.68/0.89  thf('111', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.68/0.89      inference('demod', [status(thm)],
% 0.68/0.89                ['101', '102', '103', '104', '105', '106'])).
% 0.68/0.89  thf('112', plain,
% 0.68/0.89      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 0.68/0.89      inference('demod', [status(thm)], ['110', '111'])).
% 0.68/0.89  thf('113', plain,
% 0.68/0.89      (![X17 : $i, X18 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.89           = (k3_xboole_0 @ X17 @ X18))),
% 0.68/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.89  thf('114', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ sk_C @ sk_C)
% 0.68/0.89           = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['112', '113'])).
% 0.68/0.89  thf('115', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.89      inference('demod', [status(thm)], ['31', '46'])).
% 0.68/0.89  thf('116', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.68/0.89      inference('demod', [status(thm)], ['114', '115'])).
% 0.68/0.89  thf('117', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.89      inference('demod', [status(thm)], ['58', '116'])).
% 0.68/0.89  thf('118', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.89           = (X0))),
% 0.68/0.89      inference('demod', [status(thm)], ['86', '99'])).
% 0.68/0.89  thf('119', plain,
% 0.68/0.89      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0) = (sk_B))),
% 0.68/0.89      inference('sup+', [status(thm)], ['117', '118'])).
% 0.68/0.89  thf('120', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.68/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.89  thf('121', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.68/0.89      inference('demod', [status(thm)], ['119', '120'])).
% 0.68/0.89  thf('122', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.89  thf('123', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.89      inference('demod', [status(thm)], ['97', '98'])).
% 0.68/0.89  thf('124', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.68/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.68/0.89  thf('125', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('sup+', [status(thm)], ['123', '124'])).
% 0.68/0.89  thf('126', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['122', '125'])).
% 0.68/0.89  thf('127', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.68/0.89      inference('sup+', [status(thm)], ['121', '126'])).
% 0.68/0.89  thf('128', plain, ($false), inference('demod', [status(thm)], ['0', '127'])).
% 0.68/0.89  
% 0.68/0.89  % SZS output end Refutation
% 0.68/0.89  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
