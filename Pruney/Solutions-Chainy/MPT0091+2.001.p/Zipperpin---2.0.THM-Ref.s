%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GgNVYq3fg7

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:42 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 178 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  574 (1382 expanded)
%              Number of equality atoms :   59 ( 142 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t84_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C )
          & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_C )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['27','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','24','25'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['9','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GgNVYq3fg7
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 381 iterations in 0.308s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(t84_xboole_1, conjecture,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.59/0.77          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.77        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.59/0.77             ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t84_xboole_1])).
% 0.59/0.77  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t81_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.59/0.77       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.59/0.77          | ~ (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X18 @ X20)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.59/0.77  thf('3', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.77  thf(t3_boole, axiom,
% 0.59/0.77    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.77  thf('4', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.59/0.77          | ~ (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X18 @ X20)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (r1_xboole_0 @ X1 @ X0)
% 0.59/0.77          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.77  thf('7', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.77  thf('9', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.59/0.77      inference('sup-', [status(thm)], ['3', '8'])).
% 0.59/0.77  thf('10', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.77  thf('11', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.77  thf(t54_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.59/0.77       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.59/0.77           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.59/0.77              (k4_xboole_0 @ X12 @ X14)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.59/0.77  thf(commutativity_k2_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 0.59/0.77           = (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.77           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['11', '14'])).
% 0.59/0.77  thf(t4_boole, axiom,
% 0.59/0.77    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [t4_boole])).
% 0.59/0.77  thf(t49_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.59/0.77       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 0.59/0.77      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ k1_xboole_0) @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.77  thf(t41_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.77       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.59/0.77           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.77  thf('20', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.59/0.77           = (k4_xboole_0 @ X1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['19', '20'])).
% 0.59/0.77  thf(t46_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.77  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['18', '23'])).
% 0.59/0.77  thf('25', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '24', '25'])).
% 0.59/0.77  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['10', '26'])).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.77  thf('29', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t78_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( r1_xboole_0 @ A @ B ) =>
% 0.59/0.77       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.59/0.77         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.77         (~ (r1_xboole_0 @ X15 @ X16)
% 0.59/0.77          | ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.59/0.77              = (k3_xboole_0 @ X15 @ X17)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.59/0.77           = (k3_xboole_0 @ sk_A @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))
% 0.59/0.77           = (k3_xboole_0 @ sk_A @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['28', '31'])).
% 0.59/0.77  thf('33', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.77         (~ (r1_xboole_0 @ X15 @ X16)
% 0.59/0.77          | ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.59/0.77              = (k3_xboole_0 @ X15 @ X17)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.59/0.77  thf('35', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ sk_A @ 
% 0.59/0.77           (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.59/0.77           = (k3_xboole_0 @ sk_A @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.77  thf('36', plain,
% 0.59/0.77      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.59/0.77         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('sup+', [status(thm)], ['32', '35'])).
% 0.59/0.77  thf('37', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 0.59/0.77      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.59/0.77  thf('38', plain,
% 0.59/0.77      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.59/0.77         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.77  thf('39', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.59/0.77           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.77  thf('40', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ X0)
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.59/0.77              (k2_xboole_0 @ sk_C @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['38', '39'])).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_C)
% 0.59/0.77         = (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.59/0.77      inference('sup+', [status(thm)], ['27', '40'])).
% 0.59/0.77  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('43', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 0.59/0.77      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.59/0.77  thf('44', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['42', '43'])).
% 0.59/0.77  thf('45', plain,
% 0.59/0.77      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['18', '23'])).
% 0.59/0.77  thf('46', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['44', '45'])).
% 0.59/0.77  thf('47', plain,
% 0.59/0.77      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.59/0.77         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.77  thf('48', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['41', '46', '47'])).
% 0.59/0.77  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('50', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.59/0.77           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.59/0.77              (k4_xboole_0 @ X12 @ X14)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.59/0.77  thf('51', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['49', '50'])).
% 0.59/0.77  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('53', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '24', '25'])).
% 0.59/0.77  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['52', '53'])).
% 0.59/0.77  thf('55', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.77  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['54', '55'])).
% 0.59/0.77  thf('57', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77           = (k4_xboole_0 @ X1 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['51', '56'])).
% 0.59/0.77  thf('58', plain,
% 0.59/0.77      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('sup+', [status(thm)], ['48', '57'])).
% 0.59/0.77  thf('59', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.77  thf('60', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['58', '59'])).
% 0.59/0.77  thf('61', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.59/0.77      inference('demod', [status(thm)], ['9', '60'])).
% 0.59/0.77  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
