%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2PnB4QORDx

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:44 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 117 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  528 ( 778 expanded)
%              Number of equality atoms :   56 (  82 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t85_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('52',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ X22 )
      | ( ( k4_xboole_0 @ X20 @ X22 )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2PnB4QORDx
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:54:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 1.03/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.23  % Solved by: fo/fo7.sh
% 1.03/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.23  % done 2020 iterations in 0.776s
% 1.03/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.23  % SZS output start Refutation
% 1.03/1.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.03/1.23  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.03/1.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.03/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.23  thf(sk_C_type, type, sk_C: $i).
% 1.03/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.03/1.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.03/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.23  thf(t85_xboole_1, conjecture,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.03/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.23    (~( ![A:$i,B:$i,C:$i]:
% 1.03/1.23        ( ( r1_tarski @ A @ B ) =>
% 1.03/1.23          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )),
% 1.03/1.23    inference('cnf.neg', [status(esa)], [t85_xboole_1])).
% 1.03/1.23  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf(t48_xboole_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.03/1.23  thf('1', plain,
% 1.03/1.23      (![X15 : $i, X16 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.03/1.23           = (k3_xboole_0 @ X15 @ X16))),
% 1.03/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.03/1.23  thf(commutativity_k2_xboole_0, axiom,
% 1.03/1.23    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.03/1.23  thf('2', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.03/1.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.03/1.23  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf(l32_xboole_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.03/1.23  thf('4', plain,
% 1.03/1.23      (![X2 : $i, X4 : $i]:
% 1.03/1.23         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 1.03/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.03/1.23  thf('5', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['3', '4'])).
% 1.03/1.23  thf(t41_xboole_1, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.03/1.23       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.03/1.23  thf('6', plain,
% 1.03/1.23      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.03/1.23           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.03/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.03/1.23  thf('7', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.03/1.23           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.03/1.23      inference('sup+', [status(thm)], ['5', '6'])).
% 1.03/1.23  thf(t3_boole, axiom,
% 1.03/1.23    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.03/1.23  thf('8', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.03/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.23  thf(t36_xboole_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.03/1.23  thf('9', plain,
% 1.03/1.23      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 1.03/1.23      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.03/1.23  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.03/1.23      inference('sup+', [status(thm)], ['8', '9'])).
% 1.03/1.23  thf('11', plain,
% 1.03/1.23      (![X2 : $i, X4 : $i]:
% 1.03/1.23         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 1.03/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.03/1.23  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['10', '11'])).
% 1.03/1.23  thf('13', plain,
% 1.03/1.23      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 1.03/1.23      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.03/1.23  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.03/1.23      inference('sup+', [status(thm)], ['12', '13'])).
% 1.03/1.23  thf('15', plain,
% 1.03/1.23      (![X2 : $i, X4 : $i]:
% 1.03/1.23         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 1.03/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.03/1.23  thf('16', plain,
% 1.03/1.23      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('17', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.03/1.23      inference('demod', [status(thm)], ['7', '16'])).
% 1.03/1.23  thf('18', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 1.03/1.23      inference('sup+', [status(thm)], ['2', '17'])).
% 1.03/1.23  thf('19', plain,
% 1.03/1.23      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.03/1.23           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.03/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.03/1.23  thf('20', plain,
% 1.03/1.23      (![X2 : $i, X3 : $i]:
% 1.03/1.23         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 1.03/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.03/1.23  thf('21', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.23         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.03/1.23          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['19', '20'])).
% 1.03/1.23  thf('22', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         (((k1_xboole_0) != (k1_xboole_0))
% 1.03/1.23          | (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.03/1.23      inference('sup-', [status(thm)], ['18', '21'])).
% 1.03/1.23  thf('23', plain,
% 1.03/1.23      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 1.03/1.23      inference('simplify', [status(thm)], ['22'])).
% 1.03/1.23  thf('24', plain,
% 1.03/1.23      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 1.03/1.23      inference('sup+', [status(thm)], ['1', '23'])).
% 1.03/1.23  thf('25', plain,
% 1.03/1.23      (![X2 : $i, X4 : $i]:
% 1.03/1.23         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 1.03/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.03/1.23  thf('26', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) = (k1_xboole_0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['24', '25'])).
% 1.03/1.23  thf(t49_xboole_1, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.03/1.23       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.03/1.23  thf('27', plain,
% 1.03/1.23      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.03/1.23         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.03/1.23           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.03/1.23      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.03/1.23  thf('28', plain,
% 1.03/1.23      (![X15 : $i, X16 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.03/1.23           = (k3_xboole_0 @ X15 @ X16))),
% 1.03/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.03/1.23  thf('29', plain,
% 1.03/1.23      (![X15 : $i, X16 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.03/1.23           = (k3_xboole_0 @ X15 @ X16))),
% 1.03/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.03/1.23  thf('30', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.23           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.03/1.23      inference('sup+', [status(thm)], ['28', '29'])).
% 1.03/1.23  thf('31', plain,
% 1.03/1.23      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.03/1.23         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.03/1.23           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.03/1.23      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.03/1.23  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['10', '11'])).
% 1.03/1.23  thf('33', plain,
% 1.03/1.23      (![X15 : $i, X16 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.03/1.23           = (k3_xboole_0 @ X15 @ X16))),
% 1.03/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.03/1.23  thf('34', plain,
% 1.03/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.03/1.23      inference('sup+', [status(thm)], ['32', '33'])).
% 1.03/1.23  thf('35', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.03/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.23  thf('36', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.03/1.23      inference('demod', [status(thm)], ['34', '35'])).
% 1.03/1.23  thf('37', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.23           = (k4_xboole_0 @ X1 @ X0))),
% 1.03/1.23      inference('demod', [status(thm)], ['30', '31', '36'])).
% 1.03/1.23  thf('38', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.03/1.23           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.03/1.23      inference('sup+', [status(thm)], ['27', '37'])).
% 1.03/1.23  thf('39', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.03/1.23           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 1.03/1.23      inference('sup+', [status(thm)], ['26', '38'])).
% 1.03/1.23  thf('40', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.03/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.23  thf('41', plain,
% 1.03/1.23      (![X0 : $i]: ((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 1.03/1.23      inference('demod', [status(thm)], ['39', '40'])).
% 1.03/1.23  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['10', '11'])).
% 1.03/1.23  thf(t39_xboole_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.03/1.23  thf('43', plain,
% 1.03/1.23      (![X7 : $i, X8 : $i]:
% 1.03/1.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 1.03/1.23           = (k2_xboole_0 @ X7 @ X8))),
% 1.03/1.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.03/1.23  thf(t40_xboole_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.03/1.23  thf('44', plain,
% 1.03/1.23      (![X10 : $i, X11 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 1.03/1.23           = (k4_xboole_0 @ X10 @ X11))),
% 1.03/1.23      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.03/1.23  thf('45', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 1.03/1.23           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.23      inference('sup+', [status(thm)], ['43', '44'])).
% 1.03/1.23  thf('46', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 1.03/1.23           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.03/1.23      inference('sup+', [status(thm)], ['42', '45'])).
% 1.03/1.23  thf('47', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.03/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.23  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['10', '11'])).
% 1.03/1.23  thf('49', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.03/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.23  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.03/1.23      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 1.03/1.23  thf('51', plain,
% 1.03/1.23      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.03/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.03/1.23           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.03/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.03/1.23  thf(t83_xboole_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.03/1.23  thf('52', plain,
% 1.03/1.23      (![X20 : $i, X22 : $i]:
% 1.03/1.23         ((r1_xboole_0 @ X20 @ X22) | ((k4_xboole_0 @ X20 @ X22) != (X20)))),
% 1.03/1.23      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.03/1.23  thf('53', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.23         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.03/1.23            != (k4_xboole_0 @ X2 @ X1))
% 1.03/1.23          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['51', '52'])).
% 1.03/1.23  thf('54', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 1.03/1.23          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['50', '53'])).
% 1.03/1.23  thf('55', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.03/1.23      inference('simplify', [status(thm)], ['54'])).
% 1.03/1.23  thf('56', plain,
% 1.03/1.23      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['41', '55'])).
% 1.03/1.23  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 1.03/1.23  
% 1.03/1.23  % SZS output end Refutation
% 1.03/1.23  
% 1.09/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
