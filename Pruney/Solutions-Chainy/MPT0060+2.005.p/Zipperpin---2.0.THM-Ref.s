%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EVOaHeGx7h

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:21 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 135 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  602 (1042 expanded)
%              Number of equality atoms :   67 ( 127 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t53_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','31','32','33','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','50','51','52'])).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EVOaHeGx7h
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:23:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 344 iterations in 0.151s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(t53_xboole_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.41/0.59       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.59        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.41/0.59          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t53_xboole_1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.41/0.59         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.41/0.59             (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t49_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.41/0.59       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.41/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.41/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.41/0.59         != (k4_xboole_0 @ 
% 0.41/0.59             (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A) @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf(t3_boole, axiom,
% 0.41/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.59  thf('3', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.41/0.59  thf(t48_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.41/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.41/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.59  thf(t1_boole, axiom,
% 0.41/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.59  thf('8', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.59  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf(t40_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.41/0.59           = (k4_xboole_0 @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.59           = (k3_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['6', '13'])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.59           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.59           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['5', '16'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.41/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf(t39_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.41/0.59           = (k2_xboole_0 @ X3 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.41/0.59           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.41/0.59           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0))
% 0.41/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.41/0.59              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['17', '23'])).
% 0.41/0.59  thf(t41_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.59           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.59  thf('26', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf(t51_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.41/0.59       ( A ) ))).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X16 : $i, X17 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.41/0.59           = (X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.41/0.59           (k3_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.41/0.59           (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['27', '30'])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.59           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.59  thf('33', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X16 : $i, X17 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.41/0.59           = (X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.41/0.59           (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.59  thf('37', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.41/0.59           = (k2_xboole_0 @ X3 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.41/0.59  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.41/0.59  thf('41', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.41/0.59      inference('demod', [status(thm)],
% 0.41/0.59                ['24', '25', '26', '31', '32', '33', '40'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.41/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.59           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.41/0.59           = (k4_xboole_0 @ X2 @ 
% 0.41/0.59              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.59           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.41/0.59           = (k4_xboole_0 @ X2 @ 
% 0.41/0.59              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.41/0.59      inference('demod', [status(thm)], ['44', '45'])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 0.41/0.59           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.41/0.59              (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['41', '46'])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.41/0.59           = (k4_xboole_0 @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.41/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf('51', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.41/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.41/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('demod', [status(thm)], ['47', '50', '51', '52'])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.41/0.59           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.41/0.59         != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '53', '54'])).
% 0.41/0.59  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
