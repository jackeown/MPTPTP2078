%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eKvaKz8eKF

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:57 EST 2020

% Result     : Theorem 14.91s
% Output     : Refutation 14.91s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 108 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  600 ( 887 expanded)
%              Number of equality atoms :   60 (  85 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t94_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

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
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','50','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eKvaKz8eKF
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 14.91/15.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.91/15.16  % Solved by: fo/fo7.sh
% 14.91/15.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.91/15.16  % done 6658 iterations in 14.691s
% 14.91/15.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.91/15.16  % SZS output start Refutation
% 14.91/15.16  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 14.91/15.16  thf(sk_A_type, type, sk_A: $i).
% 14.91/15.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 14.91/15.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.91/15.16  thf(sk_B_type, type, sk_B: $i).
% 14.91/15.16  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 14.91/15.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.91/15.16  thf(t94_xboole_1, conjecture,
% 14.91/15.16    (![A:$i,B:$i]:
% 14.91/15.16     ( ( k2_xboole_0 @ A @ B ) =
% 14.91/15.16       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.91/15.16  thf(zf_stmt_0, negated_conjecture,
% 14.91/15.16    (~( ![A:$i,B:$i]:
% 14.91/15.16        ( ( k2_xboole_0 @ A @ B ) =
% 14.91/15.16          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 14.91/15.16    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 14.91/15.16  thf('0', plain,
% 14.91/15.16      (((k2_xboole_0 @ sk_A @ sk_B)
% 14.91/15.16         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 14.91/15.16             (k3_xboole_0 @ sk_A @ sk_B)))),
% 14.91/15.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.91/15.16  thf(d6_xboole_0, axiom,
% 14.91/15.16    (![A:$i,B:$i]:
% 14.91/15.16     ( ( k5_xboole_0 @ A @ B ) =
% 14.91/15.16       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 14.91/15.16  thf('1', plain,
% 14.91/15.16      (![X2 : $i, X3 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ X2 @ X3)
% 14.91/15.16           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.91/15.16      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.91/15.16  thf(commutativity_k2_xboole_0, axiom,
% 14.91/15.16    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 14.91/15.16  thf('2', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.91/15.16      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.91/15.16  thf('3', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k5_xboole_0 @ X1 @ X0))),
% 14.91/15.16      inference('sup+', [status(thm)], ['1', '2'])).
% 14.91/15.16  thf('4', plain,
% 14.91/15.16      (![X2 : $i, X3 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ X2 @ X3)
% 14.91/15.16           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.91/15.16      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.91/15.16  thf('5', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 14.91/15.16      inference('sup+', [status(thm)], ['3', '4'])).
% 14.91/15.16  thf('6', plain,
% 14.91/15.16      (![X2 : $i, X3 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ X2 @ X3)
% 14.91/15.16           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.91/15.16      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.91/15.16  thf(t79_xboole_1, axiom,
% 14.91/15.16    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 14.91/15.16  thf('7', plain,
% 14.91/15.16      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 14.91/15.16      inference('cnf', [status(esa)], [t79_xboole_1])).
% 14.91/15.16  thf(symmetry_r1_xboole_0, axiom,
% 14.91/15.16    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 14.91/15.16  thf('8', plain,
% 14.91/15.16      (![X4 : $i, X5 : $i]:
% 14.91/15.16         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 14.91/15.16      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 14.91/15.16  thf('9', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 14.91/15.16      inference('sup-', [status(thm)], ['7', '8'])).
% 14.91/15.16  thf(t83_xboole_1, axiom,
% 14.91/15.16    (![A:$i,B:$i]:
% 14.91/15.16     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 14.91/15.16  thf('10', plain,
% 14.91/15.16      (![X20 : $i, X21 : $i]:
% 14.91/15.16         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 14.91/15.16      inference('cnf', [status(esa)], [t83_xboole_1])).
% 14.91/15.16  thf('11', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 14.91/15.16      inference('sup-', [status(thm)], ['9', '10'])).
% 14.91/15.16  thf(t41_xboole_1, axiom,
% 14.91/15.16    (![A:$i,B:$i,C:$i]:
% 14.91/15.16     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 14.91/15.16       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 14.91/15.16  thf('12', plain,
% 14.91/15.16      (![X8 : $i, X9 : $i, X10 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 14.91/15.16           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 14.91/15.16      inference('cnf', [status(esa)], [t41_xboole_1])).
% 14.91/15.16  thf('13', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X0 @ X1)
% 14.91/15.16           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 14.91/15.16      inference('sup+', [status(thm)], ['11', '12'])).
% 14.91/15.16  thf('14', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 14.91/15.16           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.91/15.16      inference('sup+', [status(thm)], ['6', '13'])).
% 14.91/15.16  thf(t48_xboole_1, axiom,
% 14.91/15.16    (![A:$i,B:$i]:
% 14.91/15.16     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 14.91/15.16  thf('15', plain,
% 14.91/15.16      (![X11 : $i, X12 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 14.91/15.16           = (k3_xboole_0 @ X11 @ X12))),
% 14.91/15.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.91/15.16  thf('16', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k3_xboole_0 @ X0 @ X1))),
% 14.91/15.16      inference('sup+', [status(thm)], ['14', '15'])).
% 14.91/15.16  thf('17', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k3_xboole_0 @ X1 @ X0))),
% 14.91/15.16      inference('sup+', [status(thm)], ['5', '16'])).
% 14.91/15.16  thf('18', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 14.91/15.16      inference('sup-', [status(thm)], ['9', '10'])).
% 14.91/15.16  thf('19', plain,
% 14.91/15.16      (![X2 : $i, X3 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ X2 @ X3)
% 14.91/15.16           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.91/15.16      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.91/15.16  thf('20', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 14.91/15.16      inference('sup+', [status(thm)], ['18', '19'])).
% 14.91/15.16  thf(t39_xboole_1, axiom,
% 14.91/15.16    (![A:$i,B:$i]:
% 14.91/15.16     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 14.91/15.16  thf('21', plain,
% 14.91/15.16      (![X6 : $i, X7 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 14.91/15.16           = (k2_xboole_0 @ X6 @ X7))),
% 14.91/15.16      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.91/15.16  thf('22', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 14.91/15.16      inference('demod', [status(thm)], ['20', '21'])).
% 14.91/15.16  thf('23', plain,
% 14.91/15.16      (![X6 : $i, X7 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 14.91/15.16           = (k2_xboole_0 @ X6 @ X7))),
% 14.91/15.16      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.91/15.16  thf('24', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k2_xboole_0 @ X0 @ X1))),
% 14.91/15.16      inference('sup+', [status(thm)], ['22', '23'])).
% 14.91/15.16  thf('25', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 14.91/15.16      inference('sup+', [status(thm)], ['17', '24'])).
% 14.91/15.16  thf('26', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.91/15.16      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.91/15.16  thf('27', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 14.91/15.16      inference('sup+', [status(thm)], ['3', '4'])).
% 14.91/15.16  thf(t4_xboole_1, axiom,
% 14.91/15.16    (![A:$i,B:$i,C:$i]:
% 14.91/15.16     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 14.91/15.16       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 14.91/15.16  thf('28', plain,
% 14.91/15.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 14.91/15.16           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 14.91/15.16      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.91/15.16  thf('29', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.91/15.16      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.91/15.16  thf('30', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 14.91/15.16           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.91/15.16      inference('sup+', [status(thm)], ['28', '29'])).
% 14.91/15.16  thf('31', plain,
% 14.91/15.16      (![X2 : $i, X3 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ X2 @ X3)
% 14.91/15.16           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.91/15.16      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.91/15.16  thf('32', plain,
% 14.91/15.16      (![X6 : $i, X7 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 14.91/15.16           = (k2_xboole_0 @ X6 @ X7))),
% 14.91/15.16      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.91/15.16  thf('33', plain,
% 14.91/15.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 14.91/15.16           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 14.91/15.16      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.91/15.16  thf('34', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 14.91/15.16           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 14.91/15.16      inference('sup+', [status(thm)], ['32', '33'])).
% 14.91/15.16  thf('35', plain,
% 14.91/15.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 14.91/15.16           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 14.91/15.16      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.91/15.16  thf('36', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 14.91/15.16           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 14.91/15.16      inference('demod', [status(thm)], ['34', '35'])).
% 14.91/15.16  thf('37', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 14.91/15.16           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.91/15.16      inference('sup+', [status(thm)], ['31', '36'])).
% 14.91/15.16  thf('38', plain,
% 14.91/15.16      (![X6 : $i, X7 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 14.91/15.16           = (k2_xboole_0 @ X6 @ X7))),
% 14.91/15.16      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.91/15.16  thf('39', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.91/15.16      inference('demod', [status(thm)], ['37', '38'])).
% 14.91/15.16  thf('40', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 14.91/15.16           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.91/15.16      inference('sup+', [status(thm)], ['30', '39'])).
% 14.91/15.16  thf('41', plain,
% 14.91/15.16      (![X11 : $i, X12 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 14.91/15.16           = (k3_xboole_0 @ X11 @ X12))),
% 14.91/15.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.91/15.16  thf('42', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 14.91/15.16      inference('sup-', [status(thm)], ['9', '10'])).
% 14.91/15.16  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 14.91/15.16      inference('sup+', [status(thm)], ['41', '42'])).
% 14.91/15.16  thf(t51_xboole_1, axiom,
% 14.91/15.16    (![A:$i,B:$i]:
% 14.91/15.16     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 14.91/15.16       ( A ) ))).
% 14.91/15.16  thf('44', plain,
% 14.91/15.16      (![X16 : $i, X17 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 14.91/15.16           = (X16))),
% 14.91/15.16      inference('cnf', [status(esa)], [t51_xboole_1])).
% 14.91/15.16  thf('45', plain,
% 14.91/15.16      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 14.91/15.16      inference('sup+', [status(thm)], ['43', '44'])).
% 14.91/15.16  thf('46', plain,
% 14.91/15.16      (![X6 : $i, X7 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 14.91/15.16           = (k2_xboole_0 @ X6 @ X7))),
% 14.91/15.16      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.91/15.16  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 14.91/15.16      inference('demod', [status(thm)], ['45', '46'])).
% 14.91/15.16  thf('48', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X1 @ X0)
% 14.91/15.16           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.91/15.16      inference('demod', [status(thm)], ['40', '47'])).
% 14.91/15.16  thf('49', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k2_xboole_0 @ X0 @ X1)
% 14.91/15.16           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.91/15.16      inference('sup+', [status(thm)], ['27', '48'])).
% 14.91/15.16  thf('50', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]:
% 14.91/15.16         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 14.91/15.16           = (k2_xboole_0 @ X0 @ X1))),
% 14.91/15.16      inference('demod', [status(thm)], ['25', '26', '49'])).
% 14.91/15.16  thf('51', plain,
% 14.91/15.16      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.91/15.16      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.91/15.16  thf('52', plain,
% 14.91/15.16      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 14.91/15.16      inference('demod', [status(thm)], ['0', '50', '51'])).
% 14.91/15.16  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 14.91/15.16  
% 14.91/15.16  % SZS output end Refutation
% 14.91/15.16  
% 14.91/15.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
