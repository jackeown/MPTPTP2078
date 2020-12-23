%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZMnKT2GDVz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:17 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 160 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  558 (1111 expanded)
%              Number of equality atoms :   64 ( 136 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('44',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','35','42','43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','51'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','54','55'])).

thf('57',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZMnKT2GDVz
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.72  % Solved by: fo/fo7.sh
% 0.43/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.72  % done 635 iterations in 0.264s
% 0.43/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.72  % SZS output start Refutation
% 0.43/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.72  thf(t100_xboole_1, conjecture,
% 0.43/0.72    (![A:$i,B:$i]:
% 0.43/0.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.72    (~( ![A:$i,B:$i]:
% 0.43/0.72        ( ( k4_xboole_0 @ A @ B ) =
% 0.43/0.72          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.43/0.72    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.43/0.72  thf('0', plain,
% 0.43/0.72      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.43/0.72         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.72  thf(t47_xboole_1, axiom,
% 0.43/0.72    (![A:$i,B:$i]:
% 0.43/0.72     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.43/0.72  thf('1', plain,
% 0.43/0.72      (![X10 : $i, X11 : $i]:
% 0.43/0.72         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.43/0.72           = (k4_xboole_0 @ X10 @ X11))),
% 0.43/0.72      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.43/0.72  thf(d6_xboole_0, axiom,
% 0.43/0.72    (![A:$i,B:$i]:
% 0.43/0.72     ( ( k5_xboole_0 @ A @ B ) =
% 0.43/0.72       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.43/0.72  thf('2', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X0 @ X1)
% 0.43/0.72           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.43/0.72  thf('3', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.43/0.72           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.43/0.72              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.43/0.72      inference('sup+', [status(thm)], ['1', '2'])).
% 0.43/0.72  thf(t79_xboole_1, axiom,
% 0.43/0.72    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.43/0.72  thf('4', plain,
% 0.43/0.72      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.43/0.72      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.72  thf(symmetry_r1_xboole_0, axiom,
% 0.43/0.72    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.43/0.72  thf('5', plain,
% 0.43/0.72      (![X2 : $i, X3 : $i]:
% 0.43/0.72         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.43/0.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.43/0.72  thf('6', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.72  thf(t88_xboole_1, axiom,
% 0.43/0.72    (![A:$i,B:$i]:
% 0.43/0.72     ( ( r1_xboole_0 @ A @ B ) =>
% 0.43/0.72       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.43/0.72  thf('7', plain,
% 0.43/0.72      (![X22 : $i, X23 : $i]:
% 0.43/0.72         (((k4_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X23) = (X22))
% 0.43/0.72          | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.43/0.72      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.43/0.72  thf(t40_xboole_1, axiom,
% 0.43/0.72    (![A:$i,B:$i]:
% 0.43/0.72     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.43/0.72  thf('8', plain,
% 0.43/0.72      (![X8 : $i, X9 : $i]:
% 0.43/0.72         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.43/0.72           = (k4_xboole_0 @ X8 @ X9))),
% 0.43/0.72      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.43/0.72  thf('9', plain,
% 0.43/0.72      (![X22 : $i, X23 : $i]:
% 0.43/0.72         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.43/0.72      inference('demod', [status(thm)], ['7', '8'])).
% 0.43/0.72  thf('10', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.43/0.72      inference('sup-', [status(thm)], ['6', '9'])).
% 0.43/0.72  thf('11', plain,
% 0.43/0.72      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.43/0.72      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.72  thf('12', plain,
% 0.43/0.72      (![X22 : $i, X23 : $i]:
% 0.43/0.72         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.43/0.72      inference('demod', [status(thm)], ['7', '8'])).
% 0.43/0.72  thf('13', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.43/0.72           = (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.72  thf(t48_xboole_1, axiom,
% 0.43/0.72    (![A:$i,B:$i]:
% 0.43/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.43/0.72  thf('14', plain,
% 0.43/0.72      (![X12 : $i, X13 : $i]:
% 0.43/0.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.43/0.72           = (k3_xboole_0 @ X12 @ X13))),
% 0.43/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.72  thf('15', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X0 @ X1)
% 0.43/0.72           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.43/0.72  thf('16', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.43/0.72           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.43/0.72              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 0.43/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.43/0.72  thf('17', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.43/0.72           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 0.43/0.72           = (k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ 
% 0.43/0.72              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 0.43/0.72      inference('sup+', [status(thm)], ['13', '16'])).
% 0.43/0.72  thf('18', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.43/0.72           = (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.72  thf(t3_boole, axiom,
% 0.43/0.72    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.72  thf('19', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.43/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.72  thf('20', plain,
% 0.43/0.72      (![X12 : $i, X13 : $i]:
% 0.43/0.72         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.43/0.72           = (k3_xboole_0 @ X12 @ X13))),
% 0.43/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.72  thf('21', plain,
% 0.43/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.72      inference('sup+', [status(thm)], ['19', '20'])).
% 0.43/0.72  thf(t2_boole, axiom,
% 0.43/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.43/0.72  thf('22', plain,
% 0.43/0.72      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.43/0.72  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.72      inference('demod', [status(thm)], ['21', '22'])).
% 0.43/0.72  thf('24', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X0 @ X1)
% 0.43/0.72           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.43/0.72  thf('25', plain,
% 0.43/0.72      (![X0 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X0 @ X0)
% 0.43/0.72           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.43/0.72      inference('sup+', [status(thm)], ['23', '24'])).
% 0.43/0.72  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.72      inference('demod', [status(thm)], ['21', '22'])).
% 0.43/0.72  thf('27', plain,
% 0.43/0.72      (![X0 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.43/0.72      inference('demod', [status(thm)], ['25', '26'])).
% 0.43/0.72  thf('28', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.43/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.72  thf('29', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.43/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.72  thf('30', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X0 @ X1)
% 0.43/0.72           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.43/0.72  thf('31', plain,
% 0.43/0.72      (![X0 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.43/0.72           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.43/0.72      inference('sup+', [status(thm)], ['29', '30'])).
% 0.43/0.72  thf(t5_boole, axiom,
% 0.43/0.72    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.72  thf('32', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.43/0.72      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.72  thf('33', plain,
% 0.43/0.72      (![X0 : $i]:
% 0.43/0.72         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.43/0.72      inference('demod', [status(thm)], ['31', '32'])).
% 0.43/0.72  thf('34', plain,
% 0.43/0.72      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.43/0.72      inference('sup+', [status(thm)], ['28', '33'])).
% 0.43/0.72  thf('35', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.72      inference('demod', [status(thm)], ['27', '34'])).
% 0.43/0.72  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.72      inference('demod', [status(thm)], ['21', '22'])).
% 0.43/0.72  thf(t98_xboole_1, axiom,
% 0.43/0.72    (![A:$i,B:$i]:
% 0.43/0.72     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.43/0.72  thf('37', plain,
% 0.43/0.72      (![X24 : $i, X25 : $i]:
% 0.43/0.72         ((k2_xboole_0 @ X24 @ X25)
% 0.43/0.72           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 0.43/0.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.43/0.72  thf('38', plain,
% 0.43/0.72      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.72      inference('sup+', [status(thm)], ['36', '37'])).
% 0.43/0.72  thf('39', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.43/0.72      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.72  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.43/0.72      inference('demod', [status(thm)], ['38', '39'])).
% 0.43/0.72  thf('41', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X0 @ X1)
% 0.43/0.72           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.43/0.72  thf('42', plain,
% 0.43/0.72      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.43/0.72      inference('sup+', [status(thm)], ['40', '41'])).
% 0.43/0.72  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.72      inference('demod', [status(thm)], ['27', '34'])).
% 0.43/0.72  thf('44', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.43/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.72  thf('45', plain,
% 0.43/0.72      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.43/0.72      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.72  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.43/0.72      inference('sup+', [status(thm)], ['44', '45'])).
% 0.43/0.72  thf('47', plain,
% 0.43/0.72      (![X22 : $i, X23 : $i]:
% 0.43/0.72         (((k4_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X23) = (X22))
% 0.43/0.72          | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.43/0.72      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.43/0.72  thf('48', plain,
% 0.43/0.72      (![X0 : $i]:
% 0.43/0.72         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.43/0.72      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.72  thf('49', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.43/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.72  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.72      inference('demod', [status(thm)], ['48', '49'])).
% 0.43/0.72  thf('51', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.43/0.72      inference('demod', [status(thm)], ['17', '18', '35', '42', '43', '50'])).
% 0.43/0.72  thf('52', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.72      inference('sup+', [status(thm)], ['10', '51'])).
% 0.43/0.72  thf(t49_xboole_1, axiom,
% 0.43/0.72    (![A:$i,B:$i,C:$i]:
% 0.43/0.72     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.43/0.72       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.43/0.72  thf('53', plain,
% 0.43/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.72         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.43/0.72           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.43/0.72      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.43/0.72  thf('54', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.43/0.72      inference('demod', [status(thm)], ['52', '53'])).
% 0.43/0.72  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.72      inference('demod', [status(thm)], ['48', '49'])).
% 0.43/0.72  thf('56', plain,
% 0.43/0.72      (![X0 : $i, X1 : $i]:
% 0.43/0.72         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.43/0.72           = (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.72      inference('demod', [status(thm)], ['3', '54', '55'])).
% 0.43/0.72  thf('57', plain,
% 0.43/0.72      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.72      inference('demod', [status(thm)], ['0', '56'])).
% 0.43/0.72  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.43/0.72  
% 0.43/0.72  % SZS output end Refutation
% 0.43/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
