%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TdMtwiAJsH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:34 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 137 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  496 ( 998 expanded)
%              Number of equality atoms :   42 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['18','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['13','37'])).

thf('39',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['43','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TdMtwiAJsH
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.14/1.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.14/1.37  % Solved by: fo/fo7.sh
% 1.14/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.37  % done 1558 iterations in 0.916s
% 1.14/1.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.14/1.37  % SZS output start Refutation
% 1.14/1.37  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.14/1.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.14/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.37  thf(sk_C_type, type, sk_C: $i).
% 1.14/1.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.14/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.37  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.14/1.37  thf(t106_xboole_1, conjecture,
% 1.14/1.37    (![A:$i,B:$i,C:$i]:
% 1.14/1.37     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.14/1.37       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.14/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.37    (~( ![A:$i,B:$i,C:$i]:
% 1.14/1.37        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.14/1.37          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 1.14/1.37    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 1.14/1.37  thf('0', plain,
% 1.14/1.37      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf('1', plain,
% 1.14/1.37      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 1.14/1.37      inference('split', [status(esa)], ['0'])).
% 1.14/1.37  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.14/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.37  thf(t28_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]:
% 1.14/1.37     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.14/1.37  thf('3', plain,
% 1.14/1.37      (![X10 : $i, X11 : $i]:
% 1.14/1.37         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.14/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.14/1.37  thf('4', plain,
% 1.14/1.37      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 1.14/1.37      inference('sup-', [status(thm)], ['2', '3'])).
% 1.14/1.37  thf(commutativity_k3_xboole_0, axiom,
% 1.14/1.37    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.14/1.37  thf('5', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.37  thf(t100_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]:
% 1.14/1.37     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.14/1.37  thf('6', plain,
% 1.14/1.37      (![X5 : $i, X6 : $i]:
% 1.14/1.37         ((k4_xboole_0 @ X5 @ X6)
% 1.14/1.37           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.14/1.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.14/1.37  thf('7', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         ((k4_xboole_0 @ X0 @ X1)
% 1.14/1.37           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.14/1.37      inference('sup+', [status(thm)], ['5', '6'])).
% 1.14/1.37  thf('8', plain,
% 1.14/1.37      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 1.14/1.37         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 1.14/1.37      inference('sup+', [status(thm)], ['4', '7'])).
% 1.14/1.37  thf(t48_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]:
% 1.14/1.37     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.14/1.37  thf('9', plain,
% 1.14/1.37      (![X14 : $i, X15 : $i]:
% 1.14/1.37         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.14/1.37           = (k3_xboole_0 @ X14 @ X15))),
% 1.14/1.37      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.14/1.37  thf('10', plain,
% 1.14/1.37      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 1.14/1.37         (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 1.14/1.37         = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 1.14/1.37      inference('sup+', [status(thm)], ['8', '9'])).
% 1.14/1.37  thf('11', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.37  thf('12', plain,
% 1.14/1.37      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 1.14/1.37      inference('sup-', [status(thm)], ['2', '3'])).
% 1.14/1.37  thf('13', plain,
% 1.14/1.37      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 1.14/1.37         (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)) = (sk_A))),
% 1.14/1.37      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.14/1.37  thf(t36_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.14/1.37  thf('14', plain,
% 1.14/1.37      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.14/1.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.14/1.37  thf('15', plain,
% 1.14/1.37      (![X10 : $i, X11 : $i]:
% 1.14/1.37         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.14/1.37      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.14/1.37  thf('16', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.14/1.37           = (k4_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('sup-', [status(thm)], ['14', '15'])).
% 1.14/1.37  thf('17', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.37  thf('18', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.14/1.37           = (k4_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('demod', [status(thm)], ['16', '17'])).
% 1.14/1.37  thf(t79_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.14/1.37  thf('19', plain,
% 1.14/1.37      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 1.14/1.37      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.14/1.37  thf(d7_xboole_0, axiom,
% 1.14/1.37    (![A:$i,B:$i]:
% 1.14/1.37     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.14/1.37       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.14/1.37  thf('20', plain,
% 1.14/1.37      (![X2 : $i, X3 : $i]:
% 1.14/1.37         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.14/1.37      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.14/1.37  thf('21', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.14/1.37      inference('sup-', [status(thm)], ['19', '20'])).
% 1.14/1.37  thf('22', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.37  thf('23', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.14/1.37      inference('demod', [status(thm)], ['21', '22'])).
% 1.14/1.37  thf(t16_xboole_1, axiom,
% 1.14/1.37    (![A:$i,B:$i,C:$i]:
% 1.14/1.37     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.14/1.37       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.14/1.37  thf('24', plain,
% 1.14/1.37      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 1.14/1.37           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.14/1.37      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.14/1.37  thf('25', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 1.14/1.37           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 1.14/1.37      inference('sup+', [status(thm)], ['23', '24'])).
% 1.14/1.37  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.14/1.37  thf('26', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 1.14/1.37      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.14/1.37  thf('27', plain,
% 1.14/1.37      (![X2 : $i, X3 : $i]:
% 1.14/1.37         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.14/1.37      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.14/1.37  thf('28', plain,
% 1.14/1.37      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.37      inference('sup-', [status(thm)], ['26', '27'])).
% 1.14/1.37  thf('29', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.37  thf('30', plain,
% 1.14/1.37      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.14/1.37      inference('sup+', [status(thm)], ['28', '29'])).
% 1.14/1.37  thf('31', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.37         ((k1_xboole_0)
% 1.14/1.37           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 1.14/1.37      inference('demod', [status(thm)], ['25', '30'])).
% 1.14/1.37  thf('32', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.37  thf('33', plain,
% 1.14/1.37      (![X2 : $i, X4 : $i]:
% 1.14/1.37         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.14/1.37      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.14/1.37  thf('34', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('sup-', [status(thm)], ['32', '33'])).
% 1.14/1.37  thf('35', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.37         (((k1_xboole_0) != (k1_xboole_0))
% 1.14/1.37          | (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1))),
% 1.14/1.37      inference('sup-', [status(thm)], ['31', '34'])).
% 1.14/1.37  thf('36', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.37         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1)),
% 1.14/1.37      inference('simplify', [status(thm)], ['35'])).
% 1.14/1.37  thf('37', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.37         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X1)),
% 1.14/1.37      inference('sup+', [status(thm)], ['18', '36'])).
% 1.14/1.37  thf('38', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.14/1.37      inference('sup+', [status(thm)], ['13', '37'])).
% 1.14/1.37  thf('39', plain,
% 1.14/1.37      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.14/1.37      inference('split', [status(esa)], ['0'])).
% 1.14/1.37  thf('40', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 1.14/1.37      inference('sup-', [status(thm)], ['38', '39'])).
% 1.14/1.37  thf('41', plain,
% 1.14/1.37      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 1.14/1.37      inference('split', [status(esa)], ['0'])).
% 1.14/1.37  thf('42', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 1.14/1.37      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 1.14/1.37  thf('43', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.14/1.37      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 1.14/1.37  thf('44', plain,
% 1.14/1.37      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 1.14/1.37         (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)) = (sk_A))),
% 1.14/1.37      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.14/1.37  thf('45', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.14/1.37           = (k4_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('demod', [status(thm)], ['16', '17'])).
% 1.14/1.37  thf('46', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.14/1.37           = (k4_xboole_0 @ X0 @ X1))),
% 1.14/1.37      inference('demod', [status(thm)], ['16', '17'])).
% 1.14/1.37  thf('47', plain,
% 1.14/1.37      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 1.14/1.37           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.14/1.37      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.14/1.37  thf('48', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.37         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.14/1.37           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.14/1.37      inference('sup+', [status(thm)], ['46', '47'])).
% 1.14/1.37  thf('49', plain,
% 1.14/1.37      (![X14 : $i, X15 : $i]:
% 1.14/1.37         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.14/1.37           = (k3_xboole_0 @ X14 @ X15))),
% 1.14/1.37      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.14/1.37  thf('50', plain,
% 1.14/1.37      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.14/1.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.14/1.37  thf('51', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.14/1.37      inference('sup+', [status(thm)], ['49', '50'])).
% 1.14/1.37  thf('52', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.37         (r1_tarski @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 1.14/1.37      inference('sup+', [status(thm)], ['48', '51'])).
% 1.14/1.37  thf('53', plain,
% 1.14/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.37         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 1.14/1.37      inference('sup+', [status(thm)], ['45', '52'])).
% 1.14/1.37  thf('54', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.14/1.37      inference('sup+', [status(thm)], ['44', '53'])).
% 1.14/1.37  thf('55', plain, ($false), inference('demod', [status(thm)], ['43', '54'])).
% 1.14/1.37  
% 1.14/1.37  % SZS output end Refutation
% 1.14/1.37  
% 1.14/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
