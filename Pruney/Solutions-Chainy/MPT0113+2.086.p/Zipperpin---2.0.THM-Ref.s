%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zqFuEuxuhx

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:40 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   69 (  97 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  388 ( 615 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('22',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['19','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zqFuEuxuhx
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 381 iterations in 0.137s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(t106_xboole_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.39/0.59       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.59        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.39/0.59          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf(t79_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.39/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.39/0.59  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('5', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(l32_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X2 : $i, X4 : $i]:
% 0.39/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.59  thf(t84_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.39/0.59          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X19 @ X20)
% 0.39/0.59          | ~ (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.39/0.59          | ~ (r1_xboole_0 @ X19 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.39/0.59          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.39/0.59          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.39/0.59  thf('10', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.39/0.59          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('12', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.39/0.59      inference('sup-', [status(thm)], ['4', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.59  thf('14', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('16', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('18', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('19', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.39/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.39/0.59  thf(t36_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.39/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X2 : $i, X4 : $i]:
% 0.39/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X19 @ X20)
% 0.39/0.59          | ~ (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.39/0.59          | ~ (r1_xboole_0 @ X19 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ X2 @ k1_xboole_0)
% 0.39/0.59          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.39/0.59          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.59  thf('26', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ X2 @ X0)
% 0.39/0.59          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.39/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2))),
% 0.39/0.59      inference('sup-', [status(thm)], ['20', '27'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.39/0.59          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.39/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf(t83_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i]:
% 0.39/0.59         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.59  thf(t48_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.39/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.59  thf('36', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.39/0.59  thf(t47_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.39/0.59           = (k4_xboole_0 @ X9 @ X10))),
% 0.39/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['36', '37'])).
% 0.39/0.59  thf(t3_boole, axiom,
% 0.39/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.59  thf('39', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.39/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.59  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.39/0.59      inference('sup+', [status(thm)], ['39', '40'])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (![X2 : $i, X4 : $i]:
% 0.39/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.59  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('44', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['38', '43'])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      (![X2 : $i, X3 : $i]:
% 0.39/0.59         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.39/0.59  thf('47', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.59      inference('simplify', [status(thm)], ['46'])).
% 0.39/0.59  thf('48', plain, ($false), inference('demod', [status(thm)], ['19', '47'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
