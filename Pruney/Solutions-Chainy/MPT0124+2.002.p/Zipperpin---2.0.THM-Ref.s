%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W7pctVMtMd

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  96 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  478 ( 784 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t117_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ C @ B )
     => ( ( k4_xboole_0 @ A @ C )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ C @ B )
       => ( ( k4_xboole_0 @ A @ C )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf('5',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('7',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k2_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['16','40'])).

thf('42',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['4','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W7pctVMtMd
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 114 iterations in 0.077s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(t117_xboole_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ C @ B ) =>
% 0.20/0.53       ( ( k4_xboole_0 @ A @ C ) =
% 0.20/0.53         ( k2_xboole_0 @
% 0.20/0.53           ( k4_xboole_0 @ A @ B ) @ 
% 0.20/0.53           ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( r1_tarski @ C @ B ) =>
% 0.20/0.53          ( ( k4_xboole_0 @ A @ C ) =
% 0.20/0.53            ( k2_xboole_0 @
% 0.20/0.53              ( k4_xboole_0 @ A @ B ) @ 
% 0.20/0.53              ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t117_xboole_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.20/0.53         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.53             (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t52_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.20/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ 
% 0.20/0.53              (k3_xboole_0 @ X17 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.20/0.53  thf(t48_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.53           = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.20/0.53         != (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.20/0.53  thf('5', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t45_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.53       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((X14) = (k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))
% 0.20/0.53          | ~ (r1_tarski @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (((sk_B) = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(t39_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.20/0.53           = (k2_xboole_0 @ X6 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.53  thf('9', plain, (((sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.20/0.53           = (k2_xboole_0 @ X6 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.53  thf(t40_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.20/0.53           = (k4_xboole_0 @ X8 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.53           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.20/0.53         = (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['9', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.53           = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_C @ sk_B)
% 0.20/0.53         = (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.53           = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.20/0.53           = (k4_xboole_0 @ X8 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.20/0.53           = (k2_xboole_0 @ X6 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.20/0.53              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.20/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ 
% 0.20/0.53              (k3_xboole_0 @ X17 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.20/0.53  thf(t36_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((X14) = (k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))
% 0.20/0.53          | ~ (r1_tarski @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.20/0.53           = (k2_xboole_0 @ X6 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((X14) = (k2_xboole_0 @ X13 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.20/0.53           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22', '29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.53           = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('35', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.20/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ 
% 0.20/0.53              (k3_xboole_0 @ X17 @ X19)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.53           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.53  thf('41', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((k4_xboole_0 @ sk_A @ sk_C) != (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '41'])).
% 0.20/0.53  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
