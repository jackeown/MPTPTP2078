%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1PVQSJhei4

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:14 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   58 (  67 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  366 ( 433 expanded)
%              Number of equality atoms :   42 (  51 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['4','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('29',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('30',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 = X37 )
      | ~ ( r1_tarski @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('31',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1PVQSJhei4
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:43:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 405 iterations in 0.125s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(t13_zfmisc_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.58         ( k1_tarski @ A ) ) =>
% 0.38/0.58       ( ( A ) = ( B ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i]:
% 0.38/0.58        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.58            ( k1_tarski @ A ) ) =>
% 0.38/0.58          ( ( A ) = ( B ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.38/0.58         = (k1_tarski @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(idempotence_k3_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.58  thf('1', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.58  thf(t23_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.38/0.58       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 0.38/0.58           = (k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ 
% 0.38/0.58              (k3_xboole_0 @ X12 @ X14)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.38/0.58           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf(t17_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.38/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.38/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf(t28_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.38/0.58           = (k3_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.58           = (k3_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf(t51_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.38/0.58       ( A ) ))).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.38/0.58           = (X19))),
% 0.38/0.58      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.38/0.58           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))) = (X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf(t98_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ X29 @ X30)
% 0.38/0.58           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.58  thf(t94_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k2_xboole_0 @ A @ B ) =
% 0.38/0.58       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X27 : $i, X28 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ X27 @ X28)
% 0.38/0.58           = (k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 0.38/0.58              (k3_xboole_0 @ X27 @ X28)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 0.38/0.58           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.38/0.58              (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf(t79_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 0.38/0.58      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.38/0.58  thf(d7_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.38/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.58  thf(t5_boole, axiom,
% 0.38/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.58  thf('22', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.38/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 0.38/0.58           = (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['16', '21', '22'])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['13', '23'])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.38/0.58      inference('sup+', [status(thm)], ['4', '24'])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['3', '25'])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.38/0.58         = (k1_tarski @ sk_B))),
% 0.38/0.58      inference('sup+', [status(thm)], ['0', '26'])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.38/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf('29', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.38/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf(t6_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.38/0.58       ( ( A ) = ( B ) ) ))).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X37 : $i, X38 : $i]:
% 0.38/0.58         (((X38) = (X37))
% 0.38/0.58          | ~ (r1_tarski @ (k1_tarski @ X38) @ (k1_tarski @ X37)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.38/0.58  thf('31', plain, (((sk_B) = (sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.58  thf('32', plain, (((sk_A) != (sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('33', plain, ($false),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
