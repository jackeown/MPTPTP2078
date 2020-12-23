%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V2e7zdukNP

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:49 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   24 (  32 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  133 ( 205 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t97_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
        & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X7 ) @ X9 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t97_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_B )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V2e7zdukNP
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:40:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 76 iterations in 0.087s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(t110_xboole_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.39/0.58       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.58        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.39/0.58          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.39/0.58  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf(t36_xboole_1, axiom,
% 0.42/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.42/0.58  thf('2', plain,
% 0.42/0.58      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.42/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.42/0.58  thf(t1_xboole_1, axiom,
% 0.42/0.58    (![A:$i,B:$i,C:$i]:
% 0.42/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.42/0.58       ( r1_tarski @ A @ C ) ))).
% 0.42/0.58  thf('3', plain,
% 0.42/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.58         (~ (r1_tarski @ X2 @ X3)
% 0.42/0.58          | ~ (r1_tarski @ X3 @ X4)
% 0.42/0.58          | (r1_tarski @ X2 @ X4))),
% 0.42/0.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.42/0.58  thf('4', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.58         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.58  thf('5', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.42/0.58      inference('sup-', [status(thm)], ['1', '4'])).
% 0.42/0.58  thf('6', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('7', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.58         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.58  thf('8', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_B)),
% 0.42/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.58  thf(t97_xboole_1, axiom,
% 0.42/0.58    (![A:$i,B:$i,C:$i]:
% 0.42/0.58     ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 0.42/0.58         ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 0.42/0.58       ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ))).
% 0.42/0.58  thf('9', plain,
% 0.42/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.58         ((r1_tarski @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.42/0.58          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X7) @ X9)
% 0.42/0.58          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.42/0.58      inference('cnf', [status(esa)], [t97_xboole_1])).
% 0.42/0.58  thf('10', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_B)
% 0.42/0.58          | (r1_tarski @ (k5_xboole_0 @ X0 @ sk_C) @ sk_B))),
% 0.42/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.58  thf('11', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.42/0.58      inference('sup-', [status(thm)], ['5', '10'])).
% 0.42/0.58  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.42/0.58  
% 0.42/0.58  % SZS output end Refutation
% 0.42/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
