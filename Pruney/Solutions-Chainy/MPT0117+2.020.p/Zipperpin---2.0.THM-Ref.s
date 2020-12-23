%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xhzyCHdXxw

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  113 ( 165 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t97_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
        & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X4 @ X3 ) @ X5 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t97_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_B )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xhzyCHdXxw
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:46:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 16 iterations in 0.015s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t110_xboole_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.46       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.46          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.21/0.46  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t109_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.21/0.46  thf('3', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.21/0.46  thf('6', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf(t97_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 0.21/0.46         ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 0.21/0.46       ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         ((r1_tarski @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 0.21/0.46          | ~ (r1_tarski @ (k4_xboole_0 @ X4 @ X3) @ X5)
% 0.21/0.46          | ~ (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t97_xboole_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_B)
% 0.21/0.46          | (r1_tarski @ (k5_xboole_0 @ X0 @ sk_C) @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.46  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
