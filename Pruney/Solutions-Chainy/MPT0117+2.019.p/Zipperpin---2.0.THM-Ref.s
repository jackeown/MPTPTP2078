%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J41sHgkost

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:49 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  119 ( 163 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t101_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J41sHgkost
% 0.14/0.38  % Computer   : n022.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 10:41:56 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.39  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 39 iterations in 0.032s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(t110_xboole_1, conjecture,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.24/0.53       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.53        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.24/0.53          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.24/0.53  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t101_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( k5_xboole_0 @ A @ B ) =
% 0.24/0.53       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.24/0.53  thf('1', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         ((k5_xboole_0 @ X0 @ X1)
% 0.24/0.53           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.24/0.53      inference('cnf', [status(esa)], [t101_xboole_1])).
% 0.24/0.53  thf('2', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t8_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.24/0.53       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.24/0.53  thf('4', plain,
% 0.24/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.53         (~ (r1_tarski @ X5 @ X6)
% 0.24/0.53          | ~ (r1_tarski @ X7 @ X6)
% 0.24/0.53          | (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.24/0.53      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.24/0.53          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.53  thf('6', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.24/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.24/0.53  thf(t109_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.53         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 0.24/0.53      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ X0) @ sk_B)),
% 0.24/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.53  thf('9', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.24/0.53      inference('sup+', [status(thm)], ['1', '8'])).
% 0.24/0.53  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
