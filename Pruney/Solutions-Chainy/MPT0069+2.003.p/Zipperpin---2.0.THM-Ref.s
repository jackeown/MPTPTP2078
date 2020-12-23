%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TTEZvpFFQJ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  58 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(t62_xboole_1,conjecture,(
    ! [A: $i] :
      ~ ( r2_xboole_0 @ A @ k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( r2_xboole_0 @ A @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t62_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf('2',plain,(
    r2_xboole_0 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('4',plain,(
    ~ ( r2_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','5'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('7',plain,(
    ! [X2: $i] :
      ~ ( r2_xboole_0 @ X2 @ X2 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('8',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TTEZvpFFQJ
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:18:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 7 iterations in 0.009s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.22/0.47  thf(t62_xboole_1, conjecture,
% 0.22/0.47    (![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t62_xboole_1])).
% 0.22/0.47  thf('0', plain, ((r2_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t61_xboole_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X3 : $i]: ((r2_xboole_0 @ k1_xboole_0 @ X3) | ((X3) = (k1_xboole_0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.22/0.47  thf('2', plain, ((r2_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(antisymmetry_r2_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ( r2_xboole_0 @ A @ B ) => ( ~( r2_xboole_0 @ B @ A ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (r2_xboole_0 @ X0 @ X1) | ~ (r2_xboole_0 @ X1 @ X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [antisymmetry_r2_xboole_0])).
% 0.22/0.47  thf('4', plain, (~ (r2_xboole_0 @ k1_xboole_0 @ sk_A)),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.47  thf('6', plain, ((r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '5'])).
% 0.22/0.47  thf(irreflexivity_r2_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.22/0.47  thf('7', plain, (![X2 : $i]: ~ (r2_xboole_0 @ X2 @ X2)),
% 0.22/0.47      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.22/0.47  thf('8', plain, ($false), inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
