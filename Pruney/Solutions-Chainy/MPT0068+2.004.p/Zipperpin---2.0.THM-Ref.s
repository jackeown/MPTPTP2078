%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nU33c0h4hD

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 110 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t61_xboole_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t61_xboole_1])).

thf('8',plain,(
    ~ ( r2_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nU33c0h4hD
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:40 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.42  % Solved by: fo/fo7.sh
% 0.20/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.42  % done 13 iterations in 0.006s
% 0.20/0.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.42  % SZS output start Refutation
% 0.20/0.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.42  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.42  thf(t36_xboole_1, axiom,
% 0.20/0.42    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.42  thf('0', plain,
% 0.20/0.42      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.42  thf(t3_xboole_1, axiom,
% 0.20/0.42    (![A:$i]:
% 0.20/0.42     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.42  thf('1', plain,
% 0.20/0.42      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.20/0.42      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.42  thf('2', plain,
% 0.20/0.42      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.42      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.42  thf(l32_xboole_1, axiom,
% 0.20/0.42    (![A:$i,B:$i]:
% 0.20/0.42     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.42  thf('3', plain,
% 0.20/0.42      (![X3 : $i, X4 : $i]:
% 0.20/0.42         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.20/0.42      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.42  thf('4', plain,
% 0.20/0.42      (![X0 : $i]:
% 0.20/0.42         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.42      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.42  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.42      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.42  thf(d8_xboole_0, axiom,
% 0.20/0.42    (![A:$i,B:$i]:
% 0.20/0.42     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.42       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.42  thf('6', plain,
% 0.20/0.42      (![X0 : $i, X2 : $i]:
% 0.20/0.42         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.42      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.42  thf('7', plain,
% 0.20/0.42      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.42      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.42  thf(t61_xboole_1, conjecture,
% 0.20/0.42    (![A:$i]:
% 0.20/0.42     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.20/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.42    (~( ![A:$i]:
% 0.20/0.42        ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )),
% 0.20/0.42    inference('cnf.neg', [status(esa)], [t61_xboole_1])).
% 0.20/0.42  thf('8', plain, (~ (r2_xboole_0 @ k1_xboole_0 @ sk_A)),
% 0.20/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.42  thf('9', plain, (((k1_xboole_0) = (sk_A))),
% 0.20/0.42      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.42  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.42  thf('11', plain, ($false),
% 0.20/0.42      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.42  
% 0.20/0.42  % SZS output end Refutation
% 0.20/0.42  
% 0.20/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
