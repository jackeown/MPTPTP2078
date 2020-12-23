%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QZRJA3IkdD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 (  76 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_xboole_0 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('6',plain,(
    ~ ( r2_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r2_xboole_0 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['0','7'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('9',plain,(
    ! [X5: $i] :
      ~ ( r2_xboole_0 @ X5 @ X5 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('10',plain,(
    $false ),
    inference('sup-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QZRJA3IkdD
% 0.12/0.36  % Computer   : n009.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 18:30:11 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 14 iterations in 0.007s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(t62_xboole_1, conjecture,
% 0.21/0.47    (![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t62_xboole_1])).
% 0.21/0.47  thf('0', plain, ((r2_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('1', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf(d8_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.47       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X2 : $i, X4 : $i]:
% 0.21/0.47         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((r2_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(antisymmetry_r2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( r2_xboole_0 @ A @ B ) => ( ~( r2_xboole_0 @ B @ A ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_xboole_0 @ X0 @ X1) | ~ (r2_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [antisymmetry_r2_xboole_0])).
% 0.21/0.47  thf('6', plain, (~ (r2_xboole_0 @ k1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf('8', plain, ((r2_xboole_0 @ sk_A @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.47  thf(irreflexivity_r2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.21/0.47  thf('9', plain, (![X5 : $i]: ~ (r2_xboole_0 @ X5 @ X5)),
% 0.21/0.47      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.21/0.47  thf('10', plain, ($false), inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
