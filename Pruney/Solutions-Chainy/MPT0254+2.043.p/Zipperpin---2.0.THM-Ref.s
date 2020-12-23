%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i242YQuNB4

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  154 ( 195 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['8'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r2_hidden @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['12','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i242YQuNB4
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:52:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 39 iterations in 0.019s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.47  thf('0', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.47  thf(t46_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.47  thf('2', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(t83_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X10 : $i, X12 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.47  thf(t49_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t15_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.47       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (((X5) = (k1_xboole_0)) | ((k2_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.47  thf(l24_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X21 : $i, X22 : $i]:
% 0.21/0.47         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, (~ (r2_hidden @ sk_A @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '11'])).
% 0.21/0.47  thf('13', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.47  thf(d1_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.47         (((X14) != (X13))
% 0.21/0.47          | (r2_hidden @ X14 @ X15)
% 0.21/0.47          | ((X15) != (k1_tarski @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.47  thf('15', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf('16', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '15'])).
% 0.21/0.47  thf('17', plain, ($false), inference('demod', [status(thm)], ['12', '16'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
