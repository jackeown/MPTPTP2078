%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BQTCgQUl92

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:55 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   30 (  43 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 229 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['2'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['2'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['2'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['9','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BQTCgQUl92
% 0.15/0.38  % Computer   : n002.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 11:40:22 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.47  % Solved by: fo/fo7.sh
% 0.24/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.47  % done 10 iterations in 0.010s
% 0.24/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.47  % SZS output start Refutation
% 0.24/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.47  thf(t49_zfmisc_1, conjecture,
% 0.24/0.47    (![A:$i,B:$i]:
% 0.24/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.24/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.47    (~( ![A:$i,B:$i]:
% 0.24/0.47        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.24/0.47    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.24/0.47  thf('0', plain,
% 0.24/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(t15_xboole_1, axiom,
% 0.24/0.47    (![A:$i,B:$i]:
% 0.24/0.47     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.24/0.47       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.47  thf('1', plain,
% 0.24/0.47      (![X0 : $i, X1 : $i]:
% 0.24/0.47         (((X0) = (k1_xboole_0)) | ((k2_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.24/0.47      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.24/0.47  thf('2', plain,
% 0.24/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.24/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.47  thf('3', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.24/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.24/0.47  thf(l33_zfmisc_1, axiom,
% 0.24/0.47    (![A:$i,B:$i]:
% 0.24/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.24/0.47       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.24/0.47  thf('4', plain,
% 0.24/0.47      (![X3 : $i, X4 : $i]:
% 0.24/0.47         (~ (r2_hidden @ X3 @ X4)
% 0.24/0.47          | ((k4_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_tarski @ X3)))),
% 0.24/0.47      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.24/0.47  thf('5', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_A))
% 0.24/0.47          | ~ (r2_hidden @ sk_A @ X0))),
% 0.24/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.47  thf(t4_boole, axiom,
% 0.24/0.47    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.47  thf('6', plain,
% 0.24/0.47      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.24/0.47      inference('cnf', [status(esa)], [t4_boole])).
% 0.24/0.47  thf('7', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.24/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.24/0.47  thf('8', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.24/0.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.24/0.47  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.24/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.24/0.47  thf('10', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.24/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.24/0.47  thf(l35_zfmisc_1, axiom,
% 0.24/0.47    (![A:$i,B:$i]:
% 0.24/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.47       ( r2_hidden @ A @ B ) ))).
% 0.24/0.47  thf('11', plain,
% 0.24/0.47      (![X6 : $i, X7 : $i]:
% 0.24/0.47         ((r2_hidden @ X6 @ X7)
% 0.24/0.47          | ((k4_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0)))),
% 0.24/0.47      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.24/0.47  thf('12', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.24/0.47          | (r2_hidden @ sk_A @ X0))),
% 0.24/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.47  thf('13', plain,
% 0.24/0.47      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.24/0.47      inference('cnf', [status(esa)], [t4_boole])).
% 0.24/0.47  thf('14', plain,
% 0.24/0.47      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A @ X0))),
% 0.24/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.24/0.47  thf('15', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.24/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.24/0.47  thf('16', plain, ($false), inference('demod', [status(thm)], ['9', '15'])).
% 0.24/0.47  
% 0.24/0.47  % SZS output end Refutation
% 0.24/0.47  
% 0.24/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
