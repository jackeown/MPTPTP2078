%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gRxEV4iU5d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:53 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   91 (  91 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t138_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k8_relat_1 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k8_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t138_relat_1])).

thf('0',plain,(
    ( k8_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X5 @ X6 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gRxEV4iU5d
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:43:44 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 10 iterations in 0.008s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.18/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.45  thf(t138_relat_1, conjecture,
% 0.18/0.45    (![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t138_relat_1])).
% 0.18/0.45  thf('0', plain, (((k8_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t117_relat_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.18/0.45  thf('1', plain,
% 0.18/0.45      (![X5 : $i, X6 : $i]:
% 0.18/0.45         ((r1_tarski @ (k8_relat_1 @ X5 @ X6) @ X6) | ~ (v1_relat_1 @ X6))),
% 0.18/0.45      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.18/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.45  thf('2', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.18/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.45  thf(d10_xboole_0, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.45  thf('3', plain,
% 0.18/0.45      (![X0 : $i, X2 : $i]:
% 0.18/0.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.45  thf('4', plain,
% 0.18/0.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.18/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.45  thf('5', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ k1_xboole_0)
% 0.18/0.45          | ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.18/0.45      inference('sup-', [status(thm)], ['1', '4'])).
% 0.18/0.45  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.18/0.45  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.18/0.45  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.18/0.45  thf('7', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.18/0.45      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.18/0.45  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.18/0.45      inference('sup+', [status(thm)], ['6', '7'])).
% 0.18/0.45  thf('9', plain,
% 0.18/0.45      (![X0 : $i]: ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.45      inference('demod', [status(thm)], ['5', '8'])).
% 0.18/0.45  thf('10', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.18/0.45      inference('demod', [status(thm)], ['0', '9'])).
% 0.18/0.45  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
