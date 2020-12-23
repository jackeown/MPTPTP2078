%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W3egKzL43z

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 (  88 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ X3 ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t66_relat_1,axiom,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('4',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t66_relat_1])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('6',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('10',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W3egKzL43z
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 8 iterations in 0.009s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(t138_relat_1, conjecture,
% 0.20/0.46    (![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t138_relat_1])).
% 0.20/0.46  thf('0', plain, (((k8_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t117_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ (k8_relat_1 @ X2 @ X3) @ X3) | ~ (v1_relat_1 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.20/0.46  thf(t3_xboole_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.46          | ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(t66_relat_1, axiom, (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.46  thf('4', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t66_relat_1])).
% 0.20/0.46  thf(fc14_relat_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.46       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 0.20/0.46         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X1 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X1)) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc14_relat_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.46  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.46  thf('8', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i]: ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '8'])).
% 0.20/0.46  thf('10', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '9'])).
% 0.20/0.46  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
