%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rfPvN9p6Bz

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  150 ( 195 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('3',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rfPvN9p6Bz
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 23 iterations in 0.015s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(t77_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X12 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.20/0.48  thf(t50_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t15_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((X2) = (k1_xboole_0)) | ((k2_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.48  thf(l53_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.48       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.48           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ (k2_tarski @ X9 @ X10)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X1 @ X0 @ sk_A @ sk_B)
% 0.20/0.48           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((k2_tarski @ sk_A @ sk_B)
% 0.20/0.48         = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['0', '6'])).
% 0.20/0.48  thf('8', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('9', plain, (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((k1_xboole_0) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf(t49_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ (k1_tarski @ X16) @ X17) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.48  thf('12', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
